use biodivine_lib_param_bn::biodivine_std::traits::Set;
use biodivine_lib_param_bn::decomposition::Counter;
use biodivine_lib_param_bn::symbolic_async_graph::{GraphColoredVertices, SymbolicAsyncGraph};
use biodivine_lib_param_bn::BooleanNetwork;
use std::cmp::min;
use std::convert::TryFrom;
use std::io::Read;
use std::sync::Mutex;
use std::time::{Duration, SystemTime};

fn main() {
    let mut args = std::env::args();
    args.next();
    let threads = args.next().unwrap().parse::<u32>().unwrap();
    let mut buffer = String::new();
    std::io::stdin().read_to_string(&mut buffer).unwrap();

    let model = BooleanNetwork::try_from(buffer.as_str()).unwrap();
    println!("Model vars: {}", model.as_graph().num_vars());

    let graph = SymbolicAsyncGraph::new(model).unwrap();
    println!(
        "Model params: {}",
        (graph.symbolic_context().bdd_variable_set().num_vars() as usize)
            - graph.as_network().num_vars()
    );
    println!(
        "Graph size: {} (Colors {})",
        graph.unit_colored_vertices().approx_cardinality(),
        graph.unit_colors().approx_cardinality()
    );
    let count = par_decomposition(&graph, threads);
    println!("Counted: {}", count);
}

fn par_decomposition(graph: &SymbolicAsyncGraph, threads: u32) -> usize {
    let counters = Mutex::new(Vec::new());
    let queue = ParQueue::new(threads);
    let full = graph.unit_colored_vertices().approx_cardinality();
    let remaining = Mutex::new(graph.unit_colored_vertices().approx_cardinality());
    let start = SystemTime::now();
    rayon::scope(|s| {
        queue.push(graph.mk_unit_colored_vertices());
        for _ in 0..threads {
            s.spawn(|_| {
                let mut counter = Counter::new(graph);
                while let Some((universe, should_trim)) = queue.pop() {
                    let removed =
                        one_decomposition(graph, &queue, &mut counter, universe, should_trim);
                    {
                        let mut lock_remaining = remaining.lock().unwrap();
                        *lock_remaining = *lock_remaining - removed;
                        let elapsed = start.elapsed().unwrap();
                        let unit_per_second = (full - *lock_remaining) / (elapsed.as_secs() as f64);
                        let remaining_seconds = *lock_remaining / unit_per_second;
                        println!(
                            "Remaining: {}; Expected: {}s; Throughput: {}/s; Removed {};",
                            lock_remaining,
                            remaining_seconds.round(),
                            unit_per_second.round(),
                            removed
                        );
                    }
                }
                counters.lock().unwrap().push(counter);
            });
        }
    });

    let mut result = Counter::new(graph);
    let locked_counters = counters.lock().unwrap();
    for counter in locked_counters.iter() {
        println!("Counter: {}; {}", counter.len(), result.len());
        result.merge(counter);
        //result.print();
    }

    result.print();
    result.len()
}

fn one_decomposition(
    graph: &SymbolicAsyncGraph,
    queue: &ParQueue,
    counter: &mut Counter,
    whole_universe: GraphColoredVertices,
    should_trim: bool,
) -> f64 {
    let too_small = graph
        .unit_colored_vertices()
        .vertices()
        .approx_cardinality()
        / 100.0; //(1 << (graph.as_network().num_vars() / 2)) as f64;
    if whole_universe.vertices().approx_cardinality() < too_small {
        // All components are too small.
        return whole_universe.approx_cardinality();
    }

    let universe = if should_trim {
        trim(graph, whole_universe.clone())
    } else {
        whole_universe.clone()
    };
    if universe.is_empty() {
        //println!("NO SCC");
        return whole_universe.approx_cardinality();
    }

    if universe.vertices().approx_cardinality() < too_small {
        // All components are too small.
        return whole_universe.approx_cardinality();
    }

    let pivot = universe.pick_vertex();

    let mut fwd = pivot.clone();
    let mut bwd = pivot.clone();
    let bwd_converged;

    // First, lockstep reachability with saturation
    'lockstep: loop {
        if fwd.as_bdd().size() < bwd.as_bdd().size() {
            // Advance FWD
            if fwd.as_bdd().size() > 100_000 {
                println!(
                    "FWD: {}; {}/{}",
                    fwd.as_bdd().size(),
                    fwd.approx_cardinality(),
                    universe.approx_cardinality()
                );
            }
            for var in graph.as_network().variables().rev() {
                let next_fwd = graph.var_post(var, &fwd).intersect(&universe).minus(&fwd);
                if !next_fwd.is_empty() {
                    fwd = fwd.union(&next_fwd);
                    continue 'lockstep;
                }
            }
            bwd_converged = false;
            break 'lockstep;
        } else {
            // Advance BWD
            if bwd.as_bdd().size() > 100_000 {
                println!(
                    "BWD: {}; {}/{}",
                    bwd.as_bdd().size(),
                    bwd.approx_cardinality(),
                    universe.approx_cardinality()
                );
            }
            for var in graph.as_network().variables().rev() {
                let next_bwd = graph.var_pre(var, &bwd).intersect(&universe).minus(&bwd);
                if !next_bwd.is_empty() {
                    bwd = bwd.union(&next_bwd);
                    continue 'lockstep;
                }
            }
            bwd_converged = true;
            break 'lockstep;
        }
    }

    // Then finish the set that is not done:
    if bwd_converged {
        'fwd: loop {
            if fwd.as_bdd().size() > 100_000 {
                println!(
                    "FWD: {}; {}/{}",
                    fwd.as_bdd().size(),
                    fwd.approx_cardinality(),
                    universe.approx_cardinality()
                );
            }
            for var in graph.as_network().variables().rev() {
                let next_fwd = graph.var_post(var, &fwd).intersect(&bwd).minus(&fwd);
                if !next_fwd.is_empty() {
                    fwd = fwd.union(&next_fwd);
                    continue 'fwd;
                }
            }
            break 'fwd;
        }
    } else {
        'bwd: loop {
            if bwd.as_bdd().size() > 100_000 {
                println!(
                    "BWD: {}; {}/{}",
                    bwd.as_bdd().size(),
                    bwd.approx_cardinality(),
                    universe.approx_cardinality()
                );
            }
            for var in graph.as_network().variables().rev() {
                let next_bwd = graph.var_pre(var, &bwd).intersect(&fwd).minus(&bwd);
                if !next_bwd.is_empty() {
                    bwd = bwd.union(&next_bwd);
                    continue 'bwd;
                }
            }
            break 'bwd;
        }
    }

    let scc = &fwd.intersect(&bwd);
    let non_pivot_states = &scc.minus(&pivot);
    /*println!(
        "SCC: {} ({} vertices)",
        scc.approx_cardinality(),
        scc.vertices().approx_cardinality()
    );*/
    if non_pivot_states.vertices().approx_cardinality() > too_small {
        counter.push(&non_pivot_states.colors());
    } else {
        //println!("TRIVIAL.");
    }

    let eliminated: f64;

    if bwd_converged {
        let above = bwd.minus(&scc);
        let rest = universe.minus(&bwd);

        eliminated = whole_universe.approx_cardinality()
            - (rest.approx_cardinality() + above.approx_cardinality());
        if !above.is_empty() {
            queue.push(above);
        }
        if !rest.is_empty() {
            queue.push(rest);
        }
    } else {
        let below = fwd.minus(&scc);
        let rest = universe.minus(&fwd);

        eliminated = whole_universe.approx_cardinality()
            - (rest.approx_cardinality() + below.approx_cardinality());
        if !below.is_empty() {
            queue.push(below);
        }
        if !rest.is_empty() {
            queue.push(rest);
        }
    }

    return eliminated;
}

fn _random_pivot(graph: &SymbolicAsyncGraph, set: &GraphColoredVertices) -> GraphColoredVertices {
    let mut pivot = set.clone();
    for var in graph.as_network().variables() {
        let fixed = graph.fix_network_variable(var, rand::random::<bool>());
        let and_fixed = pivot.intersect(&fixed);
        if !and_fixed.is_empty() {
            pivot = and_fixed;
        }
        // If and_fixed is empty, it means all vertices in pivot have a specific (different) value.
    }
    pivot
}

fn trim(graph: &SymbolicAsyncGraph, mut set: GraphColoredVertices) -> GraphColoredVertices {
    let initial = set.as_bdd().size();
    loop {
        // Predecessors of set inside set
        let pre = graph.pre(&set).intersect(&set);
        // Successors of these predecessors inside set.
        let post = graph.post(&pre).intersect(&set);
        // Everything in set \ post has no predecessor in this set.
        if set.is_subset(&post) {
            // set == post
            break;
        }
        if set.as_bdd().size() > 100_000 {
            println!(
                "TRIM: {}; {}",
                set.as_bdd().size(),
                set.approx_cardinality()
            );
            return set;
        }
        set = post;
        if set.as_bdd().size() > 2 * initial {
            //return set;
        }
    }
    loop {
        // Successors of set inside set
        let post = graph.post(&set).intersect(&set);
        // Predecessors of these successors inside set.
        let pre = graph.pre(&post).intersect(&set);
        // Everything in set \ pre has no successor in set.
        if set.is_subset(&pre) {
            // set == pre
            break;
        }
        if set.as_bdd().size() > 100_000 {
            println!(
                "TRIM: {}; {}",
                set.as_bdd().size(),
                set.approx_cardinality()
            );
            return set;
        }
        set = pre;
        if set.as_bdd().size() > 2 * initial {
            //return set;
        }
    }

    set
}

struct ParQueue {
    threads: u32,
    data: Mutex<(Vec<GraphColoredVertices>, u32)>,
}

impl ParQueue {
    fn new(threads: u32) -> ParQueue {
        ParQueue {
            threads,
            data: Mutex::new((Vec::new(), 0)),
        }
    }

    fn push(&self, data: GraphColoredVertices) {
        let vector = &mut self.data.lock().unwrap().0;
        vector.push(data);
    }

    fn pop(&self) -> Option<(GraphColoredVertices, bool)> {
        loop {
            {
                let top = {
                    let mut locked = self.data.lock().unwrap();
                    if locked.0.is_empty() {
                        locked.1 += 1;
                        None
                    } else {
                        locked.0.pop().map(|x| (x, locked.1 == 0))
                    }
                };

                if top.is_some() {
                    return top;
                }

                let mut sleep_for = 32;
                'wait: loop {
                    std::thread::sleep(Duration::from_millis(sleep_for));
                    let is_empty = {
                        let mut locked = self.data.lock().unwrap();
                        if locked.0.is_empty() && locked.1 == self.threads {
                            // Everybody is waiting - just return empty.
                            return None;
                        } else if locked.0.is_empty() {
                            // Sleep time can increase up to 2 seconds.
                            sleep_for = min(sleep_for * 2, 2048);
                            true
                        } else {
                            // The vector is not empty - lets try to get the value:
                            locked.1 -= 1;
                            false
                        }
                    };
                    // Check loop will repeat and try to get the value if someone else hasn't
                    // taken it away already.
                    if !is_empty {
                        break 'wait;
                    }
                }
            }
        }
    }
}
