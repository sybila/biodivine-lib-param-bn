use biodivine_lib_param_bn::biodivine_std::traits::Set;
use biodivine_lib_param_bn::decomposition::Counter;
use biodivine_lib_param_bn::symbolic_async_graph::{GraphColoredVertices, SymbolicAsyncGraph};
use biodivine_lib_param_bn::BooleanNetwork;
use std::cmp::min;
use std::convert::TryFrom;
use std::io::Read;
use std::sync::Mutex;
use std::time::Duration;

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
    let remaining = Mutex::new(graph.unit_colored_vertices().approx_cardinality());
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
                        println!("Remaining: {} (Removed {})", lock_remaining, removed);
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
    let universe = if should_trim {
        trim(graph, whole_universe.clone())
    } else {
        whole_universe.clone()
    };
    if universe.is_empty() {
        //println!("NO SCC");
        return whole_universe.approx_cardinality();
    }

    let too_small = (1 << (graph.as_network().num_vars() / 2)) as f64;
    if universe.vertices().approx_cardinality() < too_small {
        // All components are too small.
        return whole_universe.approx_cardinality();
    }

    let pivot = &universe.pick_vertex();

    let mut fwd = pivot.clone();
    let mut bwd = pivot.clone();
    let mut done_fwd = graph.mk_empty_colors();

    // Compute fwd/bwd in lockstep
    {
        let mut remaining = universe.colors();
        while !remaining.is_empty() {
            let mut fwd_to_step = remaining.clone();
            for var in graph.as_network().variables().rev() {
                let step = graph
                    .var_post(var, &fwd.intersect_colors(&fwd_to_step))
                    .intersect(&universe)
                    .minus(&fwd);

                if !step.is_empty() {
                    fwd_to_step = fwd_to_step.minus(&step.colors());
                    fwd = fwd.union(&step);
                }
                if fwd_to_step.is_empty() {
                    break;
                }
            }
            // Colors in fwd_to_step had no successors
            done_fwd = done_fwd.union(&fwd_to_step);
            remaining = remaining.minus(&fwd_to_step);

            let mut bwd_to_step = remaining.clone();
            for var in graph.as_network().variables().rev() {
                let step = graph
                    .var_pre(var, &bwd.intersect_colors(&bwd_to_step))
                    .intersect(&universe)
                    .minus(&bwd);

                if !step.is_empty() {
                    bwd_to_step = bwd_to_step.minus(&step.colors());
                    bwd = bwd.union(&step);
                }
                if bwd_to_step.is_empty() {
                    break;
                }
            }
            remaining = remaining.minus(&bwd_to_step);

            if fwd.as_bdd().size() > 100_000 || bwd.as_bdd().size() > 100_000 {
                println!("Remaining: {}", remaining.approx_cardinality());
                println!(
                    "FWD: {} ({}); BWD {} ({})",
                    fwd.approx_cardinality(),
                    fwd.as_bdd().size(),
                    bwd.approx_cardinality(),
                    bwd.as_bdd().size()
                );
            }
        }
    }

    // Bwd is everything that isn't fwd.
    let done_bwd = universe.colors().minus(&done_fwd);

    // Finish fwd/bwd sets *after* lockstep.
    {
        let mut bwd_continue = bwd.intersect_colors(&done_fwd);
        'bwd: loop {
            for var in graph.as_network().variables().rev() {
                let step = graph
                    .var_pre(var, &bwd_continue)
                    .intersect(&fwd)
                    .minus(&bwd_continue);

                if bwd_continue.as_bdd().size() > 100_000 {
                    println!(
                        "BWD {} ({})",
                        bwd_continue.approx_cardinality(),
                        bwd_continue.as_bdd().size()
                    );
                }

                if !step.is_empty() {
                    bwd_continue = bwd_continue.union(&step);
                    continue 'bwd;
                }
            }
            break 'bwd;
        }
        bwd = bwd.union(&bwd_continue);

        let mut fwd_continue = fwd.intersect_colors(&done_bwd);
        'fwd: loop {
            for var in graph.as_network().variables().rev() {
                let step = graph
                    .var_post(var, &fwd_continue)
                    .intersect(&bwd)
                    .minus(&fwd_continue);

                if fwd_continue.as_bdd().size() > 100_000 {
                    println!(
                        "FWD: {} ({})",
                        fwd_continue.approx_cardinality(),
                        fwd_continue.as_bdd().size()
                    );
                }

                if !step.is_empty() {
                    fwd_continue = fwd_continue.union(&step);
                    continue 'fwd;
                }
            }
            break 'fwd;
        }
        fwd = fwd.union(&fwd_continue);
    }

    let scc = &fwd.intersect(&bwd);
    if scc.vertices().approx_cardinality() >= too_small {
        let non_pivot_states = &scc.minus(&pivot);
        let non_trivial_colors = non_pivot_states.colors();
        if !non_trivial_colors.is_empty() {
            counter.push(&non_trivial_colors);
        } else {
            //println!("TRIVIAL.");
        }
    }
    /*println!(
        "SCC: {} ({} vertices)",
        scc.approx_cardinality(),
        scc.vertices().approx_cardinality()
    );*/

    let fwd_converged = fwd.intersect_colors(&done_fwd);
    let bwd_converged = bwd.intersect_colors(&done_bwd);
    let converged = fwd_converged.union(&bwd_converged).minus(&scc);
    let rest = universe.minus(&converged).minus(&scc);

    /*println!(
        "SPLIT: {} - {}",
        rest.approx_cardinality(),
        converged.approx_cardinality()
    );*/

    let eliminated = whole_universe.approx_cardinality()
        - (rest.approx_cardinality() + converged.approx_cardinality());

    if !rest.is_empty() {
        queue.push(rest);
    }

    if !converged.is_empty() {
        queue.push(converged);
    }

    return eliminated;
}

fn trim(graph: &SymbolicAsyncGraph, mut set: GraphColoredVertices) -> GraphColoredVertices {
    //let initial = set.as_bdd().size();
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
        //if set.as_bdd().size() > 2 * initial {
        //    return set;
        //}
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
        //if set.as_bdd().size() > 2 * initial {
        //    return set;
        //}
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
