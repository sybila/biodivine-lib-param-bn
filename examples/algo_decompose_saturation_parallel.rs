use biodivine_lib_param_bn::symbolic_async_graph::{SymbolicAsyncGraph, GraphColoredVertices};
use biodivine_lib_param_bn::biodivine_std::traits::Set;
use rayon::prelude::*;
use std::sync::Mutex;
use std::time::{SystemTime, Duration};
use biodivine_lib_param_bn::decomposition::Counter;
use std::cmp::min;
use std::io::Read;
use biodivine_lib_param_bn::BooleanNetwork;
use std::convert::TryFrom;
use std::sync::atomic::{AtomicU64, Ordering};
use rand::prelude::SliceRandom;

fn main() {
    let mut args = std::env::args();
    args.next();
    let threads = args.next().unwrap().parse::<u32>().unwrap();
    let mut buffer = String::new();
    std::io::stdin().read_to_string(&mut buffer).unwrap();


    let model = BooleanNetwork::try_from(buffer.as_str()).unwrap();
    let model = shuffle(model);
    println!("Model vars: {}", model.as_graph().num_vars());
    for var in model.variables() {
        println!("{:?}: {}", var, model.get_variable_name(var));
    }


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
    let mut universes = _decompose_by_values(&graph, vec![graph.mk_unit_colored_vertices()], threads);
    // Usually, the biggest universe ends up first, so move it to be popped first.
    universes.reverse();
    let count = sccs(&graph, universes, threads);
    println!("Counted: {}", count);
}


fn shuffle(mut network: BooleanNetwork) -> BooleanNetwork {
    let mut new_index = (0..network.num_vars()).collect::<Vec<_>>();
    new_index.shuffle(&mut rand::thread_rng());

    for var in network.variables() {
        let new_name = format!("{}_{}", new_index[var.as_index()], network.get_variable_name(var));
        network.as_graph_mut().rename(var, new_name);
    }

    BooleanNetwork::try_from(network.to_string().as_str()).unwrap()
}

fn sccs(graph: &SymbolicAsyncGraph, universes: Vec<GraphColoredVertices>, threads: u32) -> usize {
    let aggregated = Mutex::new(Counter::new(graph));
    let queue = ParQueue::new(threads, universes);
    let total_size = graph.unit_colored_vertices().approx_cardinality();
    let remaining = Mutex::new(graph.unit_colored_vertices().approx_cardinality());
    let start = SystemTime::now();
    let last_print = AtomicU64::new(0);
    rayon::scope(|s| {
        for _ in 0..threads {
            s.spawn(|_| {
                let mut counter = Counter::new(graph);
                while let Some((universe, should_trim)) = queue.pop() {
                    let removed =
                        one_scc(graph, &queue, &mut counter, universe, should_trim);
                    {
                        let mut lock_remaining = remaining.lock().unwrap();
                        *lock_remaining = *lock_remaining - removed;
                        let now = SystemTime::now()
                            .duration_since(start)
                            .unwrap()
                            .as_secs();
                        if now > last_print.load(Ordering::Relaxed) {
                            last_print.store(now, Ordering::Relaxed);
                            let elapsed = start.elapsed().unwrap();
                            let unit_per_second = (total_size - *lock_remaining) / (elapsed.as_secs() as f64);
                            let remaining_seconds = *lock_remaining / unit_per_second;
                            println!(
                                "Remaining: {}; Expected: {}s; Throughput: {}/s; Removed {}; Found: {}",
                                lock_remaining,
                                remaining_seconds.round(),
                                unit_per_second.round(),
                                removed,
                                counter.len(),
                            );
                        }
                    }
                }
                aggregated.lock().unwrap().merge(&counter);
            });
        }
    });

    let aggregated = aggregated.into_inner().unwrap();
    aggregated.print();
    aggregated.len()
}

fn one_scc(
    graph: &SymbolicAsyncGraph,
    queue: &ParQueue,
    counter: &mut Counter,
    universe: GraphColoredVertices,
    should_trim: bool,
) -> f64 {
    let mut removed = universe.approx_cardinality();
    let trimmed = if should_trim {
        trim(graph, universe)
    } else {
        universe
    };

    if trimmed.is_empty() {
        return removed;
    }

    let pivot = trimmed.pick_vertex();
    let fwd = fwd_saturation(graph, &trimmed, pivot.clone());
    let bwd = bwd_saturation(graph, &trimmed, pivot.clone());

    let scc = fwd.intersect(&bwd);
    let non_trivial_scc = scc.minus(&pivot).colors();
    if !non_trivial_scc.is_empty() {
        counter.push(&non_trivial_scc);
    }

    let fwd_only = fwd.minus(&bwd);
    if !fwd_only.is_empty() {
        removed -= fwd_only.approx_cardinality();
        queue.push(fwd_only);
    }

    let bwd_only = bwd.minus(&fwd);
    if !bwd_only.is_empty() {
        removed -= bwd_only.approx_cardinality();
        queue.push(bwd_only);
    }

    let rest = trimmed.minus(&fwd).minus(&bwd);
    if !rest.is_empty() {
        removed -= rest.approx_cardinality();
        queue.push(rest);
    }

    removed
}

fn _decompose_by_values(
    graph: &SymbolicAsyncGraph,
    mut universes: Vec<GraphColoredVertices>,
    threads: u32,
) -> Vec<GraphColoredVertices> {
    let cut_off = (1 << 15) as f64;
    let mut result = Vec::new();
    for var in graph.as_network().variables().rev() {
        println!("Splitting by var {:?}", var);
        universes = universes
            .par_iter()
            .flat_map(|universe| {
                let mut result = Vec::new();
                let pivots = graph.fix_network_variable(var, true).intersect(&universe);
                split_by(graph, &mut result, universe, &pivots);
                result
            })
            .collect();
        universes = universes
            .par_iter()
            .flat_map(|universe| {
                let mut result = Vec::new();
                let pivots = graph.fix_network_variable(var, false).intersect(&universe);
                split_by(graph, &mut result, universe, &pivots);
                result
            })
            .collect();
        if (threads as usize) < universes.len() {
            println!("Split into {}. Trim.", universes.len());
            universes = universes
                .into_par_iter()
                .map(|universe| {
                    if universe.vertices().approx_cardinality() < cut_off {
                        trim(graph, universe)
                    } else {
                        universe
                    }
                })
                .filter(|it| !it.is_empty())
                .collect();
        }

        let (mut move_result, keep) = universes.into_iter().partition(|it| it.vertices().approx_cardinality() < cut_off);
        result.append(&mut move_result);
        universes = keep;

        let size: f64 = universes
            .iter()
            .map(|it| it.approx_cardinality())
            .sum();
        println!("Size after trimming: {}/{}", size, graph.unit_colored_vertices().approx_cardinality());
    }
    universes.append(&mut result);
    universes
}

fn _decompose_by_transitions(
    graph: &SymbolicAsyncGraph,
    mut universes: Vec<GraphColoredVertices>,
    threads: u32,
) -> Vec<GraphColoredVertices> {
    for var in graph.as_network().variables().rev() {
        println!("Splitting by var {:?}", var);
        universes = universes
            .par_iter()
            .flat_map(|universe| {
                let mut result = Vec::new();
                let pivots = graph.var_can_post(var, universe);
                split_by(graph, &mut result, universe, &pivots);
                result
            })
            .collect();
        if (threads as usize) < universes.len() {
            println!("Split into {}. Trim.", universes.len());
            universes = universes
                .par_iter()
                .map(|universe| {
                    trim(graph, universe.clone())
                })
                .filter(|it| !it.is_empty())
                .collect();
        }
        let size: f64 = universes
            .iter()
            .map(|it| it.approx_cardinality())
            .sum();
        println!("Size after trimming: {}/{}", size, graph.unit_colored_vertices().approx_cardinality());
    }
    universes
}

fn split_by(
    graph: &SymbolicAsyncGraph,
    results: &mut Vec<GraphColoredVertices>,
    universe: &GraphColoredVertices,
    pivots: &GraphColoredVertices
) {
    let fwd = fwd_saturation(graph, universe, pivots.clone());
    let bwd = bwd_saturation(graph, universe, pivots.clone());

    let both = fwd.intersect(&bwd);
    if !both.is_empty() { results.push(both); }
    let rest = universe.minus(&fwd).minus(&bwd);
    if !rest.is_empty() { results.push(rest); }
    let fwd_only = fwd.minus(&bwd);
    if !fwd_only.is_empty() { results.push(fwd_only); }
    let bwd_only = bwd.minus(&fwd);
    if !bwd_only.is_empty() { results.push(bwd_only); }
}

/// Normal saturated forward reachability inside the given `universe`.
fn fwd_saturation(
    graph: &SymbolicAsyncGraph,
    universe: &GraphColoredVertices,
    mut fwd: GraphColoredVertices,
) -> GraphColoredVertices {
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
            let successors = graph.var_post(var, &fwd).intersect(universe);

            if !successors.is_subset(&fwd) {
                fwd = fwd.union(&successors);
                continue 'fwd;
            }
        }
        return fwd;
    }
}

// Normal saturated backwards reachability inside given `universe`.
fn bwd_saturation(
    graph: &SymbolicAsyncGraph,
    universe: &GraphColoredVertices,
    mut bwd: GraphColoredVertices,
) -> GraphColoredVertices {
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
            let predecessors = graph.var_pre(var, &bwd).intersect(universe);

            if !predecessors.is_subset(&bwd) {
                bwd = bwd.union(&predecessors);
                continue 'bwd;
            }
        }
        return bwd;
    }
}

/// Iteratively remove vertices with no outgoing/incoming edges.
/// It is only allowed when the symbolic size of the set is less than 10k nodes.
fn trim(graph: &SymbolicAsyncGraph, mut set: GraphColoredVertices) -> GraphColoredVertices {
    if set.as_bdd().size() > 10_000 {
        //return set;
    }
    loop {
        let pre = graph.pre(&set).intersect(&set);
        let post = graph.post(&pre).intersect(&set);
        if set.is_subset(&post) {
            // set == post
            break;
        }
        if set.as_bdd().size() > 10_000 {
            println!(
                "TRIM: {}; {}",
                set.as_bdd().size(),
                set.approx_cardinality()
            );
            //return set;
        }
        set = post;
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
        if set.as_bdd().size() > 10_000 {
            println!(
                "TRIM: {}; {}",
                set.as_bdd().size(),
                set.approx_cardinality()
            );
            //return set;
        }
        set = pre;
    }

    set
}


struct ParQueue {
    threads: u32,
    data: Mutex<(Vec<GraphColoredVertices>, u32)>,
}

impl ParQueue {
    fn new(threads: u32, universes: Vec<GraphColoredVertices>) -> ParQueue {
        ParQueue {
            threads,
            data: Mutex::new((universes, 0)),
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
