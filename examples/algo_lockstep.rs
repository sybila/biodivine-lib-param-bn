use std::io::Read;
use biodivine_lib_param_bn::symbolic_async_graph::{SymbolicAsyncGraph, GraphColoredVertices};
use biodivine_lib_param_bn::decomposition::Counter;
use biodivine_lib_param_bn::biodivine_std::traits::Set;
use biodivine_lib_param_bn::BooleanNetwork;
use std::convert::TryFrom;

fn main() {
    let mut buffer = String::new();
    std::io::stdin().read_to_string(&mut buffer).unwrap();

    let model = BooleanNetwork::try_from(buffer.as_str()).unwrap();
    println!("Model vars: {}", model.as_graph().num_vars());

    let graph = SymbolicAsyncGraph::new(model).unwrap();
    println!("Graph size: {} (Colors {})", graph.unit_colored_vertices().approx_cardinality(), graph.unit_colors().approx_cardinality());
    let count = decomposition(&graph);
    println!("Counted: {}", count);
}

fn decomposition(graph: &SymbolicAsyncGraph) -> usize {
    let mut counter = Counter::new(graph);

    let mut universes = vec![(graph.mk_unit_colored_vertices(), graph.as_network().variables().next().unwrap())];

    let start = std::time::SystemTime::now();
    let mut trimming = 0;
    let mut reach = 0;
    while let Some((universe, base)) = universes.pop() {
        let remaining: f64 = universes.iter().map(|u| u.0.approx_cardinality()).sum();
        println!("Universes: {}; SCCs: {}; Remaining: {}/{}", universes.len(), counter.len(), remaining + universe.approx_cardinality(), graph.unit_colored_vertices().approx_cardinality());
        println!("Elapsed: {}; Trim: {}; Reach: {};", start.elapsed().unwrap().as_millis(), trimming, reach);
        let start_trim = std::time::SystemTime::now();
        let universe = &trim(graph, universe);
        trimming += start_trim.elapsed().unwrap().as_millis();
        if universe.is_empty() {
            println!("NO SCC");
            continue;
        }

        let pivot = &universe.pick_vertex();
        let start_reach = std::time::SystemTime::now();

        let mut fwd = pivot.clone();
        let mut bwd = pivot.clone();
        let mut done_fwd = graph.mk_empty_colors();

        // Compute fwd/bwd in lockstep
        {
            let mut remaining = universe.colors();
            while !remaining.is_empty() {
                // Compute successors with `remaining` colors that are in `universe` and not `fwd`.
                let next_fwd = graph.post(&fwd.intersect_colors(&remaining)).intersect(&universe).minus(&fwd);
                let next_fwd_colors = next_fwd.colors();
                // Fwd completed for everything that was in remaining but now isn't.
                done_fwd = done_fwd.union(&remaining.minus(&next_fwd_colors));
                remaining = remaining.intersect(&next_fwd_colors);
                fwd = fwd.union(&next_fwd);

                // Compute predecessors with `remaining` colors that are in `universe` and not `bwd`.
                let next_bwd = graph.pre(&bwd.intersect_colors(&remaining)).intersect(&universe).minus(&bwd);
                remaining = remaining.intersect(&next_bwd.colors());
                bwd = bwd.union(&next_bwd);

                if fwd.as_bdd().size() > 100_000 || bwd.as_bdd().size() > 100_000 {
                    println!("Remaining: {}", remaining.approx_cardinality());
                    println!("FWD: {} ({}); BWD {} ({})", fwd.approx_cardinality(), fwd.as_bdd().size(), bwd.approx_cardinality(), bwd.as_bdd().size());
                }
            }
        }

        // Bwd is everything that isn't fwd.
        let done_bwd = universe.colors().minus(&done_fwd);

        // Finish fwd/bwd sets *after* lockstep.
        {
            let mut todo_bwd = done_fwd.clone();
            while !todo_bwd.is_empty() {
                let next_bwd = graph.pre(&bwd.intersect_colors(&todo_bwd)).intersect(&fwd).minus(&bwd);
                todo_bwd = next_bwd.colors();
                bwd = bwd.union(&next_bwd);
                if bwd.as_bdd().size() > 100_000 {
                    println!("BWD {} ({})", bwd.approx_cardinality(), bwd.as_bdd().size());
                }
            }

            let mut todo_fwd = done_bwd.clone();
            while !todo_fwd.is_empty() {
                let next_fwd = graph.post(&fwd.intersect_colors(&todo_fwd)).intersect(&bwd).minus(&fwd);
                todo_fwd = next_fwd.colors();
                fwd = fwd.union(&next_fwd);
                if fwd.as_bdd().size() > 100_000 {
                    println!("FWD: {} ({})", fwd.approx_cardinality(), fwd.as_bdd().size());
                }
            }
        }

        reach += start_reach.elapsed().unwrap().as_millis();

        let scc = &fwd.intersect(&bwd);
        let non_pivot_states = &scc.minus(&pivot);
        let non_trivial_colors = non_pivot_states.colors();
        println!("SCC: {} ({} vertices)", scc.approx_cardinality(), scc.vertices().approx_cardinality());
        if !non_trivial_colors.is_empty() {
            counter.push(&non_trivial_colors);
        } else {
            println!("TRIVIAL.");
        }

        let fwd_converged = fwd.intersect_colors(&done_fwd);
        let bwd_converged = bwd.intersect_colors(&done_bwd);
        let converged = fwd_converged.union(&bwd_converged).minus(&scc);
        let rest = universe.minus(&converged).minus(&scc);

        println!("SPLIT: {} - {}", rest.approx_cardinality(), converged.approx_cardinality());

        if !rest.is_empty() {
            universes.push((rest, base));
        }

        if !converged.is_empty() {
            universes.push((converged, base));
        }
    }

    counter.print();
    counter.len()
}

fn trim(graph: &SymbolicAsyncGraph, mut set: GraphColoredVertices) -> GraphColoredVertices {
    //let initial = set.as_bdd().size();
    //println!("Start trim: {}", initial);
    loop {
        // Predecessors of set inside set
        let pre = graph.pre(&set).intersect(&set);
        // Successors of these predecessors inside set.
        let post = graph.post(&pre).intersect(&set);
        // Everything in set \ post has no predecessor in this set.
        if set.is_subset(&post) {   // set == post
            break;
        }
        if set.as_bdd().size() > 10_000 {
            println!("TRIM: {}; {}", set.as_bdd().size(), set.approx_cardinality());
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
        if set.is_subset(&pre) {    // set == pre
            break;
        }
        if set.as_bdd().size() > 10_000 {
            println!("TRIM: {}; {}", set.as_bdd().size(), set.approx_cardinality());
        }
        set = pre;
        //if set.as_bdd().size() > 2 * initial {
        //    return set;
        //}
    }

    set
}