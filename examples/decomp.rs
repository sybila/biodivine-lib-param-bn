use biodivine_lib_param_bn::symbolic_async_graph::{SymbolicAsyncGraph, GraphColoredVertices};
use std::io::Read;
use biodivine_lib_param_bn::BooleanNetwork;
use std::convert::TryFrom;
use biodivine_lib_param_bn::biodivine_std::traits::Set;
use rayon::prelude::*;
use biodivine_lib_param_bn::decomposition::Counter;

fn main() {
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

    let mut universes = vec![graph.mk_unit_colored_vertices()];

    let mut too_small = Vec::new();
    let cut_off = (1 << graph.as_network().num_vars() / 2) as f64;

    for var in graph.as_network().variables() {
        println!("Starting {:?}", var);
        let is_true = graph.fix_network_variable(var, true);
        let is_false = graph.fix_network_variable(var, false);

        {
            let mapped: Vec<Vec<GraphColoredVertices>> = universes.par_iter().map(|universe| {
                //println!("Process {} / {}", universe.approx_cardinality(), universe.as_bdd().size());
                let fwd = fwd_saturation(&graph, &universe, is_true.intersect(&universe));
                let bwd = bwd_saturation(&graph, &universe, is_true.intersect(&universe));

                let mut result = Vec::new();
                let rest = universe.minus(&fwd).minus(&bwd);
                if !rest.is_empty() {
                    result.push(rest);
                }
                let both = fwd.intersect(&bwd);
                if !both.is_empty() {
                    result.push(both);
                }
                let only_bwd = bwd.minus(&fwd);
                if !only_bwd.is_empty(){
                    result.push(only_bwd);
                }
                let only_fwd = fwd.minus(&bwd);
                if !only_fwd.is_empty() {
                    result.push(only_fwd);
                }

                result
            }).collect();

            universes = mapped.into_iter().flat_map(|x| x).collect::<Vec<_>>();
        }

        println!("True done");

        {
            let mapped: Vec<Vec<GraphColoredVertices>> = universes.par_iter().map(|universe| {
                //println!("Process {} / {}", universe.approx_cardinality(), universe.as_bdd().size());
                let fwd = fwd_saturation(&graph, &universe, is_false.intersect(&universe));
                let bwd = bwd_saturation(&graph, &universe, is_false.intersect(&universe));

                let mut result = Vec::new();
                let rest = universe.minus(&fwd).minus(&bwd);
                if !rest.is_empty() {
                    result.push(rest);
                }
                let both = fwd.intersect(&bwd);
                if !both.is_empty(){
                    result.push(both);
                }
                let only_bwd = bwd.minus(&fwd);
                if !only_bwd.is_empty() {
                    result.push(only_bwd);
                }
                let only_fwd = fwd.minus(&bwd);
                if !only_fwd.is_empty() {
                    result.push(only_fwd);
                }

                result
            }).collect();

            universes = mapped.into_iter().flat_map(|x| x).collect::<Vec<_>>();
        }

        println!("False done");

        /*universes = universes
            .into_par_iter()
            .map(|universe: GraphColoredVertices| trim(&graph, universe))
            //.filter(|it| !it.is_empty() && it.approx_cardinality() > cut_off)
            .collect();*/

        let (mut to_remove, cont) = universes.into_iter().partition(|it| it.vertices().approx_cardinality() < cut_off);
        universes = cont;
        too_small.append(&mut to_remove);

        println!("Trim done");

        let sizes = universes.iter().map(|it| it.approx_cardinality()).collect::<Vec<_>>();
        println!("Sizes ({} / {}). Total {}/{}", sizes.len(), too_small.len(), sizes.iter().sum::<f64>(), graph.unit_colored_vertices().approx_cardinality());
    }

    universes.append(&mut too_small);

    let sizes = universes.iter().map(|it| it.approx_cardinality()).collect::<Vec<_>>();
    println!("Sizes ({}). Total {}/{}: {:?}", sizes.len(), sizes.iter().sum::<f64>(), graph.unit_colored_vertices().approx_cardinality(), sizes);

    let count = decomposition(&graph, universes);
    println!("Counted: {}", count);
}


fn decomposition(graph: &SymbolicAsyncGraph, mut universes: Vec<GraphColoredVertices>) -> usize {
    let mut counter = Counter::new(graph);

    let start = std::time::SystemTime::now();
    let mut trimming = 0;
    let mut reach = 0;
    while let Some(universe) = universes.pop() {
        //let too_small = (1 << (graph.as_network().num_vars() / 2)) as f64;
        //if universe.vertices().approx_cardinality() < too_small {
            // All components are too small.
            //continue;
        //}

        //let remaining: f64 = universes.iter().map(|u| u.approx_cardinality()).sum();
        println!(
            "Universes: {}; SCCs: {};",
            universes.len(),
            counter.len(),
        );
        println!(
            "Elapsed: {}; Trim: {}; Reach: {};",
            start.elapsed().unwrap().as_millis(),
            trimming,
            reach
        );
        let start_trim = std::time::SystemTime::now();
        let universe = &trim(graph, universe);
        trimming += start_trim.elapsed().unwrap().as_millis();
        if universe.is_empty() {
            println!("NO SCC");
            continue;
        }

        //if universe.vertices().approx_cardinality() < too_small {
            // All components are too small.
            //continue;
        //}

        let pivot = &universe.pick_vertex();
        let start_reach = std::time::SystemTime::now();
        let fwd = fwd_saturation(graph, &universe, pivot.clone());
        let bwd = bwd_saturation(graph, &universe, pivot.clone());
        reach += start_reach.elapsed().unwrap().as_millis();

        let scc = &fwd.intersect(&bwd);
        let non_pivot_states = &scc.minus(&pivot);
        let non_trivial_colors = non_pivot_states.colors();
        println!(
            "SCC: {} ({} vertices)",
            scc.approx_cardinality(),
            scc.vertices().approx_cardinality()
        );
        if !non_trivial_colors.is_empty() {
            //if scc.vertices().approx_cardinality() > too_small {
                counter.push(&non_trivial_colors);
            //}
        } else {
            println!("TRIVIAL.");
        }

        let rest = universe.minus(&fwd.union(&bwd));
        let above = bwd.minus(scc);
        let below = fwd.minus(scc);

        println!(
            "SPLIT: {} - {} - {}",
            rest.approx_cardinality(),
            above.approx_cardinality(),
            below.approx_cardinality()
        );

        if !rest.is_empty() {
            universes.push(rest);
        }

        if !above.is_empty() {
            universes.push(above);
        }

        if !below.is_empty() {
            universes.push(below);
        }
    }

    counter.print();
    counter.len()
}


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


fn trim(graph: &SymbolicAsyncGraph, mut set: GraphColoredVertices) -> GraphColoredVertices {
    let initial = set.as_bdd().size();
    //println!("Start trim: {}", initial);
    if set.as_bdd().size() > 10_000 {
        return set;
    }
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
        if set.as_bdd().size() > 10_000 {
            /*println!(
                "TRIM: {}; {}",
                set.as_bdd().size(),
                set.approx_cardinality()
            );*/
            return set;
        }
        if set.as_bdd().size() > 2 * initial {
            return set;
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
            /*println!(
                "TRIM: {}; {}",
                set.as_bdd().size(),
                set.approx_cardinality()
            );*/
            return set;
        }
        if set.as_bdd().size() > 2 * initial {
            return set;
        }
        set = pre;
    }

    set
}
