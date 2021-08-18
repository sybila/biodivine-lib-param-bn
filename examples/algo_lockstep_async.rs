use biodivine_lib_param_bn::symbolic_async_graph::{SymbolicAsyncGraph, GraphColoredVertices};
use biodivine_lib_param_bn::biodivine_std::traits::Set;
use std::io::Read;
use biodivine_lib_param_bn::{BooleanNetwork};
use std::convert::TryFrom;
use biodivine_lib_param_bn::decomposition::Counter;


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

        if bwd_converged {
            let above = bwd.minus(&scc);
            let rest = universe.minus(&bwd);

            println!("SPLIT: {} - {}", rest.approx_cardinality(), above.approx_cardinality());
            if !rest.is_empty() {
                universes.push((rest, base));
            }
            if !above.is_empty() {
                universes.push((above, base));
            }
        } else {
            let below = fwd.minus(&scc);
            let rest = universe.minus(&fwd);

            println!("SPLIT: {} - {}", rest.approx_cardinality(), below.approx_cardinality());
            if !rest.is_empty() {
                universes.push((rest, base));
            }
            if !below.is_empty() {
                universes.push((below, base));
            }
        }
    }

    counter.print();
    counter.len()
}

fn trim(graph: &SymbolicAsyncGraph, mut set: GraphColoredVertices) -> GraphColoredVertices {
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
    }

    set
}