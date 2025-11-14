use biodivine_lib_bdd::Bdd;
use biodivine_lib_param_bn::symbolic_async_graph::reachability::Reachability;
use biodivine_lib_param_bn::{BooleanNetwork, VariableId};
use biodivine_lib_param_bn::biodivine_std::traits::Set;
use biodivine_lib_param_bn::symbolic_async_graph::{GraphColoredVertices, SymbolicAsyncGraph};
use num_bigint::BigInt;
use num_traits::FromPrimitive;
use num_traits::One;
use std::cmp::max;
use std::cmp::min;
use std::io::Write;
use std::usize;

// A very basic benchmark for testing the performance of reachability procedures.


fn log_compression_ratio(bdd: &GraphColoredVertices) -> f64 {
    (bdd.as_bdd().cardinality() / (bdd.as_bdd().size() as f64)).log2()
}
fn log_progress(bdd: &GraphColoredVertices, all: &GraphColoredVertices) -> f64 {
    bdd.approx_cardinality().log2() / all.approx_cardinality().log2() * 100.0
}

fn main() {
    let args = std::env::args().collect::<Vec<_>>();
    let model = BooleanNetwork::try_from_file(args[1].as_str()).unwrap();
    let model = model.inline_inputs(true, true);

    println!(
        "Loaded model with {} variables and {} parameters.",
        model.num_vars(),
        model.num_parameters()
    );

    let stg = SymbolicAsyncGraph::new(&model).unwrap();

    let mut size_increase = 1000;
    let mut universe = stg.mk_unit_colored_vertices();
    let variables = stg.variables().collect::<Vec<_>>();
    while !universe.is_empty() {
        let pivot = universe.pick_vertex();
        let mut set = pivot.clone();
        let mut predecessors = stg.variables()
            .map(|x| stg.var_pre_out(x, &set))
            .collect::<Vec<_>>();

        loop {
            let mut step = stg.mk_empty_colored_vertices();
            let mut total_step_cardinality = 0.0;
            let mut total_step_size = 0;
            /*for v in stg.variables() {
                let next = stg.var_pre_out(v, &set);
                total_step_cardinality += next.as_bdd().cardinality();
                total_step_size += next.symbolic_size();
                if next.is_empty() {
                    continue;
                }

                step = step.union(&next);

                let approx = underapproximate_to_optimal_compression(step.as_bdd());
                step = GraphColoredVertices::new(approx, stg.symbolic_context());
            }*/
            /*for next in &predecessors {
                total_step_cardinality += next.as_bdd().cardinality();
                total_step_size += next.symbolic_size();
                if next.is_empty() {
                    continue;
                }

                step = step.union(&next);

                let approx = underapproximate_to_optimal_compression(step.as_bdd());
                step = GraphColoredVertices::new(approx, stg.symbolic_context());
            }*/
            let mut optimal_predecessors = predecessors.iter()
            .map(|x| {
                total_step_cardinality += x.as_bdd().cardinality();
                total_step_size += x.symbolic_size();
                let approx = underapproximate_to_optimal_compression(x.as_bdd());
                GraphColoredVertices::new(approx, stg.symbolic_context())
            })
            .collect::<Vec<_>>();

            let current_progress = log_progress(&set, &universe);
            let step_progress = (total_step_cardinality + set.approx_cardinality()).log2() / universe.approx_cardinality().log2() * 100.0;
            let max_progress_change = step_progress - current_progress;
            println!("Max step size: {}; max progress: {}", total_step_size, max_progress_change);

            if total_step_cardinality == 0.0 {
                break;
            }

            optimal_predecessors.sort_by_cached_key(|x| BigInt::from_f64(log_compression_ratio(x)));                        
            step = optimal_predecessors.pop().unwrap();

            if step.is_empty() {
                break;
            }            

            let mut recompute_predecessors = step.is_subset(&set);
            let old_progress = log_progress(&set, &universe);
            set = set.union(&step);
            let new_progress = log_progress(&set, &universe);
            let actual_progress_change = new_progress - old_progress;
            println!("Approx step: size {}; delta: {}; clauses: {}", step.symbolic_size(), actual_progress_change, step.as_bdd().exact_clause_cardinality());
            println!("New set: {}; progress: {}; compression: {}", set.symbolic_size(), log_progress(&set, &universe), log_compression_ratio(&set));

            if actual_progress_change < max_progress_change / 100.0 {
                recompute_predecessors = true;
                set = Reachability::reach_bwd(&stg, &set);//limited_reach_bwd(&stg, &set);//reach_bwd(&stg, &set, &variables, set.symbolic_size() * 1000);
            }
            /*if actual_progress_change < max_progress_change / 100.0 {
                recompute_predecessors = true;
                let mut next_set = stg.mk_empty_colored_vertices();
                for p in predecessors.iter() {
                    next_set = next_set.union(p);                    
                }
                //let approx = underapproximate_to_optimal_compression(next_set.as_bdd());
                //let next_set = GraphColoredVertices::new(approx, stg.symbolic_context());
                let old_progress = log_progress(&set, &universe);
                let old_size = set.symbolic_size();
                set = set.union(&next_set);
                //let approx = underapproximate_to_optimal_compression(set.as_bdd());
                let approx = set.as_bdd().underapproximate_to_size(old_size * 2);
                set = GraphColoredVertices::new(approx, stg.symbolic_context());
                let new_progress = log_progress(&set, &universe);
                let actual_progress_change = new_progress - old_progress;
                println!("Progress change by fast-forward: {}", actual_progress_change);
                println!("New set: {}; progress: {}; compression: {}", set.symbolic_size(), log_progress(&set, &universe), log_compression_ratio(&set));
            }*/

            // Update predecessors...
            if recompute_predecessors {                
                println!("Restarting backwards sets.");
                predecessors = stg.variables()
                    .map(|x| stg.var_pre_out(x, &set))
                    .collect::<Vec<_>>();
            } else {
                for v in stg.variables() {
                    let var_pre = stg.var_pre(v, &step);
                    let p = &mut predecessors[v.to_index()];
                    *p = p.union(&var_pre).minus(&set);
                    //*p = var_pre.minus(&set);
                }
            }
        }
        /*// Reach back
        let mut window_size = max(stg.num_vars() / 8, 1);
        while window_size < stg.num_vars() {
            println!("Window size: {}", window_size);
            let mut w = 0;
            while w < (stg.num_vars() - window_size) {
                println!("{}/{}...", w / window_size, (stg.num_vars() - window_size) / window_size);
                let window = &variables[w..(w+window_size)];
                set = reach_bwd(&stg, &set, window, set.symbolic_size() * 16);
                println!("New set: {} {} {}", set.as_bdd().size(), log_progress(&set, &universe), log_compression_ratio(&set));
                let approx = underapproximate_to_optimal_compression(set.as_bdd());
                set = GraphColoredVertices::new(approx, stg.symbolic_context());
                println!("Approx set: {} {} {}", set.as_bdd().size(), log_progress(&set, &universe), log_compression_ratio(&set));
                w += window_size;
            }
            window_size += 8;
        }

        set = set.union(&universe.pick_vertex());
        set = reach_bwd(&stg, &set, &variables, usize::MAX);
        println!("Final set: {} {}", set.symbolic_size(), set.approx_cardinality());
        assert!(false);*/
        /*'bwd: loop {
            //if set.symbolic_size() > 1_000 {
            
            fn recursive_merge(
                stg: &SymbolicAsyncGraph,
                items: &[GraphColoredVertices],
                target_cardinality: &BigUint,
            ) -> GraphColoredVertices {
                println!(
                    "Merging: {:?}",
                    items.iter().map(|x| x.symbolic_size()).collect::<Vec<_>>()
                );
                if items.len() == 1 {
                    return items[0].clone();
                }
                let mut merged = Vec::new();
                for i in 0..items.len() / 2 {
                    let merge = items[2 * i].union(&items[2 * i + 1]);
                    let approx = merge
                        .as_bdd()
                        .underapproximate_to_cardinality(&target_cardinality);
                    let merge = GraphColoredVertices::new(approx, stg.symbolic_context());
                    merged.push(merge);
                }
                if items.len() % 2 == 1 {
                    merged.push(items[items.len() - 1].clone());
                }
                return recursive_merge(&stg, &merged, target_cardinality);
            }

            /*println!(
                "BWD progress: {} ({}log-%; {}log-comp)",
                set.symbolic_size(),
                log_progress(&set, &universe),
                log_compression_ratio(&set)
            );*/            

            loop {
                let mut predecessors = stg
                    .variables()
                    .take(max_vars)
                    .map(|x| stg.var_pre_out(x, &set))
                    .collect::<Vec<_>>();

                predecessors.sort_by_cached_key(|x| -x.as_bdd().exact_cardinality());

                let improvements = predecessors
                    .iter()
                    .map(|x| x.approx_cardinality())
                    .collect::<Vec<_>>();

                let max_improvement: f64 = improvements.iter().sum();

                let current_log_percent = log_progress(&set, &universe);
                let new_log_percent = (set.approx_cardinality() + max_improvement).log2()
                / universe.approx_cardinality().log2()
                * 100.0;

                //if max_improvement == 0.0 || (max_vars != stg.num_vars() && (new_log_percent - current_log_percent) <= 0.5) {
                if max_improvement == 0.0 {
                    // Done.
                    break;
                }

                println!(
                    "Best possible improvement is to {}log-%. (delta: {})",
                    new_log_percent,
                    new_log_percent - current_log_percent
                );

                let target_improvement: f64 = max_improvement * 0.5;
                let target_improvement = BigUint::from_f64(target_improvement).unwrap();

                let mut step = stg.mk_empty_colored_vertices();
                for (i, s) in predecessors.iter().enumerate() {
                    if s.is_empty() {
                        continue;
                    }
                    step = step.union(&s);
                    //let approx = step.as_bdd().underapproximate_to_cardinality(&target_improvement);
                    //let approx = underapproximate_to_optimal_compression(step.as_bdd());
                    //step = GraphColoredVertices::new(approx, stg.symbolic_context());
                    //println!("{}/{} Step size increased to {}", i+1, predecessors.len(), step.symbolic_size());
                }
                //let step = recursive_merge(&stg, &predecessors, &target_improvement);
                println!("Computed step: {} {}", step.symbolic_size(), log_progress(&step, &universe));
                //let approx = underapproximate_to_optimal_compression(step.as_bdd());
                /*let approx = step.as_bdd().underapproximate_to_cardinality(&target_improvement);
                step = GraphColoredVertices::new(approx, stg.symbolic_context());
                println!("Approx step: {} {}", step.symbolic_size(), log_progress(&step, &universe));
                */

                let old_cardinality = set.approx_cardinality();
                let prev_step = set.clone();
                set = set.union(&step);
                let new_cardinality = set.approx_cardinality();

                // The improvement must be at least half of the actual improvement.
                let target_cardinality =
                    old_cardinality + (new_cardinality - old_cardinality) / 2.0;
                let target_cardinality = BigUint::from_f64(target_cardinality).unwrap();

                println!(
                    "New set: {} ({}log-%; {}log-comp)",
                    set.symbolic_size(),
                    log_progress(&set, &universe),
                    log_compression_ratio(&set)
                );

                //let approx = set.as_bdd().underapproximate_to_cardinality(&target_cardinality);
                /*let approx = underapproximate_to_optimal_compression(set.as_bdd());
                set = GraphColoredVertices::new(approx, stg.symbolic_context());
                println!("New optimal set: {} {}", set.as_bdd().size(), log_progress(&set, &universe));
                if set.exact_cardinality() <= prev_step.exact_cardinality() {
                    println!("The set has not increased... overriding!");
                    set = set.union(&prev_step).union(&step);
                } else {
                    println!(" >>>> The set has improved by approximation.");
                }*/

                println!(
                    "Approximated set: {} ({}log-%; {}log-comp)",
                    set.symbolic_size(),
                    log_progress(&set, &universe),
                    log_compression_ratio(&set)
                );
            }

            if max_vars == stg.num_vars() {
                break;
            } else {
                println!(" >>> Saturated {}/{} variables!", max_vars, stg.num_vars());
                max_vars += 1;
                let approx = underapproximate_to_optimal_compression(set.as_bdd());
                set = GraphColoredVertices::new(approx, stg.symbolic_context());
                println!(" >>> Start from approx set: {} {}", set.as_bdd().size(), log_progress(&set, &universe));
            }
        }*/
        // Reach front
        'fwd: loop {
            //if set.symbolic_size() > 1_000 {
            println!(
                "FWD progress: {} {}",
                set.symbolic_size(),
                set.approx_cardinality()
            );
            //}
            for var in model.variables().rev() {
                //let step = stg.var_post(var, &set).minus(&set);
                let step = stg.var_post_out(var, &set);
                if !step.is_empty() {
                    set = set.union(&step);
                    continue 'fwd;
                }
            }
            break 'fwd;
        }
        universe = universe.minus(&set);
        println!("Remaining: {}", universe.approx_cardinality());
    }
}

pub fn reach_bwd(stg: &SymbolicAsyncGraph, initial: &GraphColoredVertices, variables: &[VariableId], size_limit: usize) -> GraphColoredVertices {
    let mut result = initial.clone();
    'bwd: loop {
        for var in variables.iter().rev() {
            let step = stg.var_post_out(*var, &result);
            if !step.is_empty() {
                let old_progress = log_progress(&result, stg.unit_colored_vertices());
                let old_size = result.symbolic_size();
                result = result.union(&step);                
                let new_progress = log_progress(&result, stg.unit_colored_vertices());
                let new_size = result.symbolic_size();
                if new_size > (old_size * 3) / 2 {
                    //let approx = underapproximate_to_optimal_compression(result.as_bdd());
                    println!("Approximate to {}", (old_size * 3) / 2);
                    let approx = result.as_bdd().underapproximate_to_size((old_size * 3) / 2);
                    result = initial.union(&GraphColoredVertices::new(approx, stg.symbolic_context()));
                }
                let progress_delta = new_progress - old_progress;                
                println!("Increased reachability; size {}; progress: {}; variable {}; delta: {}.", result.symbolic_size(), new_progress, var.to_index(), progress_delta);
                //assert!(progress_delta > 0.0);
                if result.symbolic_size() > size_limit {
                    return result;
                }
                continue 'bwd; 
            }
        }
        println!("");
        return result;
    }
}

pub fn limited_reach_bwd(stg: &SymbolicAsyncGraph, initial: &GraphColoredVertices) -> GraphColoredVertices {
    let mut global_result = initial.clone();
    let mut result = initial.clone();
    let mut target_size = 10_000usize;
    'bwd: loop {
        for var in stg.variables().rev() {
            let step = stg.var_post_out(var, &result);
            if !step.is_empty() {
                let old_progress = log_progress(&result, stg.unit_colored_vertices());
                result = result.union(&step);                
                let new_progress = log_progress(&result, stg.unit_colored_vertices());
                let new_size = result.symbolic_size();
                if new_size > target_size {
                    // The set is too big!
                    if result.is_subset(&global_result) {
                        target_size *= 2;
                        println!("No progress was made. Increasing target size to {}", target_size);
                    } else {
                        global_result = global_result.union(&result);
                        let approx = result.as_bdd().underapproximate_to_size(target_size / 2);
                        result = initial.union(&GraphColoredVertices::new(approx, stg.symbolic_context()));
                        println!("Exceeded size limit. Approximated to {}.", result.symbolic_size());
                    }                        
                }
                let progress_delta = new_progress - old_progress;                
                println!("Increased reachability; size {}; progress: {}; variable {}; delta: {}.", result.symbolic_size(), new_progress, var.to_index(), progress_delta);
                continue 'bwd; 
            }
        }
        if global_result.is_subset(&result) {
            return global_result;
        }

        result = global_result.clone();
    }
}

pub fn underapproximate_to_optimal_compression(bdd: &Bdd) -> Bdd {
    if bdd.is_false() {
        return bdd.clone();
    }
    if bdd.is_true() {
        return bdd.clone();
    }

    // Compute the number of valuations going through each node and sort them.
    let mut weights = bdd
        .node_valuation_weights()
        .into_iter()
        .zip(bdd.pointers())
        .collect::<Vec<_>>();
    weights.sort_by(|(x, px), (y, py)| {
        // Smallest weights go first; if equal, biggest pointers go last.
        x.cmp(y).then(px.cmp(py).reverse())
    });
    let weights = Vec::from_iter(weights.into_iter().map(|(_, x)| x));

    fn compression_ratio(bdd: &Bdd) -> BigInt {
        max(
            BigInt::from(1),
            bdd.exact_cardinality() / BigInt::from(bdd.size()),
        )
    }

    // Binary-search for the number of nodes that give us the best compression ratio.
    let mut stop = 0usize;
    let mut increment = 1usize;
    // Initially, the best compression is the one achieved by the BDD right now.
    let mut max_compression = compression_ratio(bdd);
    if max_compression == BigInt::one() {
        return bdd.clone();
    }
    loop {
        assert!(increment > 0);
        assert!(max_compression > BigInt::one());
        let next_stop = min(stop + increment, weights.len());
        let next_approx = bdd.underapproximate(&weights[..next_stop]);
        let next_compression = compression_ratio(&next_approx);
        //println!("{} + {} | {} vs {}", stop, increment, next_compression, max_compression);
        if increment == 1 && next_compression < max_compression {
            // If the next value is worse, this is the best.
            return bdd.underapproximate(&weights[..stop]);
        } else {
            if next_compression < max_compression {
                // If *some* next value is worse, decrease the increment.
                increment = max(increment / 2, 1);
            } else {
                // If this value is better, move to it and increase increment.
                // next_compression >= max_compression
                max_compression = next_compression;
                increment = min(increment * 2, weights.len());
                stop = next_stop;
            }
        }
    }
}
