use std::collections::{HashMap, HashSet};
use biodivine_lib_param_bn::biodivine_std::traits::Set;
use biodivine_lib_param_bn::{BooleanNetwork, FnUpdate, Monotonicity, VariableId};
use biodivine_lib_param_bn::symbolic_async_graph::SymbolicAsyncGraph;

/*
    The basic idea is the following: Instead of using *any* transition during reachability,
    let's group transitions going in "one direction" (i.e. increasing and decreasing).

    First, this could just flat out "work better", similar to how saturation helps. However, this
    could also have useful implications for locally monotonic networks.

    Some observations why this might be good (applied to increase, decrease is symmetric):
     - We don't have to consider variables that are already universally `1`.
     - If x regulates y with negative monotonicity, and y cannot be increased, then increasing
       x cannot enable y to increase (I think).
     - Consequently, we might be able to just "propagate" positive dependencies in "BFS layers"
       and disregard everything else? Also, there should be some limit on how many times we have
       to repeat positive cycles (probably just once?)
     - Also, we can test the following: Assuming we take the whole space of possibly increased
       values, is there a way to increase this value? I.e. is there even a single transition from
       0 to 1 in this space? Because if not, we can just never update it.

    Subsequently, the question is, how often do we have to switch between increase and decrease
    modes. In the worst case, this can probably still be a lot, but my intuition is that it
    actually might not be as bad in practice.

 */

fn main() {
    let args = std::env::args().collect::<Vec<_>>();
    let model = BooleanNetwork::try_from_file(args[1].as_str()).unwrap();
    let mut model = model.infer_valid_graph().unwrap();
    // Fix inputs.
    for var in model.variables() {
        if model.get_update_function(var).is_none() {
            model.set_update_function(var, Some(FnUpdate::mk_true())).unwrap();
        }
    }
    let stg = SymbolicAsyncGraph::new(model.clone()).unwrap();

    /*let mut transitive_targets = HashMap::new();
    for var in model.variables() {
        transitive_targets.insert(var, model.as_graph().transitive_targets(var));
    }*/

    let mut remaining = stg.mk_unit_colored_vertices();
    while !remaining.is_empty() {
        /*let mut set = remaining.pick_vertex();
        'fwd: loop {
            for var in model.variables().rev() {
                let var_post = stg.var_post(var, &set);
                if !var_post.is_subset(&set) {
                    set = set.union(&var_post);
                    if set.symbolic_size() > 10_000 {
                        println!("Updated {}, result {} nodes.", var.to_index(), set.symbolic_size());
                    }
                    continue 'fwd;
                }
            }
            break;
        }
        remaining = remaining.minus(&set);*/

        let mut set = remaining.pick_vertex();
        let mut done = false;
        while !done {
            done = true;
            let mut remaining_vars: HashSet<VariableId> = HashSet::from_iter(model.variables());
            'increase: loop {
                let mut check = remaining_vars.iter().cloned().collect::<Vec<_>>();
                check.sort();
                check.reverse();

                let mut roots = Vec::new();
                'scan: for var in check.clone() {
                    for regulator in model.regulators(var) {
                        let reg = model.as_graph().find_regulation(regulator, var).unwrap();
                        // The node is not a "root" if it has a dependency that isn't checked yet.
                        if reg.get_monotonicity().unwrap() == Monotonicity::Activation && remaining_vars.contains(&regulator) {
                            continue 'scan;
                        }
                    }
                    roots.push(var);
                }

                println!("Got {} roots.", roots.len());
                if !roots.is_empty() {
                    for var in roots {
                        let var_increase = stg.var_post(var, &set.fix_network_variable(var, false));
                        set = set.union(&var_increase);
                        remaining_vars.remove(&var);

                        for target in model.targets(var) {
                            let reg = model.as_graph().find_regulation(var, target).unwrap();
                            if reg.get_monotonicity().unwrap() == Monotonicity::Activation {
                                remaining_vars.insert(target);
                            }
                        }

                        println!("Increased root {}, result {} nodes, queue {}.", var.to_index(), set.symbolic_size(), remaining_vars.len());
                    }
                    continue 'increase;
                }

                for var in check {
                    remaining_vars.remove(&var);
                    // Increase states where var=false.
                    let var_increase = stg.var_post(var, &set.fix_network_variable(var, false));
                    if !var_increase.is_subset(&set) {

                        for target in model.targets(var) {
                            let reg = model.as_graph().find_regulation(var, target).unwrap();
                            if reg.get_monotonicity().unwrap() == Monotonicity::Activation {
                                remaining_vars.insert(target);
                            }
                        }

                        set = set.union(&var_increase);
                        println!("Increased {}, result {} nodes, queue {}.", var.to_index(), set.symbolic_size(), remaining_vars.len());
                        done = false;
                        continue 'increase;
                    } else {
                        println!("No increase in {} (queue {}).", var.to_index(), remaining_vars.len());
                    }
                }
                break;
            }

            'decrease: loop {
                for var in model.variables().rev() {
                    // Decrease states where var=true.
                    let var_decrease = stg.var_post(var, &set.fix_network_variable(var, true));
                    if !var_decrease.is_subset(&set) {
                        set = set.union(&var_decrease);
                        if set.symbolic_size() > 1_000 {
                            println!("Decreased {}, result {} nodes.", var.to_index(), set.symbolic_size());
                        }
                        done = false;
                        continue 'decrease;
                    }
                }
                break;
            }
        }

        remaining = remaining.minus(&set);
        println!("Switch!");
    }
}