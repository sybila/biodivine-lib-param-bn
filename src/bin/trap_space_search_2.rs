use biodivine_lib_param_bn::biodivine_std::traits::Set;
use biodivine_lib_param_bn::symbolic_async_graph::{GraphColoredVertices, SymbolicAsyncGraph};
use biodivine_lib_param_bn::{BooleanNetwork, FnUpdate, VariableId};
use std::collections::HashSet;

fn main() {
    let args = std::env::args().collect::<Vec<_>>();
    let buffer = std::fs::read_to_string(&args[1]).unwrap();

    let mut model = BooleanNetwork::try_from(buffer.as_str()).unwrap();
    // Fix inputs to true.
    for var in model.variables() {
        if model.get_update_function(var).is_none() {
            println!("Fix variable {:?}", var);
            model
                .set_update_function(var, Some(FnUpdate::Const(true)))
                .unwrap();
        }
    }

    let stg = SymbolicAsyncGraph::new(model.clone()).unwrap();
    /*let var = VariableId::try_from_usize(model.as_graph(), 6).unwrap();
    let percolated = percolate(&stg, &stg.mk_subspace(&[(var, true)]));
    println!("Is trap: {} Is empty: {}", stg.is_trap(&percolated), percolated.is_empty());
    let percolated = percolate(&stg, &stg.mk_subspace(&[(var, false)]));
    println!("Is trap: {} Is empty: {}", stg.is_trap(&percolated), percolated.is_empty());*/

    //let variables: HashSet<VariableId> = stg.as_network().variables().collect();
    //branch_search(&stg, stg.unit_colored_vertices(), variables);

    let variables: Vec<VariableId> = stg.as_network().variables().collect();
    branch_search_2(
        &stg,
        stg.unit_colored_vertices(),
        stg.unit_colored_vertices(),
        variables,
    );
}

/// Remove a variable from a vector, creating a copy.
fn remove_variable(variables: &[VariableId], variable: VariableId) -> Vec<VariableId> {
    variables
        .iter()
        .filter(|it| **it != variable)
        .cloned()
        .collect()
}

fn branch_search_2(
    stg: &SymbolicAsyncGraph,
    space_candidate: &GraphColoredVertices,
    trap_candidate: &GraphColoredVertices,
    mut free_variables: Vec<VariableId>,
) {
    // First, percolate the candidate
    print_space(stg, space_candidate);
    let ref space_candidate = constant_propagation(stg, space_candidate); //, &mut free_variables);
    let ref trap_candidate = trap_candidate.intersect(&space_candidate);
    print_space(stg, space_candidate);
    println!("{:?}", free_variables);

    for var in free_variables.clone() {
        println!("Check {:?}", var);
        let true_subspace = space_candidate.fix_network_variable(var, true);
        let false_subspace = space_candidate.fix_network_variable(var, false);

        let true_subspace = constant_propagation(stg, &true_subspace); //, &mut remove_variable(&free_variables, var));
        print_space(stg, &true_subspace);
        let true_subspace = tail_elimination(stg, &true_subspace);
        print_space(stg, &true_subspace);
        let true_subspace = constant_propagation(stg, &true_subspace); //, &mut remove_variable(&free_variables, var));
        print_space(stg, &true_subspace);
        let false_subspace = constant_propagation(stg, &false_subspace); //, &mut remove_variable(&free_variables, var));
        print_space(stg, &false_subspace);
        let false_subspace = tail_elimination(stg, &false_subspace);
        print_space(stg, &false_subspace);
    }
}

fn tail_elimination(
    stg: &SymbolicAsyncGraph,
    space: &GraphColoredVertices,
) -> GraphColoredVertices {
    let mut result = space.clone();
    loop {
        let mut trapped = result.clone();
        for var in stg.as_network().variables().rev() {
            trapped = trapped.minus(&stg.var_can_post_out(var, &result));
        }

        if trapped.is_empty() {
            return trapped;
        }

        if stg.find_subspace(&trapped.vertices()) == stg.find_subspace(&result.vertices()) {
            return stg.mk_subspace(&stg.find_subspace(&result.vertices()));
        }

        result = stg.mk_subspace(&stg.find_subspace(&trapped.vertices()));
        //print!("Iteration: ");
        //print_space(stg, &result);
    }
}

fn tail_elimination_2(
    stg: &SymbolicAsyncGraph,
    space: &GraphColoredVertices,
) -> GraphColoredVertices {
    let mut result = space.clone();

    'tail: loop {
        //println!("Result: {} / {}", result.approx_cardinality(), result.as_bdd().size());
        for var in stg.as_network().variables().rev() {
            let not_trapped = stg.var_can_post_out(var, &result);

            if !not_trapped.is_empty() {
                let new_result = result.minus(&not_trapped);

                if new_result.is_empty() {
                    return new_result;
                }

                if stg.find_subspace(&result.vertices())
                    != stg.find_subspace(&new_result.vertices())
                {
                    result = stg.mk_subspace(&stg.find_subspace(&new_result.vertices()));
                    //print!(" ----- ");
                    //print_space(stg, &result);
                    continue 'tail;
                } else {
                    result = new_result;
                    continue 'tail;
                }
            }
        }

        return result;
    }
}

fn constant_propagation(
    stg: &SymbolicAsyncGraph,
    space: &GraphColoredVertices,
) -> GraphColoredVertices {
    let mut result = space.clone();
    'propagation: loop {
        for var in stg.as_network().variables() {
            let true_subspace = result.fix_network_variable(var, true);
            let false_subspace = result.fix_network_variable(var, false);
            if true_subspace.is_empty() || false_subspace.is_empty() {
                continue;
            }

            let true_subspace_image = stg.var_post(var, &true_subspace);
            let false_subspace_image = stg.var_post(var, &false_subspace);

            //println!("Tested {:?} with {} / {}", var, true_subspace_image.approx_cardinality(), false_subspace_image.approx_cardinality());

            // If the variable is truly constant, one of the images must be empty.
            if true_subspace_image.is_empty() || false_subspace_image.is_empty() {
                if false_subspace.is_subset(&true_subspace_image) {
                    //println!("Var {:?} is false", var);
                    // Every state in true can map into false, the variable is guaranteed to be false.
                    result = false_subspace;
                    //*free_variables = remove_variable(&free_variables, var);
                    continue 'propagation;
                }
                if true_subspace.is_subset(&false_subspace_image) {
                    //println!("Var {:?} is true", var);
                    // Every state in false can map into true...
                    result = true_subspace;
                    //*free_variables = remove_variable(&free_variables, var);
                    continue 'propagation;
                }
                // Note that it is also possible that one of the images is empty, but the variable
                // still has a trap space for both values. I.e. there can be a region that simply
                // cannot perform a transition.
            }
        }

        /*if result.is_empty() {
            println!("Empty.");
        }*/
        return result;
    }
}

/*
fn branch_search(
    stg: &SymbolicAsyncGraph,
    candidate_space: &GraphColoredVertices,
    mut free_variables: HashSet<VariableId>,
) -> GraphColoredVertices {
    print_space(stg, candidate_space);
    let mut trap_basin = stg.mk_empty_vertices();
    for var in free_variables.clone() {
        println!("VAR: {:?}", var);
        let var_true = stg.fix_network_variable(var, true);

        let true_subspace = candidate_space.intersect(&var_true); //percolate(stg, &candidate_space.intersect(&var_true));
        let false_subspace = candidate_space.minus(&var_true); //percolate(stg, &candidate_space.minus(&var_true));

        println!("Percolated: {} / {}", true_subspace.approx_cardinality(), false_subspace.approx_cardinality());
        if true_subspace.is_empty() || false_subspace.is_empty() {
            free_variables.remove(&var);
            println!("Var is constant.");
            continue
        }

        let (_, true_trap_candidate) = simplify_trap(stg, &true_subspace.minus(&trap_basin));
        let (_, false_trap_candidate) = simplify_trap(stg, &false_subspace.minus(&trap_basin));

        let mut variables = free_variables.clone();
        variables.remove(&var);

        if !true_trap_candidate.is_empty() {
            let true_subspace = stg.mk_subspace(&stg.find_subspace(&true_trap_candidate.vertices()));
            let true_trap_basin = branch_search(stg, &true_subspace, variables.clone());
            trap_basin = trap_basin.union(&true_trap_basin);
        }

        if !false_trap_candidate.is_empty() {
            let false_subspace = stg.mk_subspace(&stg.find_subspace(&false_trap_candidate.vertices()));
            let false_trap_basin = branch_search(stg, &false_subspace, variables.clone());
            trap_basin = trap_basin.union(&false_trap_basin);
        }

        trap_basin = bwd(stg, &trap_basin, &candidate_space);
        if candidate_space.is_subset(&trap_basin) {
            // Everything done.
            break;
        }
    }

    if stg.is_trap(&candidate_space) {
        if trap_basin.is_empty() {
            println!("Minimum trap:");
        } else {
            println!("Also a trap, but not minimum.");
        }
        print_space(stg, &candidate_space);
        candidate_space.clone()
    } else {
        trap_basin
    }
}

fn simplify_trap(stg: &SymbolicAsyncGraph, trap: &GraphColoredVertices) -> (bool, GraphColoredVertices) {
    let mut result = trap.clone();
    'trap: loop {
        for var in stg.as_network().variables().rev() {
            let leaves_trap = stg.var_can_post_out(var, &result);

            if !leaves_trap.is_empty() {
                result = result.minus(&leaves_trap);

                if !spaces_are_equal(stg, &result, trap) {
                    // Result is smaller than trap, this is enough for now.
                    return (false, result);
                }

                continue 'trap;
            }
        }

        // Fixed-point is reached.
        return (true, result);
    }
}

fn spaces_are_equal(stg: &SymbolicAsyncGraph, set_a: &GraphColoredVertices, set_b: &GraphColoredVertices) -> bool {
    for var in stg.as_network().variables() {
        let is_true = stg.fix_network_variable(var, true);
        let is_false = stg.fix_network_variable(var, false);
        if is_true.is_subset(set_a) != is_true.is_subset(set_b) || is_false.is_subset(set_a) != is_false.is_subset(set_b) {
            return false;
        }
    }

    true
}*/

/*
fn branch_search(
    stg: &SymbolicAsyncGraph,
    space: &GraphColoredVertices
) -> GraphColoredVertices {
    if space.is_empty() {
        return stg.mk_empty_vertices();
    }

    if space.is_singleton() {
        // If the candidate is a single state, we just have to test if it is a trap.
        if stg.is_trap(space) {
            println!("Found singleton.");
            print_space(stg, space);
        }
        return space.clone();
    }

    // First, pick the best variable for conditioning. This is the variable for which we can
    // eliminate the most states just by fixing the value and doing percolation (or the first
    // variable if percolation odes not work).
    let mut best_var: Option<VariableId> = None;
    let mut best_size = space.exact_cardinality();

    for var in stg.as_network().variables() {
        let var_is_true = stg.fix_network_variable(var, true);
        let true_subspace = percolate(stg, &space.intersect(&var_is_true));
        let false_subspace = percolate(stg, &space.minus(&var_is_true));

        let relative_size = true_subspace.exact_cardinality() + false_subspace.exact_cardinality();
        //println!("Relative size ({:?}): {} / {}", var, true_subspace.approx_cardinality() / space.approx_cardinality(), false_subspace.approx_cardinality() / space.approx_cardinality());
        if relative_size < best_size || best_var == None {
            best_size = relative_size;
            best_var = Some(var);
        }
    }

    println!("Test space:");
    print_space(stg, space);
    println!("Condition on {:?} with {} vs. {}", best_var, best_size, space.exact_cardinality());

    let best_var = best_var.unwrap();
    let var_is_true = stg.fix_network_variable(best_var, true);
    let true_subspace = percolate(stg, &space.intersect(&var_is_true));
    let false_subspace = percolate(stg, &space.minus(&var_is_true));

    let true_trapped = branch_search(stg, &true_subspace);
    let false_trapped = branch_search(stg, &false_subspace);


    if true_trapped.is_empty() && false_trapped.is_empty() && stg.is_trap(&space) {
        println!("Found trap space.");
        print_space(stg, space);
        return space.clone();
    }

    //let trapped = true_trapped.union(&false_trapped);
    //let trapped = bwd(stg, &trapped, &space);

    //assert!(space.is_subset(&trapped));

    //trapped
    stg.mk_empty_vertices()
}*/

pub fn bwd(
    stg: &SymbolicAsyncGraph,
    initial: &GraphColoredVertices,
    space: &GraphColoredVertices,
) -> GraphColoredVertices {
    // TODO: Instead of intersection, find which variables in space are constant and ignore
    // those, since there's no way that they can be updated.

    let mut result = initial.clone();

    loop {
        let mut stop = true;
        // The order is important to update Bdd based on the "easiest" variables first.
        for var in stg.as_network().variables().rev() {
            let step = stg.var_pre_out(var, &result).intersect(&space);

            if !step.is_empty() {
                result = result.union(&step);
                stop = false;
                break;
            }
        }
        if cfg!(feature = "print_progress") && result.as_bdd().size() > 100_000 {
            println!("Backward progress: {}", result.as_bdd().size())
        }
        if stop {
            return result;
        }
    }
}
/*
/// Perform "constant propagation" on the given subspace, such that the result is still a subspace,
/// and all minimal trap spaces remain contained in the result.
///
/// Note that this only covers minimal trap spaces that are already in the given `space`.
/// If constant propagation shows that all transitions leave the given space, the result is empty,
/// not the new assumed superset of the trap space. In other worst, the result must always
/// be a subset of the argument.
fn percolate(stg: &SymbolicAsyncGraph, space: &GraphColoredVertices) -> GraphColoredVertices {
    let mut space = space.clone();
    loop {
        // The operations are performed until fixed-point. Note that a trap space will always
        // remain a trap space (if there is a transition outside, its target would have to be
        // included). However, a general subspace can become a trap space by percolation.

        let mut percolated_states = stg.mk_empty_vertices();

        // "Tail" percolation: Keep states that have a direct predecessor within the subspace.
        // This "minimizes" the subspace by removing transient states that cannot be visited
        // repeatedly.
        for var in stg.as_network().variables() {
            let has_predecessor_inside = stg.var_post_within(var, &space);
            percolated_states = percolated_states.union(&has_predecessor_inside);
        }

        // "Head" percolation: Remove states that have a direct successor outside the subspace.
        // This removes states that cannot appear in a trap set within this subspace.
        //
        // This is largely useless if the result already is a trap space, but testing if the
        // space is a trap space has similar complexity, so there doesn't seem to be a clear
        // benefit in not doing this.
        //
        for var in stg.as_network().variables() {
            let has_successor_outside = stg.var_can_post_out(var, &space);
            percolated_states = percolated_states.minus(&has_successor_outside);
        }

        //println!(" {} / {} ", space.approx_cardinality(), percolated_states.approx_cardinality());

        if percolated_states.is_empty() {
            //println!("Result empty");
            return stg.mk_empty_vertices();
        }

        let original_subspace = stg.find_subspace(&space.vertices());
        let percolated_subspace = stg.find_subspace(&percolated_states.vertices());

        if original_subspace == percolated_subspace {
            println!("Percolation finished:");
            print_space(&stg, &space);
            return space;
        } else {
            space = stg.mk_subspace(&percolated_subspace);
            //println!("Percolation step:");
            //print_space(&stg, &space);
        }
    }
}*/

fn print_space(stg: &SymbolicAsyncGraph, trap_space: &GraphColoredVertices) {
    print!("    > ");
    for var in stg.as_network().variables() {
        let is_true = stg.fix_network_variable(var, true);
        let is_false = stg.fix_network_variable(var, false);
        if !trap_space.is_subset(&is_true) && !trap_space.is_subset(&is_false) {
            print!("*");
        } else if trap_space.is_subset(&is_false) {
            print!("0");
        } else {
            print!("1");
        }
    }

    print!(" | Is trap? {}", stg.is_trap(&trap_space));
    print!(" | Is empty? {}", trap_space.is_empty());
    println!();
}
