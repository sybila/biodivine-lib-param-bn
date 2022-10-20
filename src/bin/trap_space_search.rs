use biodivine_lib_param_bn::biodivine_std::traits::Set;
use biodivine_lib_param_bn::symbolic_async_graph::{GraphColoredVertices, SymbolicAsyncGraph};
use biodivine_lib_param_bn::{BooleanNetwork, FnUpdate, VariableId};
use std::convert::TryFrom;

// A very basic benchmark for testing the performance of reachability procedures.

fn main() {
    let args = std::env::args().collect::<Vec<_>>();
    let buffer = std::fs::read_to_string(&args[1]).unwrap();

    let mut model = BooleanNetwork::try_from(buffer.as_str()).unwrap();
    // Fix inputs to true.
    for var in model.variables() {
        if model.get_update_function(var).is_none() {
            model
                .set_update_function(var, Some(FnUpdate::Const(true)))
                .unwrap();
        }
    }

    let stg = SymbolicAsyncGraph::new(model.clone()).unwrap();

    /*let mut results: Vec<GraphColoredVertices> = Vec::new();
    let variables = model.variables().collect::<Vec<_>>();
    branch(
        &stg,
        stg.mk_unit_colored_vertices(),
        stg.mk_unit_colored_vertices(),
        &variables,
        &mut results
    );

    println!("Results: ");
    for result in &results {
        print_space(&stg, result);
    }*/

    trap_branch(&stg, stg.unit_colored_vertices());
}

fn trap_branch(stg: &SymbolicAsyncGraph, candidate: &GraphColoredVertices) -> GraphColoredVertices {
    let mut traps = stg.mk_empty_vertices();
    let mut traps_bwd = stg.mk_empty_vertices();
    for var in stg.as_network().variables().rev() {
        let is_true = stg.fix_network_variable(var, true);

        let true_subspace = candidate.intersect(&is_true);
        let false_subspace = candidate.minus(&is_true);

        if true_subspace.is_empty() || false_subspace.is_empty() {
            // This variable is already fixed.
            continue;
        }

        //println!("Check var: {}", var);

        let mut true_trap_candidate = true_subspace.clone();
        let mut false_trap_candidate = false_subspace.clone();

        for var in stg.as_network().variables() {
            true_trap_candidate =
                true_trap_candidate.minus(&stg.var_can_post_out(var, &true_trap_candidate));
            false_trap_candidate =
                false_trap_candidate.minus(&stg.var_can_post_out(var, &false_trap_candidate));
        }

        true_trap_candidate = expand_to_cube(stg, &true_trap_candidate);
        false_trap_candidate = expand_to_cube(stg, &false_trap_candidate);

        //println!("Test:");
        //print_space(stg, &candidate);

        /*if !true_trap_candidate.is_empty() {
            println!("True trap candidate: {}", true_trap_candidate.approx_cardinality());
            print_space(stg, &true_trap_candidate);
            let true_traps = trap_branch(stg, &true_trap_candidate);
            traps = traps.union(&true_traps);
        }

        if !false_trap_candidate.is_empty() {
            println!("False trap candidate: {}", false_trap_candidate.approx_cardinality());
            print_space(stg, &false_trap_candidate);
            let false_traps = trap_branch(stg, &false_trap_candidate);
            traps = traps.union(&false_traps);
        }*/

        // TODO: Do a hybrid: there is a limit on the number of steps, but the limit increases
        // with recursion, so if the trap set is actually empty, you are eventually going
        // to give it the resource to verify that.
        // Also, we can send the trap set "approximation" to the recursive calls so that they
        // don't have to start completely from scratch.
        // Similarly, we can propagate the backwards reachable parts to the "parent" calls
        // so that they don't have to recompute the reachability again.

        let true_trap = forward_closed(&stg, &true_subspace.minus(&traps_bwd));
        let false_trap = forward_closed(&stg, &false_subspace.minus(&traps_bwd));

        if !true_trap.is_empty() {
            println!(
                "Found true trap set of size {}",
                true_trap.approx_cardinality()
            );
            let true_traps = trap_branch(stg, &expand_to_cube(stg, &true_trap));
            traps = traps.union(&true_traps);
        }

        if !false_trap.is_empty() {
            println!(
                "Found false trap set of size {}",
                false_trap.approx_cardinality()
            );
            let false_traps = trap_branch(stg, &expand_to_cube(stg, &false_trap));
            traps = traps.union(&false_traps);
        }

        traps_bwd = traps_bwd.union(&traps);
        traps_bwd = backward(&stg, &traps_bwd, &candidate);
        if candidate.is_subset(&traps_bwd) {
            println!("Everything covered...");
            break;
        }
    }

    if is_trap_space(stg, &candidate) {
        if traps.is_empty() {
            println!("Minimum trap:");
        } else {
            println!("Also a trap, but not minimum.");
        }
        print_space(stg, &candidate);
        candidate.clone()
    } else {
        traps
    }
}

fn branch(
    stg: &SymbolicAsyncGraph,
    universe: GraphColoredVertices,
    candidate: GraphColoredVertices,
    branch_on: &[VariableId],
    results: &mut Vec<GraphColoredVertices>,
) -> bool {
    if universe.is_empty() || candidate.is_empty() {
        println!("Skip empty.");
        // Universe can become
        return false;
    }

    println!("1. Start processing.");
    print_space(stg, &candidate);

    // Assert that candidate is a trap set. Just in case.
    assert!(candidate.as_bdd().is_clause());

    let mut not_trapped = stg.mk_empty_vertices();
    for var in stg.as_network().variables() {
        let can_go_out = stg.var_can_post_out(var, &universe);
        not_trapped = not_trapped.union(&can_go_out);
    }
    let trapped = universe.minus(&not_trapped);
    println!("  Trapped states: {}", trapped.approx_cardinality());

    if trapped.is_empty() {
        // Universe is not empty, but everything goes out.
        return false;
    }

    let candidate = percolate(stg, &trapped, candidate);

    println!("  After percolation: ");
    print_space(stg, &candidate);

    if branch_on.is_empty() {
        println!("  Nothing more to branch on.");
        if is_trap_space(stg, &candidate) {
            println!("   Minimal trap.");
            print_space(stg, &candidate);
            results.push(candidate);
            return true;
        } else {
            return false;
        }
    } else if candidate.as_bdd().is_valuation() {
        if is_trap_space(stg, &candidate) {
            println!("   Minimal trap.");
            print_space(stg, &candidate);
            results.push(candidate);
            return true;
        } else {
            println!("   Single state but not trap.");
            return false;
        }
    } else {
        let mut i_var = 0;
        while i_var < branch_on.len() {
            let var_true = stg.fix_network_variable(branch_on[i_var], true);
            let var_false = stg.fix_network_variable(branch_on[i_var], false);
            if candidate.is_subset(&var_true) || candidate.is_subset(&var_false) {
                i_var += 1;
            } else {
                break;
            }
        }

        if i_var >= branch_on.len() {
            if is_trap_space(stg, &candidate) {
                println!("   Minimal trap.");
                print_space(stg, &candidate);
                results.push(candidate);
                return true;
            } else {
                println!("   All is percolated.");
                return false;
            }
        }
        let branch_var = branch_on[i_var];
        println!("  Branch on {}", branch_var);

        let var_true = stg.fix_network_variable(branch_var, true);
        let var_false = stg.fix_network_variable(branch_var, false);

        let has_trap_in_true = branch(
            stg,
            trapped.intersect(&var_true),
            candidate.intersect(&var_true),
            &branch_on[(i_var + 1)..],
            results,
        );

        let has_trap_in_false = branch(
            stg,
            trapped.intersect(&var_false),
            candidate.intersect(&var_false),
            &branch_on[(i_var + 1)..],
            results,
        );

        let has_trap_in_free = if !(has_trap_in_true || has_trap_in_false) {
            branch(
                stg,
                trapped.clone(),
                candidate.clone(),
                &branch_on[(i_var + 1)..],
                results,
            )
        } else {
            false
        };

        let has_smaller_trap = has_trap_in_true || has_trap_in_false || has_trap_in_free;
        if !has_smaller_trap && is_trap_space(stg, &candidate) {
            println!("   Minimal trap.");
            print_space(stg, &candidate);
            results.push(candidate);
            return true;
        } else {
            return has_smaller_trap;
        }
    }
}

fn is_trap_space(stg: &SymbolicAsyncGraph, candidate: &GraphColoredVertices) -> bool {
    for var in stg.as_network().variables() {
        if !stg.var_can_post_out(var, &candidate).is_empty() {
            return false;
        }
    }
    true
}

fn percolate(
    stg: &SymbolicAsyncGraph,
    trapped_states: &GraphColoredVertices,
    mut candidate: GraphColoredVertices,
) -> GraphColoredVertices {
    //print_space(stg, &candidate);
    //print_space(stg, &trapped_states);
    //println!("{}", trapped_states.approx_cardinality());
    for var in stg.as_network().variables() {
        let var_is_true = stg.fix_network_variable(var, true);
        if trapped_states.is_subset(&var_is_true) {
            candidate = candidate.intersect(&var_is_true);
        }

        let var_is_false = stg.fix_network_variable(var, false);
        if trapped_states.is_subset(&var_is_false) {
            candidate = candidate.intersect(&var_is_false);
        }
    }

    // Since the states are trapped, they must contain some kind of trap space and so the result
    // of percolation cannot be empty.
    assert!(!candidate.is_empty());
    assert!(candidate.as_bdd().is_clause());

    candidate
}

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
    println!();
}

/// Input a cube, output a larger cube
fn cube_fwd(stg: &SymbolicAsyncGraph, initial: &GraphColoredVertices) -> GraphColoredVertices {
    let mut result = initial.clone();
    'fwd: loop {
        for var in stg.as_network().variables().rev() {
            let can_go_out = stg.var_can_post_out(var, &result);
            if !can_go_out.is_empty() {
                result = make_variable_free(stg, var, &result);
                continue 'fwd;
            }
        }
        assert!(result.as_bdd().is_clause());
        return result;
    }
}

fn cube_bwd(stg: &SymbolicAsyncGraph, initial: &GraphColoredVertices) -> GraphColoredVertices {
    let mut result = initial.clone();
    'fwd: loop {
        for var in stg.as_network().variables().rev() {
            let can_go_out = stg.var_can_pre_out(var, &result);
            if !can_go_out.is_empty() {
                result = make_variable_free(stg, var, &result);
                continue 'fwd;
            }
        }
        assert!(result.as_bdd().is_clause());
        return result;
    }
}

fn expand_to_cube(stg: &SymbolicAsyncGraph, set: &GraphColoredVertices) -> GraphColoredVertices {
    let mut result = set.clone();
    for var in stg.as_network().variables() {
        let var_true = stg.fix_network_variable(var, true);
        let var_false = stg.fix_network_variable(var, false);
        if !(result.is_subset(&var_true) || result.is_subset(&var_false)) {
            result = make_variable_free(stg, var, &result);
        }
    }
    result
}

fn make_variable_free(
    stg: &SymbolicAsyncGraph,
    var: VariableId,
    cube: &GraphColoredVertices,
) -> GraphColoredVertices {
    let bdd_var = stg.symbolic_context().get_state_variable(var);
    let relaxed_bdd = cube.as_bdd().var_project(bdd_var);
    stg.empty_vertices().copy(relaxed_bdd)
}

/// Compute the largest forward closed subset of the `initial` set. That is, the states that can
/// only reach states inside `initial`.
///
/// In particular, if the initial set is a weak basin, the result is a strong basin.
pub fn forward_closed(
    graph: &SymbolicAsyncGraph,
    initial: &GraphColoredVertices,
) -> GraphColoredVertices {
    let mut i = 0;
    let mut basin = initial.clone();
    loop {
        i += 1;
        let mut stop = true;
        for var in graph.as_network().variables().rev() {
            let can_go_out = graph.var_can_post_out(var, &basin);
            //let outside_successors = graph.var_post(var, &basin).minus(&basin);
            //let can_go_out = graph.var_pre(var, &outside_successors).intersect(&basin);

            if !can_go_out.is_empty() {
                basin = basin.minus(&can_go_out);
                stop = false;
                break;
            }
        }
        if basin.as_bdd().size() > 10_000 {
            //println!("Skip");
            //return graph.mk_empty_vertices();
            println!("Forward closed progress: {}", basin.as_bdd().size())
        }
        if stop {
            //println!("I: {}", i);
            return basin;
        }
    }
}

/// Compute the coloured set of all backward reachable states from the `initial` set.
pub fn backward(
    graph: &SymbolicAsyncGraph,
    initial: &GraphColoredVertices,
    superset: &GraphColoredVertices,
) -> GraphColoredVertices {
    let mut result = initial.clone();

    loop {
        let mut stop = true;
        // The order is important to update Bdd based on the "easiest" variables first.
        for var in graph.as_network().variables().rev() {
            let step = graph
                .var_pre(var, &result)
                .minus(&result)
                .intersect(&superset);

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
