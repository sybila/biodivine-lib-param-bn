use std::cmp::min;
use biodivine_lib_param_bn::biodivine_std::traits::Set;
use biodivine_lib_param_bn::symbolic_async_graph::{GraphColoredVertices, GraphColors, SymbolicAsyncGraph};
use biodivine_lib_param_bn::{BooleanNetwork, FnUpdate, ParameterId, VariableId};
use std::collections::HashSet;
use biodivine_lib_bdd::{BddPartialValuation, BddVariable};

fn main() {
    let args = std::env::args().collect::<Vec<_>>();
    let network_path = args[1].clone();
    let network_string = std::fs::read_to_string(network_path).unwrap();
    let pool = BooleanNetwork::try_from(network_string.as_str()).unwrap();
    println!("Loaded a model pool with {} variables.", pool.num_vars(),);

    let stg = SymbolicAsyncGraph::new(pool.clone()).unwrap();

    println!(
        "STG: {} x {}",
        stg.unit_colored_vertices().vertices().approx_cardinality(),
        stg.unit_colors().approx_cardinality()
    );

    let mut inputs = HashSet::new();
    for var in pool.variables() {
        if &Some(FnUpdate::Var(var)) == pool.get_update_function(var) {
            inputs.insert(var);
        }
    }

    println!("Network has {} input(s).", inputs.len());

    let mut has_feedback = HashSet::new();
    for scc in pool.as_graph().components() {
        if scc.len() > 1 {
            for var in scc {
                has_feedback.insert(var);
            }
        }
    }

    println!("Network has {} feedback variable(s).", has_feedback.len());

    let mut stabilising_interventions = stg.mk_unit_colors();
    let mut trap_spaces = Vec::new();

    for var in pool.variables() {
        if inputs.contains(&var) {
            println!("Skipping input variable {}.", pool.get_variable_name(var));
            continue;
        }
        trap_spaces.push(stg.fix_network_variable(var, true));
        //trap_spaces.push(stg.fix_network_variable(var, false));
        println!("Initialized {}.", pool.get_variable_name(var));
    }

    while let Some(trap) = trap_spaces.pop() {
        match step(&stg, trap) {
            Ok(colors) => {
                stabilising_interventions = stabilising_interventions.intersect(&colors);
                trap_spaces = trap_spaces.into_iter()
                    .map(|it| it.intersect_colors(&stabilising_interventions))
                    .collect();
                println!("Finished process. Remaining: {}", trap_spaces.len());
            }
            Err(trap) => {
                trap_spaces.push(trap);
                trap_spaces.sort_by_key(|it| -(it.as_bdd().size() as isize));
            }
        }
    }

    /*for var in pool.variables() {
        if inputs.contains(&var) {
            println!("Skipping input variable {}.", pool.get_variable_name(var));
            continue;
        }
        let var_true = stg.fix_network_variable(var, true).intersect_colors(&stabilising_interventions);
        let var_false = stg.fix_network_variable(var, false).intersect_colors(&stabilising_interventions);

        let true_trap = stg.trap_forward(&var_true);
        let observably_stable = true_trap.colors();
        // Remove colours that are already know
        let var_false = var_false.minus_colors(&observably_stable);
        let false_trap = stg.trap_forward(&var_false);
        let observably_stable = observably_stable.union(&false_trap.colors());

        println!(
            "Variable {} is observably stable: {}",
            pool.get_variable_name(var),
            observably_stable.approx_cardinality(),
        );

        stabilising_interventions = stabilising_interventions.intersect(&observably_stable);
    }*/

    println!("Total stabilising interventions: {}", stabilising_interventions.approx_cardinality());
    println!("{}", stabilising_interventions.as_bdd().to_string());

    let best = find_best(&stg, stabilising_interventions.clone());
    println!("Best intervention: {}", best);
}


fn step(stg: &SymbolicAsyncGraph, trap: GraphColoredVertices) -> Result<GraphColors, GraphColoredVertices> {
    for var in stg.as_network().variables().rev() {
        let step = stg.var_can_post_out(var, &trap);
        if !step.is_empty() {
            return Err(trap.minus(&step));
        }
    }

    Ok(trap.colors())
}

/*
def find_valid(cutoff, k_active, k_remaining, perturbations):
	if perturbations.is_empty():
		# Dead end - return some sufficiently large value
		return pool.num_vars() + 1
	if len(k_active) >= cutoff:
		return pool.num_vars() + 1
	if not perturbations.intersect(knockout_as_params(pool, stg, k_active)).is_empty():
		print(f"Found {k_active} // {len(k_active)}")
		return len(k_active)
	if len(k_remaining) == 0:
		return pool.num_vars() + 1

	head, *tail = k_remaining
	head_true = stg.fix_parameter(f"ctrl_{head}", True)
	head_false = stg.fix_parameter(f"ctrl_{head}", False)
	not_included = find_valid(cutoff, k_active, tail, perturbations.intersect(head_false))
	included = find_valid(min(cutoff, not_included), k_active + [head], tail, perturbations.intersect(head_true))
	return min(not_included, included)

 */

fn build_intervention(
    stg: &SymbolicAsyncGraph,
    intervention: &BddPartialValuation
) -> GraphColors {
    let ctx = stg.symbolic_context();
    let bdd = ctx.bdd_variable_set().mk_conjunctive_clause(&intervention);
    stg.empty_colors().copy(bdd)
}

fn find_best(
    stg: &SymbolicAsyncGraph,
    candidates: GraphColors
) -> usize {
    let mut intervention = BddPartialValuation::empty();
    for var in stg.symbolic_context().parameter_variables() {
        intervention.set_value(*var, false);
    }
    let mut remaining = stg.symbolic_context().parameter_variables().clone();
    let best = find_best_intervention(
        stg,
        remaining.len(),
        &mut intervention,
        &mut remaining,
        candidates
    );

    assert_eq!(remaining.len(), stg.symbolic_context().parameter_variables().len());
    assert_eq!(0, count_ones(stg.symbolic_context().parameter_variables(), &intervention));

    best
}

fn find_best_intervention(
    stg: &SymbolicAsyncGraph,
    cutoff: usize,
    intervention: &mut BddPartialValuation,
    remaining: &mut Vec<BddVariable>,
    candidates: GraphColors
) -> usize {
    if candidates.is_empty() {
        // No remaining interventions possible.
        return usize::MAX;
    }
    if count_ones(stg.symbolic_context().parameter_variables(), intervention) >= cutoff {
        // The current considered intervention is larger than previous maximal one.
        return usize::MAX;
    }
    if !candidates.intersect(&build_intervention(stg, &intervention)).is_empty() {
        // The chosen intervention candidate is within the available candidates. We found a minimal
        // intervention set.
        return count_ones(stg.symbolic_context().parameter_variables(), intervention);
    }
    if remaining.is_empty() {
        // There are no remaining variables that we could put into the intervention.
        return usize::MAX;
    }

    let intervention_var = remaining.pop().unwrap();

    let candidates_true = candidates.as_bdd().var_select(intervention_var, true);
    let candidates_true = stg.empty_colors().copy(candidates_true);
    let candidates_false = candidates.as_bdd().var_select(intervention_var, false);
    let candidates_false = stg.empty_colors().copy(candidates_false);

    let without_var = find_best_intervention(stg, cutoff, intervention, remaining, candidates_false);

    intervention.set_value(intervention_var, true);
    let with_var = find_best_intervention(stg, min(without_var, cutoff), intervention, remaining, candidates_true);
    intervention.set_value(intervention_var, false);

    remaining.push(intervention_var);

    min(without_var, with_var)
}

/// Count the number of ones in the valuation that are within the given context set of variables.
fn count_ones(context: &[BddVariable], valuation: &BddPartialValuation) -> usize {
    let mut total = 0;
    for var in context {
        if Some(true) == valuation.get_value(*var) {
            total += 1;
        }
    }
    total
}