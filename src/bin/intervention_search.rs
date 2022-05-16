use std::cmp::min;
use std::collections::HashSet;
use biodivine_lib_bdd::BddVariable;
use biodivine_lib_param_bn::{BooleanNetwork, FnUpdate, VariableId};
use biodivine_lib_param_bn::biodivine_std::traits::Set;
use biodivine_lib_param_bn::symbolic_async_graph::SymbolicAsyncGraph;

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

    let mut candidate_vars = pool.variables().collect::<Vec<_>>();
    candidate_vars.sort_by_cached_key(|it| pool.regulators(*it).len());
    let mut intervention = Vec::new();
    let best = find_best_intervention(&pool, usize::MAX, &mut intervention, &mut candidate_vars, true);
    println!("Best intervention: {}", best);
}

fn apply_intervention(bn: &BooleanNetwork, intervention: &Vec<VariableId>) -> BooleanNetwork {
    println!("Intervention: {:?}", intervention);
    let mut result = bn.clone();
    for var in intervention {
        result.set_update_function(*var, Some(FnUpdate::mk_var(*var))).unwrap();
    }
    result
}

fn is_all_stable(pool: BooleanNetwork) -> bool {
    let stg = SymbolicAsyncGraph::new(pool.clone()).unwrap();

    //println!("Considering {}", pool.to_string());
    for var in pool.variables() {
        let var_true = stg.fix_network_variable(var, true);
        let var_false = stg.fix_network_variable(var, false);

        let true_trap = stg.trap_forward(&var_true);
        let observably_stable = true_trap.colors();
        // Remove colours that are already know
        let var_false = var_false.minus_colors(&observably_stable);
        let false_trap = stg.trap_forward(&var_false);
        let observably_stable = observably_stable.union(&false_trap.colors());

        //println!("True trap: {}, False trap: {}", true_trap.colors().approx_cardinality(), false_trap.colors().approx_cardinality());

        if observably_stable.is_empty() {
            return false;
        }
    }

    true
}


fn find_best_intervention(
    pool: &BooleanNetwork,
    cutoff: usize,
    intervention: &mut Vec<VariableId>,
    remaining: &mut Vec<VariableId>,
    test: bool,
) -> usize {
    if intervention.len() >= cutoff {
        // The current considered intervention is larger than previous maximal one.
        return usize::MAX;
    }
    if test && is_all_stable(apply_intervention(pool, intervention)) {
        if intervention.len() < cutoff {
            println!("New best: {}", intervention.len());
        }
        return intervention.len();
    }
    if remaining.is_empty() {
        // There are no remaining variables that we could put into the intervention.
        return usize::MAX;
    }

    let intervention_var = remaining.pop().unwrap();
    intervention.push(intervention_var);
    let with_var = find_best_intervention(pool, cutoff, intervention, remaining, true);
    intervention.pop();

    let without_var = find_best_intervention(pool, min(cutoff, with_var), intervention, remaining, false);

    remaining.push(intervention_var);

    min(without_var, with_var)
}