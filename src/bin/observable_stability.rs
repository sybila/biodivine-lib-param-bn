use biodivine_lib_param_bn::biodivine_std::traits::Set;
use biodivine_lib_param_bn::symbolic_async_graph::SymbolicAsyncGraph;
use biodivine_lib_param_bn::{BooleanNetwork, FnUpdate};
use std::collections::HashSet;

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

    let mut total = 0;
    let mut total_feedback = 0;
    for var in pool.variables() {
        if inputs.contains(&var) {
            println!("Skipping input variable {}.", pool.get_variable_name(var));
            continue;
        }
        let var_true = stg.fix_network_variable(var, true);
        let var_false = stg.fix_network_variable(var, false);

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

        if !observably_stable.is_empty() {
            total += 1;
            if has_feedback.contains(&var) {
                total_feedback += 1;
            }
        }
    }

    println!("Total observably stable: {}", total);
    println!("Total observably stable with feedback: {}", total_feedback);
}

