use biodivine_lib_param_bn::BinaryOp::{Iff, Or, Xor};
use biodivine_lib_param_bn::{BooleanNetwork, FnUpdate, Monotonicity, RegulatoryGraph};

/// Goes through the given source directory (first argument), takes every `.aeon` file,
/// interprets it as a regulatory graph, builds a classic monotonic model pool for it,
/// and dumps it with the same name into the target directory (second argument).
fn main() {
    let args = std::env::args().collect::<Vec<_>>();
    let source_dir = args[1].clone();
    let target_dir = args[2].clone();

    for file in std::fs::read_dir(source_dir).unwrap() {
        let file = file.unwrap();
        let file_name = file.file_name();
        let file_name = file_name.to_str().unwrap();
        if file_name.ends_with(".aeon") {
            println!("Processing: {file_name}");

            let model_string = std::fs::read_to_string(file.path()).unwrap();
            let model = BooleanNetwork::try_from(model_string.as_str()).unwrap();
            if let Some(pool) = build_monotonic_pool(model.as_graph()) {
                std::fs::write(format!("{target_dir}/{file_name}"), pool.to_string()).unwrap();
            } else {
                println!("Model is not monotonic.");
            }
        }
    }
}

fn build_monotonic_pool(graph: &RegulatoryGraph) -> Option<BooleanNetwork> {
    let pool_rg = copy_rg_with_self_loops(graph);

    let mut pool_bn = BooleanNetwork::new(pool_rg);

    for var in pool_bn.variables() {
        let name = pool_bn.get_variable_name(var);
        let original_id = graph.find_variable(name).unwrap();

        if graph.regulators(original_id).is_empty() {
            // Turn constants into inputs:
            pool_bn
                .set_update_function(var, Some(FnUpdate::mk_var(var)))
                .unwrap();
        } else {
            // Build the whole function:

            let mut function = FnUpdate::mk_false();

            // Build individual disjunction clauses.
            for original_regulator in graph.regulators(original_id) {
                let regulator = pool_bn
                    .as_graph()
                    .find_variable(graph.get_variable_name(original_regulator))
                    .unwrap();
                let regulation = graph
                    .find_regulation(original_regulator, original_id)
                    .unwrap();
                let clause = match regulation.get_monotonicity() {
                    Some(Monotonicity::Activation) => {
                        FnUpdate::mk_binary(Xor, FnUpdate::mk_var(var), FnUpdate::mk_var(regulator))
                    }
                    Some(Monotonicity::Inhibition) => {
                        FnUpdate::mk_binary(Iff, FnUpdate::mk_var(var), FnUpdate::mk_var(regulator))
                    }
                    None => return None, // Non-monotonic network.
                };
                function = FnUpdate::mk_binary(Or, function, clause);
            }

            // Add final xor.
            function = FnUpdate::mk_binary(Xor, FnUpdate::mk_var(var), function);

            pool_bn.set_update_function(var, Some(function)).unwrap();
        }
    }

    Some(pool_bn)
}

/// Copy existing regulatory graph while adding self-loop regulations to everything
/// and erasing any observability/monotonicity constraints.
fn copy_rg_with_self_loops(graph: &RegulatoryGraph) -> RegulatoryGraph {
    let variable_names = graph
        .variables()
        .map(|it| graph.get_variable_name(it).clone())
        .collect::<Vec<_>>();

    let mut new_rg = RegulatoryGraph::new(variable_names);

    // Copy existing regulations.
    for reg in graph.regulations() {
        new_rg
            .add_regulation(
                graph.get_variable_name(reg.get_regulator()),
                graph.get_variable_name(reg.get_target()),
                false,
                None,
            )
            .unwrap();
    }

    // Add self-loops for variables that don't have them.
    for var in new_rg.variables() {
        if new_rg.find_regulation(var, var).is_none() {
            let name = new_rg.get_variable_name(var).clone();
            new_rg.add_regulation(&name, &name, false, None).unwrap();
        }
    }

    new_rg
}
