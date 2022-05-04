use biodivine_lib_param_bn::{BooleanNetwork, FnUpdate, VariableId};
use std::convert::TryFrom;
use std::io::Read;

/// Takes an input aeon model with uninterpreted/implicit update functions and transforms it
/// to bnet with synthetic parameters. The resulting bnet model has no restrictions on the values
/// of parameters (similar to aeon file where every regulation is non-observable and unspecified).
fn main() {
    let mut buffer = String::new();
    std::io::stdin().read_to_string(&mut buffer).unwrap();

    let mut model = BooleanNetwork::try_from(buffer.as_str()).unwrap();
    //let introduce_parameters = collect_synthetic_parameter_names(&model);
    //println!("New parameters: {:?}", introduce_parameters);
    for var in model.variables() {
        flatten_update_function(&mut model, var);
    }

    println!("{}", model.to_bnet(false).unwrap());
}

/// Replace the update function of the given `variable` with a flattened version using only
/// zero arity parameters.
fn flatten_update_function(network: &mut BooleanNetwork, variable: VariableId) {
    if network.regulators(variable).is_empty() {
        // Skip zero-regulator variables.
        return;
    }

    let flattened = if let Some(function) = network.get_update_function(variable) {
        let function = function.clone(); // Clone necessary for borrow checking.
        flatten_fn_update(network, &function)
    } else {
        let regulators = network.regulators(variable);
        let name = format!("{}_", network.get_variable_name(variable));
        explode_function(network, &regulators, name)
    };
    network
        .set_update_function(variable, Some(flattened))
        .unwrap();
}

fn flatten_fn_update(network: &mut BooleanNetwork, update: &FnUpdate) -> FnUpdate {
    match update {
        FnUpdate::Const(value) => FnUpdate::Const(*value),
        FnUpdate::Var(id) => FnUpdate::Var(*id),
        FnUpdate::Not(update) => flatten_fn_update(network, update).negation(),
        FnUpdate::Param(id, args) => {
            let name = network.get_parameter(*id).get_name().clone();
            explode_function(network, args, format!("{}_", name))
        }
        FnUpdate::Binary(op, left, right) => FnUpdate::Binary(
            *op,
            Box::new(flatten_fn_update(network, left)),
            Box::new(flatten_fn_update(network, right)),
        ),
    }
}

fn explode_function(
    network: &mut BooleanNetwork,
    regulators: &[VariableId],
    name_prefix: String,
) -> FnUpdate {
    if regulators.is_empty() {
        let parameter = network.find_parameter(name_prefix.as_str());
        let parameter =
            parameter.unwrap_or_else(|| network.add_parameter(name_prefix.as_str(), 0).unwrap());
        FnUpdate::Param(parameter, Vec::new())
    } else {
        let regulator = regulators[0];
        let true_branch = explode_function(network, &regulators[1..], format!("{}1", name_prefix));
        let false_branch = explode_function(network, &regulators[1..], format!("{}0", name_prefix));
        let var = FnUpdate::Var(regulator);
        var.clone()
            .implies(true_branch)
            .and(var.negation().implies(false_branch))
    }
}
