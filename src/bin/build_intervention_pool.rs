use biodivine_lib_param_bn::{BooleanNetwork, FnUpdate};
use biodivine_lib_param_bn::BinaryOp::{And, Imp};

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
            let pool = add_intervention_parameters(model);
            std::fs::write(format!("{target_dir}/{file_name}"), pool.to_string()).unwrap();
        }
    }
}

fn add_intervention_parameters(pool: BooleanNetwork) -> BooleanNetwork {
    let mut new_pool = pool.clone();

    for var in new_pool.variables() {
        if &Some(FnUpdate::Var(var)) == new_pool.get_update_function(var) {
            // Skip inputs.
            continue;
        }

        let update = new_pool.get_update_function(var).clone().unwrap();
        let name = new_pool.get_variable_name(var);
        let p_name = format!("ctrl_{}", name);
        let p_id = new_pool.add_parameter(p_name.as_str(), 0).unwrap();
        let fn_update = FnUpdate::mk_binary(
            And,
            FnUpdate::mk_binary(
                Imp,
                FnUpdate::Param(p_id, Vec::new()),
                FnUpdate::Var(var)
            ),
            FnUpdate::mk_binary(
                Imp,
                FnUpdate::mk_not(FnUpdate::Param(p_id, Vec::new())),
                update.clone(),
            ),
        );
        new_pool.set_update_function(var, Some(fn_update)).unwrap();
    }

    new_pool
}