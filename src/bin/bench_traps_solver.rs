use biodivine_lib_param_bn::biodivine_std::bitvector::BitVector;
use biodivine_lib_param_bn::fixed_points::FixedPoints;
use biodivine_lib_param_bn::solver_context::BnSolverContext;
use biodivine_lib_param_bn::trap_spaces::solver_iterator::SolverIterator;
use biodivine_lib_param_bn::trap_spaces::Space;
use biodivine_lib_param_bn::{BooleanNetwork, FnUpdate};

fn main() {
    let args = Vec::from_iter(std::env::args());
    let path = &args[1];
    let mut model = BooleanNetwork::try_from_file(path).unwrap();

    for var in model.variables() {
        if model.get_update_function(var).is_none() {
            model
                .set_update_function(var, Some(FnUpdate::Const(false)))
                .unwrap();
        }
    }
    //let model = model.inline_inputs();

    println!(
        "Loaded model with {} variables and {} parameters.",
        model.num_vars(),
        model.num_parameters()
    );

    /*println!("{}", model.to_string());

    for reg in model.as_graph().regulations() {
        if reg.get_monotonicity().is_none() {
            println!("Has non-monotonous reg.");
            break;
        }
    }*/

    let mut config = z3::Config::new();
    config.set_bool_param_value("auto_config", true); // Not sure if this does something...
    let z3 = z3::Context::new(&config);

    let ctx = BnSolverContext::new(&z3, model.clone());

    SolverIterator::recursive_iteration(&ctx);

    /*let iterator = SolverIterator::new(&ctx);

    println!(
        "{:?}",
        model
            .variables()
            .map(|it| model.get_variable_name(it))
            .collect::<Vec<_>>()
    );

    let mut i = 0;
    for model in iterator {
        println!("{}", model);
        i += 1;
        if i > 100 {
            println!("Too many traps to print.");
            return;
        }
    }

    if i == 0 {
        unreachable!("No traps were found.")
    } else {
        println!("All traps printed.");
    }*/
}
