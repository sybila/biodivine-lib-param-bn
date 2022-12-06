use biodivine_lib_param_bn::biodivine_std::bitvector::BitVector;
use biodivine_lib_param_bn::fixed_points::FixedPoints;
use biodivine_lib_param_bn::solver_context::BnSolverContext;
use biodivine_lib_param_bn::BooleanNetwork;
use biodivine_lib_param_bn::Space;

fn main() {
    let args = Vec::from_iter(std::env::args());
    let path = &args[1];
    let model = BooleanNetwork::try_from_file(path).unwrap();
    let model = model.inline_inputs();

    println!(
        "Loaded model with {} variables and {} parameters.",
        model.num_vars(),
        model.num_parameters()
    );

    let z3 = z3::Context::new(&z3::Config::new());

    let ctx = BnSolverContext::new(&z3, model.clone());

    let all_states = Space::new(&model);

    let iterator = FixedPoints::solver_iterator(&ctx, &[all_states], &[]);

    println!(
        "{:?}",
        model
            .variables()
            .map(|it| model.get_variable_name(it))
            .collect::<Vec<_>>()
    );

    let mut i = 0;
    for model in iterator {
        let values = model
            .get_state()
            .values()
            .into_iter()
            .map(i32::from)
            .collect::<Vec<_>>();
        println!("{:?}", values);
        i += 1;
        if i > 1000 {
            println!("Too many fixed-points to print.");
            return;
        }
    }

    if i == 0 {
        println!("No fixed-points are present.");
    } else {
        println!("All fixed points printed.");
    }
}
