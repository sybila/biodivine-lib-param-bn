/*
   This is a very simple binary intended as an integration test for the solver fixed-point
   detection. In particular, it tries to enumerate the fixed-points using Z3 and then tests
   that each returned fixed-point is indeed valid. Finally, if the collection is small enough,
   we compare it to the symbolic result.
*/

use biodivine_lib_param_bn::biodivine_std::traits::Set;
use biodivine_lib_param_bn::fixed_points::FixedPoints;
use biodivine_lib_param_bn::solver_context::BnSolverContext;
use biodivine_lib_param_bn::symbolic_async_graph::SymbolicAsyncGraph;
use biodivine_lib_param_bn::BooleanNetwork;
use biodivine_lib_param_bn::Space;

fn main() {
    let args = std::env::args().collect::<Vec<_>>();

    let model = BooleanNetwork::try_from_file(args[1].as_str()).unwrap();
    let model = model.inline_inputs(true);
    println!(
        "Loaded model with {} variables and {} parameters/inputs.",
        model.num_vars(),
        model.num_parameters()
    );

    let z3 = z3::Context::new(&z3::Config::new());
    let ctx = BnSolverContext::new(&z3, model.clone());
    let stg = SymbolicAsyncGraph::new(model.clone()).unwrap();

    let all_vertices = vec![Space::new(&model)];
    let iterator = FixedPoints::solver_iterator(&ctx, &all_vertices, &[]);

    let mut count = 0;
    for model in iterator {
        count += 1;

        let symbolic = model.get_symbolic_model(stg.symbolic_context());
        let symbolic = FixedPoints::symbolic(&stg, &symbolic);

        assert!(!symbolic.is_empty());
        assert!(symbolic.is_singleton());

        println!("Validity check {}/??? passed.", count);
        if count >= 1000 {
            println!("Skip total set comparison. Too many vertices.");
        }
    }

    let mut all_symbolic = FixedPoints::symbolic(&stg, stg.unit_colored_vertices());

    // Restart the iterator.
    let iterator = FixedPoints::solver_iterator(&ctx, &all_vertices, &[]);

    let mut count_2 = 0;
    for model in iterator {
        count_2 += 1;
        let symbolic_model = model.get_symbolic_model(stg.symbolic_context());
        assert!(symbolic_model.is_subset(&all_symbolic));
        all_symbolic = all_symbolic.minus(&symbolic_model);
        println!("Exhaustiveness check {}/{} passed.", count_2, count);
    }

    assert!(all_symbolic.is_empty());

    println!("All checks have passed.");
}
