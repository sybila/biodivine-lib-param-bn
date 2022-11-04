use biodivine_lib_param_bn::fixed_points::solver_iterator::SolverIterator;
use biodivine_lib_param_bn::fixed_points::FixedPoints;
use biodivine_lib_param_bn::solver_context::BnSolverContext;
use biodivine_lib_param_bn::symbolic_async_graph::SymbolicAsyncGraph;
use biodivine_lib_param_bn::{BooleanNetwork, VariableId};
use biodivine_lib_param_bn::biodivine_std::bitvector::BitVector;

fn main() {
    let args = Vec::from_iter(std::env::args());
    let path = &args[1];
    let model = BooleanNetwork::try_from_file(path).unwrap();
    //let model = model.inline_inputs();

    println!(
        "Loaded model with {} variables and {} parameters.",
        model.num_vars(),
        model.num_parameters()
    );

    let z3 = z3::Context::new(&z3::Config::new());
    //build_z3_query(&z3, &model);

    let ctx = BnSolverContext::new(&z3, model.clone());

    let iterator = SolverIterator::new(&ctx);

    println!("{:?}", model.variables()
        .map(|it| model.get_variable_name(it)).collect::<Vec<_>>());

    let mut i = 0;
    //println!("Count: {}", iterator.take(10).count());
    for model in iterator {
        println!("Model: {}", model.as_z3_model().);
        println!("{:?}", model.get_state());
        i += 1;
        if i > 10 {
           panic!("Too many fixed-points.");
        }
    }
    //let i = iterator.take(100).count();

    println!("Count: {}", i);

    let stg = SymbolicAsyncGraph::new(model.clone()).unwrap();
    let fixed_points = FixedPoints::symbolic(&stg, stg.unit_colored_vertices());

    println!("Actual fixed points: {}", fixed_points.approx_cardinality());
    /*for vertex in fixed_points.vertices().materialize().iter() {
        println!("{:?}", vertex.values());
    }*/

}
