use biodivine_lib_param_bn::fixed_points::FixedPoints2;
use biodivine_lib_param_bn::symbolic_async_graph::SymbolicAsyncGraph;
use biodivine_lib_param_bn::BooleanNetwork;

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

    let stg = SymbolicAsyncGraph::new(model).unwrap();

    let iterator = biodivine_lib_param_bn::fixed_points::SymbolicIterator::new(
        &stg,
        stg.unit_colored_vertices(),
        100_000
    );

    for set in iterator {
        println!(
            "Fixed-point vertices: {}[nodes:{}]",
            fixed_points.approx_cardinality(),
            fixed_points.symbolic_size()
        );
    }
}
