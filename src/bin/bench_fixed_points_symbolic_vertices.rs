use biodivine_lib_param_bn::BooleanNetwork;
use biodivine_lib_param_bn::fixed_points::FixedPoints;
use biodivine_lib_param_bn::symbolic_async_graph::SymbolicAsyncGraph;

fn main() {
    let args = Vec::from_iter(std::env::args());
    let path = &args[1];
    let model = BooleanNetwork::try_from_file(path).unwrap();
    let model = model.inline_inputs(true, true);

    println!(
        "Loaded model with {} variables and {} parameters.",
        model.num_vars(),
        model.num_parameters()
    );

    let stg = SymbolicAsyncGraph::new(&model).unwrap();

    let fixed_points = FixedPoints::symbolic_vertices(&stg, stg.unit_colored_vertices());
    println!(
        "Fixed-point vertices: {}[nodes:{}]",
        fixed_points.approx_cardinality(),
        fixed_points.symbolic_size()
    );
}
