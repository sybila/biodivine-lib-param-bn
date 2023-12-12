use biodivine_lib_param_bn::symbolic_async_graph::SymbolicAsyncGraph;
use biodivine_lib_param_bn::BooleanNetwork;
use std::cmp::min;
use std::sync::Arc;

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

    let stg = SymbolicAsyncGraph::new(model).unwrap();
    let stg = Arc::new(stg);

    let dimensions = usize::from(stg.symbolic_context().bdd_variable_set().num_vars());

    let mut iterator = biodivine_lib_param_bn::fixed_points::SymbolicIterator::new(
        stg.as_ref(),
        stg.unit_colored_vertices(),
        10 * dimensions,
    );

    // Ideally, you'd set this number much higher, but we are trying to test how long it takes
    // to enumerate with this type of scaling.
    let max_limit = 100_000 * dimensions;
    println!(
        "Initial limit {}. Max limit: {}",
        10 * dimensions,
        max_limit
    );

    while let Some(set) = iterator.next() {
        println!(
            "Fixed-point vertices: {}[nodes:{}]",
            set.approx_cardinality(),
            set.symbolic_size()
        );
        let current = iterator.get_limit();
        if set.symbolic_size() > current {
            let new_limit = min(max_limit, 2 * current);
            println!("Bump limit to {}", new_limit);
            iterator.set_limit(new_limit);
        } else {
            println!("Keep old limit {}.", current);
        }
    }
}
