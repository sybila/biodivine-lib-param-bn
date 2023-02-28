use biodivine_lib_param_bn::biodivine_std::traits::Set;
use biodivine_lib_param_bn::symbolic_async_graph::reachability::Reachability;
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

    let mut count = 0;
    let mut universe = stg.mk_unit_colored_vertices();
    while !universe.is_empty() {
        let reduced_stg = stg.restrict(&universe);
        let mut component = universe.pick_vertex();
        loop {
            let update = Reachability::reach_bwd_basic(&reduced_stg, &component);
            let update = Reachability::reach_fwd_basic(&reduced_stg, &update);
            if update.is_subset(&component) {
                break;
            } else {
                component = update;
            }
        }
        println!("Found weak component: {}", component.approx_cardinality());
        universe = universe.minus(&component);
        count += 1;
    }
    println!("Total {count} components.")
}
