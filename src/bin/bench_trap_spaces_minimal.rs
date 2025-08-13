use biodivine_lib_param_bn::BooleanNetwork;
use biodivine_lib_param_bn::symbolic_async_graph::SymbolicAsyncGraph;
use biodivine_lib_param_bn::trap_spaces::{SymbolicSpaceContext, TrapSpaces};

fn main() {
    let args = std::env::args().collect::<Vec<_>>();
    let bn = BooleanNetwork::try_from_file(args[1].as_str()).unwrap();
    let ctx = SymbolicSpaceContext::new(&bn);
    let stg = SymbolicAsyncGraph::with_space_context(&bn, &ctx).unwrap();

    let unit_set = ctx.mk_unit_colored_spaces(&stg);
    let minimal_traps = TrapSpaces::minimal_symbolic(&ctx, &stg, &unit_set, false);
    println!(
        "Found {}/{}({}) minimal trap(s).",
        minimal_traps.spaces().approx_cardinality(),
        minimal_traps.colors().approx_cardinality(),
        minimal_traps.approx_cardinality()
    );
}
