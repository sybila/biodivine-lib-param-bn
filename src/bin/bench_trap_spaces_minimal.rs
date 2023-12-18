use biodivine_lib_param_bn::symbolic_async_graph::SymbolicAsyncGraph;
use biodivine_lib_param_bn::trap_spaces::{SymbolicSpaceContext, TrapSpaces};
use biodivine_lib_param_bn::BooleanNetwork;

fn main() {
    let args = std::env::args().collect::<Vec<_>>();
    let bn = BooleanNetwork::try_from_file(args[1].as_str()).unwrap();
    let ctx = SymbolicSpaceContext::new(&bn);
    let stg = SymbolicAsyncGraph::with_space_context(&bn, &ctx).unwrap();

    let unit_set = ctx.mk_unit_colored_spaces(&stg);
    let essential_traps = TrapSpaces::essential_symbolic(&bn, &ctx, &unit_set);
    println!(
        "Found {} essential trap(s).",
        essential_traps.approx_cardinality()
    );

    let minimal_traps = TrapSpaces::minimize(&ctx, &essential_traps);
    println!(
        "Found {}/{}({}) minimal trap(s).",
        minimal_traps.spaces().approx_cardinality(),
        minimal_traps.colors().approx_cardinality(),
        minimal_traps.approx_cardinality()
    );
}
