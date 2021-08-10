use biodivine_lib_param_bn::biodivine_std::traits::Set;
use biodivine_lib_param_bn::decomposition::{coloured_scc, stepped_coloured_scc};
use biodivine_lib_param_bn::symbolic_async_graph::SymbolicAsyncGraph;
use biodivine_lib_param_bn::BooleanNetwork;
use std::convert::TryFrom;
use std::io::Read;
use std::sync::atomic::{AtomicU32, Ordering};

fn main() {
    let mut buffer = String::new();
    std::io::stdin().read_to_string(&mut buffer).unwrap();

    let model = BooleanNetwork::try_from(buffer.as_str()).unwrap();
    println!("Model: {}", model);
    println!("Model vars: {}", model.as_graph().num_vars());

    let graph = SymbolicAsyncGraph::new(model).unwrap();
    stepped_coloured_scc(&graph, |scc| {
        println!(
            "Found scc: {:?}; States: {:?}",
            scc.approx_cardinality(),
            scc.vertices().approx_cardinality()
        );
    });
}
