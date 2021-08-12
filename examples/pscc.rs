use biodivine_lib_param_bn::decomposition::baseline_fwd_bwd;
use biodivine_lib_param_bn::symbolic_async_graph::SymbolicAsyncGraph;
use biodivine_lib_param_bn::BooleanNetwork;
use std::convert::TryFrom;
use std::io::Read;
use std::sync::atomic::{AtomicU32, Ordering};

fn main() {
    let mut buffer = String::new();
    std::io::stdin().read_to_string(&mut buffer).unwrap();

    let model = BooleanNetwork::try_from(buffer.as_str()).unwrap();
    println!("Model vars: {}", model.as_graph().num_vars());

    let graph = SymbolicAsyncGraph::new(model).unwrap();
    println!("Graph colors: {}", graph.unit_colors().approx_cardinality());
    baseline_fwd_bwd(&graph, |scc| {
        println!(
            "Found scc: {:?}; States: {:?}",
            scc.approx_cardinality(),
            scc.vertices().approx_cardinality()
        );
    });
}
