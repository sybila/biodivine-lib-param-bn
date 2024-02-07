/*
   This is a very simple binary intended as an integration test or benchmark for the FVS
   approximation algorithm. We can run this on the BBM dataset to see if the algorithm is
   responsive and that it produces expected results. It is not included in normal tests
   because it needs to be compiled with optimizations, and generally we don't really want to
   run it every time we test (also, measuring the performance would be harder if this were
   a test).
*/

use biodivine_lib_param_bn::{BooleanNetwork, SdGraph};
use std::time::Instant;

fn main() {
    let args = std::env::args().collect::<Vec<_>>();
    let model = BooleanNetwork::try_from_file(args[1].as_str()).unwrap();
    let model = model.infer_valid_graph().unwrap();

    // First, compute the feedback vertex set.
    let start = Instant::now();
    let fvs = model.as_graph().feedback_vertex_set();
    let elapsed = Instant::now() - start;
    println!("FVS size: {}", fvs.len());

    // Then compute the SCC decomposition without the FVS. The result should be empty
    // since the graph should be acyclic.
    let graph = SdGraph::from(model.as_graph());
    let mut restriction = graph.mk_all_vertices();
    for x in &fvs {
        restriction.remove(x);
    }
    assert!(graph
        .restricted_strongly_connected_components(&restriction)
        .is_empty());
    println!("{}, {}", fvs.len(), elapsed.as_millis());
}
