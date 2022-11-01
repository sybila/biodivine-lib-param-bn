use biodivine_lib_param_bn::{BooleanNetwork, SdGraph, VariableId};
use std::collections::HashSet;

fn main() {
    let args = std::env::args().collect::<Vec<_>>();
    let model = BooleanNetwork::try_from_file(args[1].as_str()).unwrap();

    // First, compute the feedback vertex set.
    let ic = model.as_graph().independent_cycles();
    println!("IC size: {}", ic.len());

    // Check that the cycles are pair-wise disjoint.
    let ic_hashed: Vec<HashSet<VariableId>> =
        ic.iter().map(|it| it.iter().cloned().collect()).collect();
    for i in 0..ic.len() {
        for j in (i + 1)..ic.len() {
            let a = &ic_hashed[i];
            let b = &ic_hashed[j];
            assert!(a.intersection(b).next().is_none());
        }
    }

    // Check that the rest of the graph is acyclic.
    let graph = SdGraph::from(model.as_graph());
    let mut restriction = graph.mk_all_vertices();
    for x in &ic {
        for y in x {
            restriction.remove(y);
        }
    }
    assert!(graph
        .restricted_strongly_connected_components(&restriction)
        .is_empty());
}
