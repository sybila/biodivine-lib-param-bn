use crate::symbolic_async_graph::{SymbolicAsyncGraph, GraphColoredVertices};
use crate::biodivine_std::traits::Set;

pub fn coloured_scc<F>(graph: &SymbolicAsyncGraph, callback: F) where F: Fn(GraphColoredVertices) -> () {
    let mut universe = graph.mk_unit_colored_vertices();

    while !universe.is_empty() {
        let pivot = universe.pick_vertex();
        println!("Picked pivot: {}", pivot.approx_cardinality());
    }
}