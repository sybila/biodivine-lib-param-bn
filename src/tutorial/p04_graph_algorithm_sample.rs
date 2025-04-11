//! # SCC Detection Algorithm
//!
//! Finally, let us examine a very basic algorithm built using this library:
//! symbolic detection of SCC components.
//!
//! First, we need to define simple forward/backward reachability procedures:
//!
//! ```rust
//! use biodivine_lib_param_bn::symbolic_async_graph::{GraphColoredVertices, SymbolicAsyncGraph};
//! use biodivine_lib_param_bn::biodivine_std::traits::Set;
//!
//! fn fwd(graph: &SymbolicAsyncGraph, initial: &GraphColoredVertices) -> GraphColoredVertices {
//!     let mut result = initial.clone();
//!     loop {
//!         let post = graph.post(&result);
//!         if post.is_subset(&result) {
//!             return result;
//!         } else {
//!             result = result.union(&post);
//!         }
//!     }
//! }
//!
//! fn bwd(graph: &SymbolicAsyncGraph, initial: &GraphColoredVertices) -> GraphColoredVertices {
//!     let mut result = initial.clone();
//!     loop {
//!         let post = graph.pre(&result);
//!         if post.is_subset(&result) {
//!             return result;
//!         } else {
//!             result = result.union(&post);
//!         }
//!     }
//! }
//! ```
//!
//! Note that in practice, it would be much better to use something like *saturation*, where
//! the transitions which are applied are selected greedily one at a time, instead of applying
//! them all at once using full `post` or `pre`. However, for the purpose of this tutorial, this
//! should be sufficient.
//!
//! Now we can observe that an SCC of vertex `v` is always the intersection of forward and backward
//! reachable vertices from `v`. Hence, we can write the following simple algorithm:
//!
//! ```rust
//! # use biodivine_lib_param_bn::symbolic_async_graph::{SymbolicAsyncGraph, GraphColoredVertices};
//! # use biodivine_lib_param_bn::BooleanNetwork;
//! # use std::convert::TryFrom;
//! # use biodivine_lib_param_bn::biodivine_std::traits::Set;
//! # fn fwd(graph: &SymbolicAsyncGraph, initial: &GraphColoredVertices) -> GraphColoredVertices {
//! #     let mut result = initial.clone();
//! #     loop {
//! #         let post = graph.post(&result);
//! #         if post.is_subset(&result) {
//! #             return result;
//! #         } else {
//! #             result = result.union(&post);
//! #         }
//! #     }
//! # }
//!
//! # fn bwd(graph: &SymbolicAsyncGraph, initial: &GraphColoredVertices) -> GraphColoredVertices {
//! #     let mut result = initial.clone();
//! #     loop {
//! #         let post = graph.pre(&result);
//! #         if post.is_subset(&result) {
//! #             return result;
//! #         } else {
//! #             result = result.union(&post);
//! #         }
//! #     }
//! # }
//! fn scc(graph: &SymbolicAsyncGraph) -> Vec<GraphColoredVertices> {
//!     let mut universe = graph.mk_unit_colored_vertices();
//!     let mut components = Vec::new();
//!     while !universe.is_empty() {
//!         // Pick one vertex in universe for every color in universe
//!         let pivots = universe.pick_vertex();
//!         let fwd = fwd(graph, &pivots);
//!         let bwd = bwd(graph, &pivots);
//!         let scc = fwd.intersect(&bwd);
//!         universe = universe.minus(&scc);
//!         components.push(scc);
//!     }
//!     components
//! }
//! // Boolean network from the previous tutorial:
//! let bn = BooleanNetwork::try_from(r"
//!     A -> B
//!     C -|? B
//!     $B: A
//!     C -> A
//!     B -> A
//!     A -| A
//!     $A: C | f(A, B)
//! ").unwrap();
//! let stg = SymbolicAsyncGraph::new(&bn).unwrap();
//!
//! // Note that since the symbolic graph contains different transitions for different colors,
//! // this will create SCCs that overlap for some colors but are completely different for others.
//! // Hence, the same vertex can appear in multiple SCCs for different colors.
//! let components = scc(&stg);
//! assert_eq!(7, components.len());
//! assert_eq!(2.0, components[0].vertices().approx_cardinality());
//! assert_eq!(1.0, components[1].vertices().approx_cardinality());
//! assert_eq!(2.0, components[2].vertices().approx_cardinality());
//! assert_eq!(1.0, components[3].vertices().approx_cardinality());
//! assert_eq!(2.0, components[4].vertices().approx_cardinality());
//! assert_eq!(2.0, components[5].vertices().approx_cardinality());
//! assert_eq!(1.0, components[6].vertices().approx_cardinality());
//! ```
//!
//!
