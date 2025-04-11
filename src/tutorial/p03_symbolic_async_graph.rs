//! # Symbolic Asynchronous Graph
//!
//! When we talk about the behaviour of a Boolean network, we typically refer to a specific
//! state-transition graph which that network generates. In this library, we consider the
//! *asynchronous* variant of such graph. The vertices of the graph are all possible combinations
//! of Boolean valuations of the network variables (i.e. $\\{0,1\\}^n$). The edges then represent
//! non-deterministic applications of the update functions, such that each edge changes exactly
//! one variable. If the network is parametrised, each edge is also assigned a set of colors, which
//! contains every parametrisation for which the edge is enabled. This structure is managed by
//! a `SymbolicAsyncGraph`.
//!
//! To represent this type of graph, we use Binary Decision Diagrams (BDDs) implemented in our
//! [`lib-bdd`](https://github.com/sybila/biodivine-lib-bdd). Using these, we can often work with
//! large sets ($2^{1000}$ elements and beyond) concisely. However, in the worst case, this
//! representation is still linear in the size of the set, and we thus cannot guarantee that it
//! works well for every model.
//!
//! Using BDDs, we implement three important symbolic set types: `GraphVertices`, `GraphColors`,
//! and `GraphColoredVertices` (set of pairs `(vertex, color)`). These cannot be created
//! directly, because they depend on the structure of the graph, but can be obtained from the
//! `SymbolicAsyncGraph`. Once you have such a set, you can perform common set operations
//! like `union`, `intersection`, `subset` test and more. For `GraphColoredVertices`, you can
//! also project to just the vertex or color portion of the set.
//!
//! ```rust
//! use biodivine_lib_param_bn::BooleanNetwork;
//! use std::convert::TryFrom;
//! use biodivine_lib_param_bn::symbolic_async_graph::{SymbolicAsyncGraph, GraphColoredVertices};
//! use biodivine_lib_param_bn::biodivine_std::traits::Set;
//! use biodivine_lib_param_bn::biodivine_std::bitvector::{ArrayBitVector, BitVector};
//!
//! // Boolean network from the previous tutorial:
//! let bn = BooleanNetwork::try_from(r"
//!     A -> B
//!     C -|? B
//!     ## Update function of variable B:
//!     $B: A
//!     C -> A
//!     B -> A
//!     A -| A
//!     $A: C | f(A, B)
//! ").unwrap();
//!
//! // At this point, the implementation checks if there is at least one parametrisation which
//! // satisfies all the requirements imposed by the RegulatoryGraph. If no such parametrisation
//! // exists, an error is returned, typically also with an explanation why.
//! let stg = SymbolicAsyncGraph::new(&bn)?;
//!
//! // Once we have a `SymbolicAsyncGraph`, we can access the `GraphVertices`, `GraphColors`
//! // and `GraphColoredVertices`. Basic methods return a reference, `mk_*` methods create
//! // a new owned object.
//! assert_eq!(32.0, stg.unit_colored_vertices().approx_cardinality());
//! assert_eq!(8.0, stg.unit_colored_vertices().vertices().approx_cardinality());
//! assert_eq!(4.0, stg.unit_colored_vertices().colors().approx_cardinality());
//! assert!(stg.empty_colored_vertices().is_empty());
//! assert!(stg.mk_empty_colors().is_empty());
//! assert_eq!(stg.mk_unit_colors(), stg.unit_colored_vertices().colors());
//! // WARNING: Remember that floating point numbers may not be exact for larger values.
//! // In fact, for some very large models, the set size can be simply approximated to infinity.
//!
//! // You can still access the underlying network of the graph:
//! assert_eq!(3, stg.as_network().unwrap().num_vars());
//! // Just note that in some advanced instances, the network may not exist, in which case
//! // `as_network` returns `None`
//!
//! // You can also obtain a set where all vertices have a Boolean variable set
//! // to the given value:
//! let id_a = bn.as_graph().find_variable("A").unwrap();
//! let a_is_true: GraphColoredVertices = stg.fix_network_variable(id_a, true);
//! // This can be used to (for example) construct a set of initial states specified by the user.
//!
//! // Finally, by providing a set of colors, you can let the async graph pick a "witness", i.e.
//! // one of the fully specified networks which are admissible for the given set of colors.
//! let witness = stg.pick_witness(stg.unit_colors());
//! assert_eq!(0, witness.parameters().count());
//!
//! // `GraphVertices` can be also iterated. But keep in mind the materialized set can be
//! // enormous, so always check if the operation is feasible,
//! // for example by inspecting the `approx_cardinality`.
//! for vertex in stg.unit_colored_vertices().vertices().materialize().iter() {
//!     println!("Value of A in state {:?} is {}", vertex, vertex.get(id_a.into()));
//!     // You can also turn the vertex back into a singleton set (with all colors):
//!     let singleton = stg.vertex(&vertex);
//!     assert_eq!(4.0, singleton.approx_cardinality());
//!     assert_eq!(1.0, singleton.vertices().approx_cardinality());
//! }
//!
//! // At the moment, `GraphColors` cannot be iterated as we don't have a public
//! // representation of a single parametrisation. However, this is something that
//! // should be available in the future.
//!
//! // You can pick a singleton subset though:
//! let one_color = stg.unit_colors().pick_singleton();
//! assert_eq!(1.0, one_color.approx_cardinality());
//!
//! // For `GraphColoredVertices`, you can also pick a singleton, as well as pick one
//! // color for each vertex or one vertex for each color in the set.
//!
//! // For each color (4 colors), pick one vertex from the set:
//! assert_eq!(4.0, stg.unit_colored_vertices().pick_vertex().approx_cardinality());
//! // For each vertex (8 vertices), pick one color from the set:
//! assert_eq!(8.0, stg.unit_colored_vertices().pick_color().approx_cardinality());
//! // Note that result of this operation is still a set of (vertex, color) pairs.
//!
//! # Ok::<(), String>(())
//! ```
//!
//! ## Working With Graph Transitions
//!
//! To explore the edges of the graph symbolically, you can use the `pre`, `post`, `var_pre` and
//! `var_post` methods. These take a `ColoredVertexSet` $A$ and return a new `ColoredVertexSet` $B$,
//! which contains exactly the one-step predecessors (or successors) of the vertices in $A$ with
//! their respective colors, for which they can be reached. The `var_*` methods do this only for
//! one update function, while `post` and `pre` consider all update functions simultaneously
//! (which is more computationally demanding).
//!
//! Furthermore, if you only need to test which vertices *can* perform a transition, you can use
//! these methods with a `can_*` prefix, in which case the desired subset of $A$ will be returned.
//!
//! ```rust
//! # use biodivine_lib_param_bn::BooleanNetwork;
//! # use std::convert::TryFrom;
//! # use biodivine_lib_param_bn::symbolic_async_graph::{SymbolicAsyncGraph, GraphColoredVertices};
//! # use biodivine_lib_param_bn::biodivine_std::traits::Set;
//! # use biodivine_lib_param_bn::biodivine_std::bitvector::{ArrayBitVector, BitVector};
//! # // Boolean network from the previous tutorial:
//! # let bn = BooleanNetwork::try_from(r"
//! #     A -> B
//! #     C -|? B
//! #     $B: A
//! #     C -> A
//! #     B -> A
//! #     A -| A
//! #     $A: C | f(A, B)
//! # ").unwrap();
//! # let stg = SymbolicAsyncGraph::new(&bn)?;
//! let id_b = bn.as_graph().find_variable("B").unwrap();
//! let b_is_true = stg.fix_network_variable(id_b, true);
//! let b_is_false = stg.fix_network_variable(id_b, false);
//!
//! // Jumping from A=0 to A=1: Vertices that have predecessor with
//! // respect to this jump are the ones into which we are jumping, and vice versa:
//! assert_eq!(stg.var_can_pre(id_b, &b_is_true), stg.var_post(id_b, &b_is_false));
//! assert_eq!(stg.var_can_post(id_b, &b_is_false), stg.var_pre(id_b, &b_is_true));
//!
//! // All states with A=1 have some predecessor (for some color):
//! assert_eq!(4.0, stg.can_pre(&b_is_true).vertices().approx_cardinality());
//! // Also all states with A=0 have some successor (for some color):
//! assert_eq!(4.0, stg.can_post(&b_is_false).vertices().approx_cardinality());
//!
//! // However, after we fix a specific color, only three of the four states with B=1 have
//! // a predecessor.
//! let some_color = stg.unit_colors().pick_singleton();
//! let b_is_true_with_color = b_is_true.intersect_colors(&some_color);
//! let b_is_false_with_color = b_is_false.intersect_colors(&some_color);
//! assert_eq!(3.0, stg.can_pre(&b_is_true_with_color).vertices().approx_cardinality());
//! assert_eq!(4.0, stg.can_post(&b_is_false_with_color).vertices().approx_cardinality());
//!
//! // Note that this does not (always) hold for pre/post, since now we are using all transitions,
//! // not just the B-transition:
//! assert_ne!(stg.can_pre(&b_is_true), stg.post(&b_is_false));
//! assert_ne!(stg.can_post(&b_is_false), stg.pre(&b_is_true));
//! # Ok::<(), String>(())
//! ```
//!
//! Using these building blocks, you can construct powerful symbolic algorithms that analyse
//! the behaviour of Boolean networks. A simple example of such an algorithm is given in the
//! next tutorial.
//!
//! If there are some operations that are not provided, you can sometimes prototype them using
//! raw `Bdd` objects. These can be obtained from every set using `as_bdd` or `into_bdd` methods
//! (conversion back to a set is possible using a `copy(Bdd)` method which uses the `self` object
//! to provide the appropriate context for the set). Also, you can have a look at `SymbolicContext`
//! and `FunctionTable`, which are part of the `SymbolicAsyncGraph`, if you need some more
//! advanced operations for mapping colors to the parametrisation of the `BooleanNetwork`.
//! However, these require expert knowledge of the topic and are not covered
//! by this tutorial.
//!
