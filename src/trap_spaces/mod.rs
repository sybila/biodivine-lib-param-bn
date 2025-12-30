use crate::symbolic_async_graph::SymbolicContext;
use crate::symbolic_async_graph::projected_iteration::OwnedRawSymbolicIterator;
use biodivine_lib_bdd::{Bdd, BddVariable};

mod _impl_network_colored_spaces;
mod _impl_network_spaces;
mod _impl_symbolic_space_context;
mod _impl_trap_spaces;

/// This object is a special extension of [SymbolicContext] which (aside from states and functions)
/// allows representing network subspaces (see also [crate::Space]).
///
/// The representation uses the "extra state variables" supported by [SymbolicContext]. For each
/// network variable `x`, [SymbolicSpaceContext] adds two extra symbolic variables which we
/// refer to as `x_T` and `x_F`. These then encode individual spaces such that `(1,0) = 1`,
/// `(0,1) = 0` and `(1,1) = *`. Value `(0,0)` is invalid in this encoding.
/// [SymbolicSpaceContext] should document how the `(0,0)` is treated by each method (i.e. if
/// the result discards invalid values, or if they need to be excluded later).
///
/// Note that the BDDs returned by [SymbolicSpaceContext] are not directly compatible with
/// [crate::symbolic_async_graph::SymbolicAsyncGraph], because they use a different [SymbolicContext]. However, you can
/// create a [crate::symbolic_async_graph::SymbolicAsyncGraph] that is compatible with the [SymbolicSpaceContext] by
/// using the [SymbolicContext] available in [SymbolicSpaceContext::inner_context]
/// (see also [crate::symbolic_async_graph::SymbolicAsyncGraph::with_space_context]).
///
#[derive(Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct SymbolicSpaceContext {
    inner_ctx: SymbolicContext,
    dual_variables: Vec<(BddVariable, BddVariable)>,
    space_to_vertex_bdd: Bdd,
    vertex_to_space_bdd: Bdd,
}

/// A symbolic set consisting of network subspaces (see also [crate::Space]).
///
/// This is in principle similar to [crate::symbolic_async_graph::GraphVertices], but uses [SymbolicSpaceContext] for encoding.
#[derive(Clone, Eq, PartialEq, Hash, Debug)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct NetworkSpaces {
    bdd: Bdd,
    dual_variables: Vec<(BddVariable, BddVariable)>,
}

/// An iterator which goes through the elements of a [NetworkSpaces] set.
pub struct SpaceIterator {
    inner_iterator: OwnedRawSymbolicIterator,
    dual_variables: Vec<(BddVariable, BddVariable)>,
}

/// A symbolic relation consisting of network subspaces and parameter colors (valuations).
///
/// This is similar to [crate::symbolic_async_graph::GraphColoredVertices], but uses [SymbolicSpaceContext] for encoding
/// of spaces. Colors/parameters are encoded the same way as in the normal [SymbolicContext].
#[derive(Clone, Eq, PartialEq, Hash, Debug)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct NetworkColoredSpaces {
    bdd: Bdd,
    dual_variables: Vec<(BddVariable, BddVariable)>,
    parameter_variables: Vec<BddVariable>,
}

/// A utility object similar to [crate::fixed_points::FixedPoints] which facilitates trap space computation.
pub struct TrapSpaces {
    _dummy: (),
}
