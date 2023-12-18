use crate::symbolic_async_graph::projected_iteration::OwnedRawSymbolicIterator;
use crate::symbolic_async_graph::SymbolicContext;
use biodivine_lib_bdd::{Bdd, BddVariable};

mod _impl_network_colored_spaces;
mod _impl_network_spaces;
mod _impl_symbolic_space_context;
mod _impl_trap_spaces;

/// This object is a special extension of [SymbolicContext] which (aside from states and functions)
/// allows representing network subspaces (see also [Space]).
///
/// The representation uses the "extra state variables" supported by [SymbolicContext]. For each
/// network variable `x`, [SymbolicSpaceContext] adds two extra symbolic variables which we
/// refer to as `x_T` and `x_F`. These then encode individual spaces such that `(1,0) = 1`,
/// `(0,1) = 0` and `(1,1) = *`. Value `(0,0)` is invalid in this encoding.
/// [SymbolicSpaceContext] should document how the `(0,0)` is treated by each method (i.e. if
/// the result discards invalid values, or if they need to be excluded later).
///
/// Note that the BDDs returned by [SymbolicSpaceContext] are not directly compatible with
/// [SymbolicAsyncGraph], because they use a different [SymbolicContext]. However, you can
/// create a [SymbolicAsyncGraph] that is compatible with the [SymbolicSpaceContext] by
/// using the [SymbolicContext] available in [SymbolicSpaceContext::inner_context]
/// (see also [SymbolicAsyncGraph::with_space_context]).
///
pub struct SymbolicSpaceContext {
    inner_ctx: SymbolicContext,
    dual_variables: Vec<(BddVariable, BddVariable)>,
}

/// A symbolic set consisting of network subspaces (see also [Space]).
///
/// This is in principle similar to [GraphVertices], but uses [SymbolicSpaceContext] for encoding.
#[derive(Clone, Eq, PartialEq, Hash, Debug)]
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
/// This is similar to [GraphColoredVertices], but uses [SymbolicSpaceContext] for encoding
/// of spaces. Colors/parameters are encoded the same way as in the normal [SymbolicContext].
#[derive(Clone, Eq, PartialEq, Hash, Debug)]
pub struct NetworkColoredSpaces {
    bdd: Bdd,
    dual_variables: Vec<(BddVariable, BddVariable)>,
    parameter_variables: Vec<BddVariable>,
}

/// A utility object similar to [FixedPoints] which facilitates trap space computation.
pub struct TrapSpaces {
    _dummy: (),
}
