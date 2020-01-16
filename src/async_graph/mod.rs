use crate::{BooleanNetwork, VariableIdIterator};
use crate::bdd_params::{BddParameterEncoder, BddParams};
use crate::biodivine_std::IdState;

mod impl_evolution_operators;
mod impl_async_graph;
mod impl_static_constraints;

/// An asynchronous transition system of a `BooleanNetwork`. The states of the graph
/// are standard `IdState`s. The parameter sets of the graph are the `BddParams`.
pub struct AsyncGraph {
    network: BooleanNetwork,
    encoder: BddParameterEncoder,
    /// The parameter valuations which satisfy the static regulation constraints.
    unit_set: BddParams
}

/// A forward `EvolutionOperator` of the `AsyncGraph`.
pub struct Fwd<'a> {
    graph: &'a AsyncGraph
}

/// A backward `EvolutionOperator` of the `AsyncGraph`.
pub struct Bwd<'a> {
    graph: &'a AsyncGraph
}

/// An iterator over successors of a state in the `AsyncGraph`.
pub struct FwdIterator<'a> {
    graph: &'a AsyncGraph,
    state: IdState,
    variables: VariableIdIterator
}

/// An iterator over predecessors of a state in the `AsyncGraph`.
pub struct BwdIterator<'a> {
    graph: &'a AsyncGraph,
    state: IdState,
    variables: VariableIdIterator
}

