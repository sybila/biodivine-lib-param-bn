//! *Legacy* semi-symbolic representation of the coloured asynchronous state-transition graph.
//!
//! It represents states explicitly (see `IdState`), but uses symbolic representation (`BddParams`)
//! for sets of parameters.
//!

use crate::bdd_params::{BddParameterEncoder, BddParams};
use crate::biodivine_std::structs::{IdState, IdStateRange};
use crate::biodivine_std::traits::{Graph, InvertibleGraph, Set};
use crate::{BooleanNetwork, VariableId, VariableIdIterator};

mod impl_async_graph;
mod impl_default_edge_params;
mod impl_evolution_operators;

/// An asynchronous transition system of a `BooleanNetwork`. The states of the graph
/// are standard `IdState`s. The parameter sets are given by the associated `AsyncGraphEdgeParams`.
///
/// Async graph implements the standard "asynchronous update", i.e. every variable can be
/// non-deterministically updated at any time, but the actual parameters for which this
/// happens are determined by the `AsyncGraphEdgeParams`.
///
/// This actually hides a lot of complexity, because implementing `AsyncGraphEdgeParams` is typically
/// much easier than re-implementing the whole async graph structure.
pub struct AsyncGraph<P: AsyncGraphEdgeParams> {
    edges: P,
}

/// Default implementation for edge parameters which adheres to the monotonicity and observability
/// constraints  of the network, but poses no other restrictions.
pub struct DefaultEdgeParams {
    network: BooleanNetwork,
    encoder: BddParameterEncoder,
    /// The parameter valuations which satisfy the static regulation constraints.
    unit_set: BddParams,
    empty_set: BddParams,
}

/// Async graph edges implement the edge colouring (parametrisation) of a graph. Instances of
/// this trait are used together with the `AsyncGraph` to produce a semantic coloured graph
/// of a parametrised Boolean network.
///
/// See `DefaultEdgeParams` for default implementation of edge colours.
///
/// This trait is especially useful when constructing things like wrappers of existing graphs,
/// which need to modify the behaviour of the graph. Another option are various custom
/// parameter encoders, where we simply do not want to re-implement the whole graph trait
/// front scratch.
pub trait AsyncGraphEdgeParams {
    type ParamSet: Set;
    // A reference to the underlying Boolean network.
    fn network(&self) -> &BooleanNetwork;
    /// Create a new empty set of parameters.
    fn empty_params(&self) -> &Self::ParamSet;
    /// Create a new full set of parameters.
    fn unit_params(&self) -> &Self::ParamSet;
    /// Create parameters for the edge starting in the given `state`,
    /// flipping the given `variable`.
    fn edge_params(&self, state: IdState, variable: VariableId) -> Self::ParamSet;
    /// Construct a witness network for the given set of parameters.
    ///
    /// TODO: It is not really essential in this trait. Think of a way to move it elsewhere.
    fn make_witness(&self, params: &Self::ParamSet) -> BooleanNetwork;
}

/// A forward `EvolutionOperator` of the `AsyncGraph`.
pub struct Fwd<'a, Edges: AsyncGraphEdgeParams> {
    graph: &'a AsyncGraph<Edges>,
}

/// A backward `EvolutionOperator` of the `AsyncGraph`.
pub struct Bwd<'a, Edges: AsyncGraphEdgeParams> {
    graph: &'a AsyncGraph<Edges>,
}

/// An iterator over successors of a state in the `AsyncGraph`.
pub struct FwdIterator<'a, Edges: AsyncGraphEdgeParams> {
    graph: &'a AsyncGraph<Edges>,
    state: IdState,
    variables: VariableIdIterator,
}

/// An iterator over predecessors of a state in the `AsyncGraph`.
pub struct BwdIterator<'a, Edges: AsyncGraphEdgeParams> {
    graph: &'a AsyncGraph<Edges>,
    state: IdState,
    variables: VariableIdIterator,
}

impl<'a, Edges: AsyncGraphEdgeParams> Graph for &'a AsyncGraph<Edges> {
    type State = IdState;
    type Params = Edges::ParamSet;
    type States = IdStateRange;
    type FwdEdges = Fwd<'a, Edges>;
    type BwdEdges = Bwd<'a, Edges>;

    fn states(&self) -> Self::States {
        IdStateRange::new(self.num_states())
    }

    fn fwd(&self) -> Self::FwdEdges {
        Fwd { graph: self }
    }

    fn bwd(&self) -> Self::BwdEdges {
        Bwd { graph: self }
    }
}

impl<'a, Edges: AsyncGraphEdgeParams> InvertibleGraph for &'a AsyncGraph<Edges> {
    type FwdEdges = Fwd<'a, Edges>;
    type BwdEdges = Bwd<'a, Edges>;
}
