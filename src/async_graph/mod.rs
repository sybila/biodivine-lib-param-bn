use crate::bdd_params::{BddParameterEncoder, BddParams};
use crate::{BooleanNetwork, VariableIdIterator};
use biodivine_lib_std::param_graph::Graph;
use biodivine_lib_std::{IdState, IdStateRange};

mod impl_async_graph;
mod impl_evolution_operators;

/// An asynchronous transition system of a `BooleanNetwork`. The states of the graph
/// are standard `IdState`s. The parameter sets of the graph are the `BddParams`.
pub struct AsyncGraph {
    network: BooleanNetwork,
    encoder: BddParameterEncoder,
    /// The parameter valuations which satisfy the static regulation constraints.
    unit_set: BddParams,
}

/// A forward `EvolutionOperator` of the `AsyncGraph`.
pub struct Fwd<'a> {
    graph: &'a AsyncGraph,
}

/// A backward `EvolutionOperator` of the `AsyncGraph`.
pub struct Bwd<'a> {
    graph: &'a AsyncGraph,
}

/// An iterator over successors of a state in the `AsyncGraph`.
pub struct FwdIterator<'a> {
    graph: &'a AsyncGraph,
    state: IdState,
    variables: VariableIdIterator,
}

/// An iterator over predecessors of a state in the `AsyncGraph`.
pub struct BwdIterator<'a> {
    graph: &'a AsyncGraph,
    state: IdState,
    variables: VariableIdIterator,
}

impl<'a> Graph for &'a AsyncGraph {
    type State = IdState;
    type Params = BddParams;
    type States = IdStateRange;
    type FwdEdges = Fwd<'a>;
    type BwdEdges = Bwd<'a>;

    fn states(&self) -> Self::States {
        return IdStateRange::new(self.num_states());
    }

    fn fwd(&self) -> Self::FwdEdges {
        return Fwd { graph: self };
    }

    fn bwd(&self) -> Self::BwdEdges {
        return Bwd { graph: self };
    }
}
