use crate::_impl_regulatory_graph::signed_directed_graph::Sign::{Negative, Positive};
use crate::{RegulatoryGraph, VariableId};
use std::collections::HashSet;
use std::ops::Add;

/// **(internal)** Basic utility methods for manipulating the `SdGraph`.
mod _impl_sd_graph;

/// **(internal)** Compute basic reachability properties within the `SdGraph`.
mod _reachability;

/// **(internal)** Perform a decomposition of the signed directed graph (or its subgraph)
/// into strongly connected components.
mod _strongly_connected_components;

/// **(internal)** Perform decomposition of the signed directed graph (or its subgraph)
/// into weakly connected components.
mod _weakly_connected_components;

/// **(internal)** Algorithms for detecting smallest cycles, including positive/negative
/// variants for each algorithms.
mod _cycle_detection;

/// **(internal)** Algorithm for computing an approximation of the minimum feedback vertex set.
mod _feedback_vertex_set;

/// **(internal)** Algorithm for computing an approximation of the maximum independent cycles set.
mod _independent_cycles;

/// A sign enum that describes the monotonicity of edges.
///
/// TODO: If we rewrite the API at some point, this should merge with `Monotonicity`.
#[derive(Copy, Clone, Eq, PartialEq, Hash, Debug)]
pub enum Sign {
    Positive,
    Negative,
}

/// A more efficient representation of a signed directed graph that can be used for studying
/// the properties of a `RegulatoryGraph`.
///
/// TODO: If we rewrite the API at some point, this should just merge with a `RegulatoryGraph`.
#[derive(Clone, Debug)]
pub struct SdGraph {
    successors: Vec<Vec<(VariableId, Sign)>>,
    predecessors: Vec<Vec<(VariableId, Sign)>>,
}

impl Add for Sign {
    type Output = Sign;

    fn add(self, rhs: Self) -> Self::Output {
        match (self, rhs) {
            (Positive, Positive) => Positive,
            (Negative, Negative) => Positive,
            (Positive, Negative) => Negative,
            (Negative, Positive) => Negative,
        }
    }
}

/// Algorithms for analysing the underlying signed directed graph.
impl RegulatoryGraph {
    /// Compute all *non-trivial* strongly connected components of the regulatory graph.
    ///
    /// The result is sorted by component size.
    pub fn strongly_connected_components(&self) -> Vec<HashSet<VariableId>> {
        SdGraph::from(self).strongly_connected_components()
    }

    /// Compute all *non-trivial* strongly connected components restricted within the given set
    /// of vertices.
    ///
    /// The result is sorted by component size.
    pub fn restricted_strongly_connected_components(
        &self,
        restriction: &HashSet<VariableId>,
    ) -> Vec<HashSet<VariableId>> {
        SdGraph::from(self).restricted_strongly_connected_components(restriction)
    }

    /// Compute all variables that transitively regulate the given `target` variable.
    pub fn transitive_regulators(&self, target: VariableId) -> HashSet<VariableId> {
        SdGraph::from(self).backward_reachable(HashSet::from([target]))
    }

    /// Compute all variables that are transitively regulated by the given `regulator` variable.
    pub fn transitive_targets(&self, regulator: VariableId) -> HashSet<VariableId> {
        SdGraph::from(self).forward_reachable(HashSet::from([regulator]))
    }

    /// Compute the shortest cycle that contains the given `pivot` vertex, or `None` if there
    /// is no such cycle.
    pub fn shortest_cycle(&self, pivot: VariableId) -> Option<Vec<VariableId>> {
        let graph = SdGraph::from(self);
        graph.shortest_cycle(&graph.mk_all_vertices(), pivot, usize::MAX)
    }

    /// Compute the shortest simple cycle that contains the given `pivot` vertex and has the
    /// specified `target_parity`.
    pub fn shortest_parity_cycle(
        &self,
        pivot: VariableId,
        target_parity: Sign,
    ) -> Option<Vec<VariableId>> {
        let graph = SdGraph::from(self);
        graph.shortest_parity_cycle(&graph.mk_all_vertices(), pivot, target_parity, usize::MAX)
    }

    /// Compute the set of variables that, if removed, cause this `RegulatoryGraph` to become
    /// acyclic.
    ///
    /// The method tries to obtain a minimal such set, but the minimality is not guaranteed.
    pub fn feedback_vertex_set(&self) -> HashSet<VariableId> {
        let graph = SdGraph::from(self);
        graph.restricted_feedback_vertex_set(&graph.mk_all_vertices())
    }

    /// Compute the set of variables that, if removed, causes this `RegulatoryGraph` to lose
    /// all cycles of the specified parity.
    ///
    /// The method tries to obtain a minimal such set, but the minimality is not guaranteed.
    pub fn parity_feedback_vertex_set(&self, parity: Sign) -> HashSet<VariableId> {
        let graph = SdGraph::from(self);
        graph.restricted_parity_feedback_vertex_set(&graph.mk_all_vertices(), parity)
    }

    /// Compute a collection of independent cycles of this `RegulatoryGraph`. That is, disjoint
    /// cycles that intersect every cycle in the graph.
    ///
    /// The method tries to obtain a maximal such set, but the maximality is not guaranteed.
    pub fn independent_cycles(&self) -> Vec<Vec<VariableId>> {
        let graph = SdGraph::from(self);
        graph.restricted_independent_cycles(&graph.mk_all_vertices())
    }

    /// Compute a collection of independent cycles of this `RegulatoryGraph` with desired `parity`.
    /// That is, disjoint cycles of the given `parity` that intersect every other cycle of this
    /// `parity` in the graph.
    ///
    /// The method tries to obtain a maximal such set, but the maximality is not guaranteed.
    pub fn independent_parity_cycles(&self, parity: Sign) -> Vec<Vec<VariableId>> {
        let graph = SdGraph::from(self);
        graph.restricted_independent_parity_cycles(&graph.mk_all_vertices(), parity)
    }
}
