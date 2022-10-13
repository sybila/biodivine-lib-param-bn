use crate::VariableId;
use crate::_impl_regulatory_graph::signed_directed_graph::{SdGraph, Sign};
use std::collections::HashSet;

impl SdGraph {
    /// Return the set of vertices forward-reachable from the `initial` set.
    pub fn forward_reachable(&self, initial: HashSet<VariableId>) -> HashSet<VariableId> {
        reachability(&self.successors, initial)
    }

    /// Return the set of vertices backward-reachable from the `initial` set.
    pub fn backward_reachable(&self, initial: HashSet<VariableId>) -> HashSet<VariableId> {
        reachability(&self.predecessors, initial)
    }

    /// Return the set of vertices forward-reachable from the `initial` set within
    /// the `restriction` set.
    pub fn restricted_forward_reachable(
        &self,
        restriction: &HashSet<VariableId>,
        initial: HashSet<VariableId>,
    ) -> HashSet<VariableId> {
        restricted_reachability(&self.successors, initial, restriction)
    }

    /// Return the set of vertices backward-reachable from the `initial` set within
    /// the `restriction` set.
    pub fn restricted_backward_reachable(
        &self,
        restriction: &HashSet<VariableId>,
        initial: HashSet<VariableId>,
    ) -> HashSet<VariableId> {
        restricted_reachability(&self.predecessors, initial, restriction)
    }
}

/// **(internal)** A shared utility method that implements either forward or backward reachability
/// depending on the supplied set of `SdGraph` edges.
fn reachability(
    edges: &Vec<Vec<(VariableId, Sign)>>,
    initial: HashSet<VariableId>,
) -> HashSet<VariableId> {
    let mut result = initial;
    let mut frontier = result.clone();
    while !frontier.is_empty() {
        let mut new_frontier = HashSet::new();
        for x in frontier {
            for (step, _) in &edges[x.to_index()] {
                if !result.contains(step) {
                    result.insert(*step);
                    new_frontier.insert(*step);
                }
            }
        }
        frontier = new_frontier;
    }
    result
}

/// **(internal)** A shared utility method that implements either a restricted forward or backward
/// reachability depending on the supplied `SdGraph` edge relation.
fn restricted_reachability(
    edges: &Vec<Vec<(VariableId, Sign)>>,
    initial: HashSet<VariableId>,
    universe: &HashSet<VariableId>,
) -> HashSet<VariableId> {
    let mut result = initial;
    let mut frontier = result.clone();
    while !frontier.is_empty() {
        let mut new_frontier = HashSet::new();
        for x in frontier {
            for (step, _) in &edges[x.to_index()] {
                if !result.contains(step) && universe.contains(step) {
                    result.insert(*step);
                    new_frontier.insert(*step);
                }
            }
        }
        frontier = new_frontier;
    }
    result
}

#[cfg(test)]
mod tests {
    use crate::_impl_regulatory_graph::_impl_misc::tests::build_test_regulatory_graph;
    use crate::_impl_regulatory_graph::signed_directed_graph::SdGraph;
    use std::collections::HashSet;

    #[test]
    pub fn basic_reachability_test() {
        // See method for high-level graph description.
        let rg = build_test_regulatory_graph();

        let a = rg.find_variable("a").unwrap();
        let b_1 = rg.find_variable("b_1").unwrap();
        let b_2 = rg.find_variable("b_2").unwrap();
        let c = rg.find_variable("c").unwrap();
        let d_1 = rg.find_variable("d_1").unwrap();
        let d_2 = rg.find_variable("d_2").unwrap();
        let d_3 = rg.find_variable("d_3").unwrap();
        let e = rg.find_variable("e").unwrap();

        let graph = SdGraph::from(&rg);

        let fwd = graph.forward_reachable(HashSet::from([c]));
        let bwd = graph.backward_reachable(HashSet::from([c]));

        assert_eq!(fwd, HashSet::from([c, d_1, d_2, d_3, e]));
        assert_eq!(bwd, HashSet::from([c, b_1, b_2, a]));

        let restriction = HashSet::from([b_1, b_2, c, e]);

        let fwd = graph.restricted_forward_reachable(&restriction, HashSet::from([b_1, c]));
        let bwd = graph.restricted_backward_reachable(&restriction, HashSet::from([e]));

        assert_eq!(fwd, restriction);
        assert_eq!(bwd, restriction);
    }
}
