use crate::VariableId;
use crate::_impl_regulatory_graph::signed_directed_graph::{SdGraph, Sign};
use std::collections::HashSet;

impl SdGraph {
    /// Compute a feedback vertex set of the subgraph induced by the vertices in the
    /// given `restriction` set.
    ///
    /// A feedback vertex set is a set of vertices such that when these vertices are removed,
    /// the resulting graph is acyclic.
    ///
    /// The algorithm attempts to minimize the size of the resulting FVS, but it
    /// is not guaranteed that the result is minimal, as the minimal FVS problem
    /// is NP complete. Also note that while the *size* of the result is deterministic,
    /// the actual vertices may not be as they depend on the iteration order of a `HashSet`.
    ///
    /// The algorithm works by greedily picking vertices from the shortest cycles, prioritising
    /// vertices with the highest overall degree.
    pub fn restricted_feedback_vertex_set(
        &self,
        restriction: &HashSet<VariableId>,
    ) -> HashSet<VariableId> {
        let mut result = HashSet::new();

        // By preprocessing the state space into components, we avoid a lot of cycle detection
        // that would otherwise just prove that the variable does not have any cycles.
        let mut components = self.restricted_strongly_connected_components(restriction);
        while let Some(mut scc) = components.pop() {
            let mut best_candidate = (VariableId::from_index(0), usize::MAX, 0usize);
            // Not particularly efficient but keeps the procedure deterministic.
            // However, by a lucky coincidence, it also seems to on average improve the results :O
            let mut scc_iter: Vec<VariableId> = scc.iter().cloned().collect();
            scc_iter.sort();
            for x in &scc_iter {
                if let Some(cycle_length) = self.shortest_cycle_length(&scc, *x, best_candidate.1) {
                    if cycle_length == 1 {
                        // If the cycle has length one, it is guaranteed to appear in the FVS
                        // and we can just stop looking for the other cycles.
                        best_candidate = (*x, cycle_length, 0);
                        break;
                    }
                    let degree = self.approx_degree(*x, &scc);
                    if cycle_length < best_candidate.1 {
                        // If this is the best cycle, just update it.
                        best_candidate = (*x, cycle_length, degree);
                    } else if cycle_length == best_candidate.1 {
                        // If this is equal to the best cycle, compare degrees.
                        if degree > best_candidate.2 {
                            best_candidate = (*x, cycle_length, degree);
                        }
                    }
                }
            }

            assert_ne!(best_candidate.1, usize::MAX);
            result.insert(best_candidate.0);
            scc.remove(&best_candidate.0);

            // Finally, run SCC decomposition again on the smaller component and "return" results
            // back into processing.
            components.append(&mut self.restricted_strongly_connected_components(&scc));
        }

        result
    }

    /// Compute a feedback vertex set of the desired parity, considered within the subgraph induced
    /// by the vertices in `restriction`.
    ///
    /// A parity feedback vertex set is a set of vertices such that when removed, the graph has
    /// no cycles of the specified parity. See also `restriction_feedback_vertex_set` for notes
    /// about determinism, minimality and complexity.
    pub fn restricted_parity_feedback_vertex_set(
        &self,
        restriction: &HashSet<VariableId>,
        parity: Sign,
    ) -> HashSet<VariableId> {
        let mut result = HashSet::new();

        let mut components = self.restricted_strongly_connected_components(restriction);
        while let Some(mut scc) = components.pop() {
            let mut best_candidate = (VariableId::from_index(0), usize::MAX, 0usize);
            // Not particularly efficient but keeps the procedure deterministic.
            // However, by a lucky coincidence, it also seems to on average improve the results :O
            let mut scc_iter: Vec<VariableId> = scc.iter().cloned().collect();
            scc_iter.sort();
            for x in &scc_iter {
                if let Some(cycle_length) =
                    self.shortest_parity_cycle_length(&scc, *x, parity, best_candidate.1)
                {
                    if cycle_length == 1 {
                        // If the cycle has length one, it is guaranteed to appear in the FVS
                        // and we can just stop looking for any other cycles.
                        best_candidate = (*x, cycle_length, 0);
                        break;
                    }
                    let degree = self.approx_degree(*x, &scc);
                    if cycle_length < best_candidate.1 {
                        // If this is the best cycle, just update it.
                        best_candidate = (*x, cycle_length, degree);
                    } else if cycle_length == best_candidate.1 {
                        // If this is equal to the best cycle, compare degrees.
                        if degree > best_candidate.2 {
                            best_candidate = (*x, cycle_length, degree);
                        }
                    }
                }
            }

            if best_candidate.1 == usize::MAX {
                // No cycles found.
                continue;
            }

            result.insert(best_candidate.0);
            scc.remove(&best_candidate.0);
            components.append(&mut self.restricted_strongly_connected_components(&scc));
        }

        result
    }

    /// **(internal)** Compute the degree of a vertex within the given set.
    pub(crate) fn approx_degree(
        &self,
        vertex: VariableId,
        universe: &HashSet<VariableId>,
    ) -> usize {
        let in_degree = self.predecessors[vertex.to_index()]
            .iter()
            .filter(|(x, _)| universe.contains(x))
            .count();
        let out_degree = self.successors[vertex.to_index()]
            .iter()
            .filter(|(x, _)| universe.contains(x))
            .count();

        in_degree + out_degree
    }
}

#[cfg(test)]
mod tests {
    use crate::RegulatoryGraph;
    use crate::_impl_regulatory_graph::signed_directed_graph::SdGraph;
    use crate::_impl_regulatory_graph::signed_directed_graph::Sign::{Negative, Positive};

    #[test]
    pub fn test_feedback_vertex_set() {
        // Its a similar test graph to the one used for component computation,
        // but `b_1 -> b_2` is a negative cycle and the `d`-component has both one positive and
        // one negative cycle. Finally, `e` has a positive self-loop
        let rg = RegulatoryGraph::try_from(
            r#"
            a -> c
            b_1 -> b_2
            b_2 -| b_1
            b_2 -> c
            c -> d_2
            c -> e
            d_1 -> d_3
            d_3 -| d_2
            d_2 -> d_1
            d_1 -> d_2
            e -> e
        "#,
        )
        .unwrap();

        let a = rg.find_variable("a").unwrap();
        let b_1 = rg.find_variable("b_1").unwrap();
        let b_2 = rg.find_variable("b_2").unwrap();
        let c = rg.find_variable("c").unwrap();
        let d_1 = rg.find_variable("d_1").unwrap();
        let d_2 = rg.find_variable("d_2").unwrap();
        let d_3 = rg.find_variable("d_3").unwrap();
        let e = rg.find_variable("e").unwrap();

        let graph = SdGraph::from(&rg);

        let vertices = graph.mk_all_vertices();
        let fvs = graph.restricted_feedback_vertex_set(&vertices);
        let p_fvs = graph.restricted_parity_feedback_vertex_set(&vertices, Positive);
        let n_fvs = graph.restricted_parity_feedback_vertex_set(&vertices, Negative);

        assert!(!(fvs.contains(&a) || p_fvs.contains(&a) || n_fvs.contains(&a)));
        assert!(!(fvs.contains(&c) || p_fvs.contains(&c) || n_fvs.contains(&c)));

        assert_eq!(fvs.len(), 3);
        assert_eq!(p_fvs.len(), 2);
        assert_eq!(n_fvs.len(), 2);

        assert!(fvs.contains(&e));
        assert!(p_fvs.contains(&e));
        assert!(!n_fvs.contains(&e));

        assert!(fvs.contains(&b_1) || fvs.contains(&b_2));
        assert!(!(p_fvs.contains(&b_1) || p_fvs.contains(&b_2)));
        assert!(n_fvs.contains(&b_1) || n_fvs.contains(&b_2));

        // d_3 can't appear in FVS or positive FVS, but it can appear in negative FVS.
        assert!(fvs.contains(&d_1) || fvs.contains(&d_2));
        assert!(p_fvs.contains(&d_1) || p_fvs.contains(&d_2));
        assert!(n_fvs.contains(&d_1) || n_fvs.contains(&d_2) || n_fvs.contains(&d_3));
    }
}
