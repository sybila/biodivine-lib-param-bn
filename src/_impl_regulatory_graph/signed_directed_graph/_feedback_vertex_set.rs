use crate::VariableId;
use crate::_impl_regulatory_graph::signed_directed_graph::{SdGraph, Sign};
use std::collections::{HashMap, HashSet};

impl SdGraph {
    /// A utility function that prunes the `candidates` set to a smaller subset that is still
    /// guaranteed to be a valid FVS with respect to the specified cycle detection function.
    ///
    /// This is not the complete FVS approximation algorithm, but it is used multiple times,
    /// so we abstract it into this helper method.
    fn _fvs_helper<F: Fn(&HashSet<VariableId>, VariableId) -> Option<Vec<VariableId>>>(
        &self,
        subgraph: &mut HashSet<VariableId>,
        mut candidates: HashSet<VariableId>,
        compute_cycle: F,
    ) -> HashSet<VariableId> {
        let mut result = HashSet::new();

        // The shortest known cycle in the current `subgraph` for the given `pivot`.
        let mut shortest_cycle_for_pivot: HashMap<VariableId, Vec<VariableId>> = HashMap::new();

        while !candidates.is_empty() {
            // Ensure determinism.
            let mut iterable = Vec::from_iter(candidates.clone());
            iterable.sort();

            let mut best = (VariableId(0), usize::MAX, 0);
            for vertex in iterable {
                let cycle = if let Some(known_cycle) = shortest_cycle_for_pivot.get(&vertex) {
                    known_cycle
                } else if let Some(computed_cycle) = compute_cycle(subgraph, vertex) {
                    shortest_cycle_for_pivot
                        .entry(vertex)
                        .or_insert(computed_cycle)
                } else {
                    subgraph.remove(&vertex);
                    candidates.remove(&vertex);
                    continue;
                };

                let degree = self.approx_degree(vertex, subgraph);
                if cycle.len() < best.1 || (cycle.len() == best.1 && degree > best.2) {
                    best = (vertex, cycle.len(), degree);
                }
                if cycle.len() == 1 {
                    // Self-loops are always optimal.
                    break;
                }
            }

            if best.1 == usize::MAX {
                // The remaining graph is acyclic!
                return result;
            }

            result.insert(best.0);
            subgraph.remove(&best.0);
            candidates.remove(&best.0);

            shortest_cycle_for_pivot.retain(|_k, v| !v.contains(&best.0));
        }

        result
    }

    /// Compute a feedback vertex set of the subgraph induced by the vertices in the
    /// given `restriction` set.
    ///
    /// A feedback vertex set is a set of vertices such that when these vertices are removed,
    /// the resulting graph is acyclic.
    ///
    /// The algorithm attempts to minimize the size of the resulting FVS, but it
    /// is not guaranteed that the result is minimal, as the minimal FVS problem
    /// is NP complete.
    ///
    /// The algorithm works by greedily picking vertices from the shortest cycles, prioritising
    /// vertices with the highest overall degree.
    pub fn restricted_feedback_vertex_set(
        &self,
        restriction: &HashSet<VariableId>,
    ) -> HashSet<VariableId> {
        let candidates = restriction.clone();

        // We then prune the candidates twice: First time, most of the uninteresting nodes are
        // removed, second time then optimizes the result such that it is (usually) at least
        // subset minimal. The minimality is still not guaranteed though.

        let candidates = self._fvs_helper(&mut restriction.clone(), candidates, |g, x| {
            self.shortest_cycle(g, x, usize::MAX)
        });

        self._fvs_helper(&mut restriction.clone(), candidates, |g, x| {
            self.shortest_cycle(g, x, usize::MAX)
        })
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
        // We will be searching in a subset of a known FVS. This is because FVS detection is
        // a bit faster and usually gives us a reasonable starting point.
        let candidates = self.restricted_feedback_vertex_set(restriction);

        // The same as normal FVS method, but uses different cycle detection. Here, we don't
        // repeat it again, because in most cases it is not needed.
        self._fvs_helper(&mut restriction.clone(), candidates, |g, x| {
            self.shortest_parity_cycle(g, x, parity, usize::MAX)
        })
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
    use crate::_impl_regulatory_graph::signed_directed_graph::SdGraph;
    use crate::_impl_regulatory_graph::signed_directed_graph::Sign::{Negative, Positive};
    use crate::{BooleanNetwork, RegulatoryGraph, VariableId};
    use std::collections::HashSet;

    #[test]
    pub fn test_feedback_vertex_set() {
        // It's a similar test graph to the one used for component computation,
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

    #[test]
    fn test_feedback_vertex_set_2() {
        let bn = BooleanNetwork::try_from(
            r#"
            a -> b
            b -|? c
            c -? a
            a -| c
            c -> d
            e -| b
        "#,
        )
        .unwrap();

        let expected = HashSet::from_iter([VariableId::from_index(2)]);
        assert_eq!(expected, bn.as_graph().feedback_vertex_set());
    }
}
