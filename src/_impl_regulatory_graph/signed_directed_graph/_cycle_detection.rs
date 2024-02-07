use crate::VariableId;
use crate::_impl_regulatory_graph::signed_directed_graph::{SdGraph, Sign};
use std::collections::HashSet;
use Sign::Positive;

impl SdGraph {
    /// Compute the shortest cycle (or one of the shortest cycles) within `restriction` that
    /// also contains the `pivot` vertex. The result is a vector with pivot at position zero
    /// and other vertices in the order in which they appear on the cycle. If no such cycle
    /// exists, returns `None`.
    ///
    /// The result is similar to `shortest_cycle_length`, but there is non-trivial overhead
    /// associated with actually computing the cycle, not just its length, hence we separate
    /// the two algorithms. Panics if `pivot` is not a member of `restriction`.
    ///
    /// Finally, you can restrict the search to only include cycles of a specific length
    /// by providing an inclusive `upper_bound` (the length is counted as the number of
    /// edges in the cycle, i.e. a cycle is returned only if `edge_count <= upper_bound`).
    pub fn shortest_cycle(
        &self,
        restriction: &HashSet<VariableId>,
        pivot: VariableId,
        upper_bound: usize,
    ) -> Option<Vec<VariableId>> {
        assert!(
            restriction.contains(&pivot),
            "Pivot vertex must be present in the restriction set."
        );

        // Shortest_cycle is called so often when computing a feedback vertex set, that this
        // actually helps with performance quite a bit compared to a normal hash map.
        let mut shortest_predecessor: Vec<Option<VariableId>> = vec![None; self.successors.len()];

        // No need for frontier to be a set, because each vertex is inserted only if it is
        // inserted into `shorted_predecessor` first, where it is only inserted at most once.
        let mut frontier = vec![pivot];
        let mut length = 0usize;
        while !frontier.is_empty() {
            length += 1;
            if length > upper_bound {
                // There may be a cycle, but it has more than `upper_bound` edges.
                return None;
            }

            let mut new_frontier = Vec::with_capacity(frontier.len());
            for x in frontier {
                for (succ, _) in &self.successors[x.to_index()] {
                    if *succ == pivot {
                        // Found cycle. Because this is BFS, the cycle is minimal,
                        // we just have to back-track.
                        let mut cycle = vec![x];
                        while let Some(last) = cycle.last() {
                            if *last == pivot {
                                // The cycle is complete. Reverse it and return.
                                cycle.reverse();
                                return Some(cycle);
                            }
                            cycle.push(shortest_predecessor[last.to_index()].unwrap());
                        }
                    }
                    if !restriction.contains(succ) {
                        // We don't want to leave `restriction`.
                        continue;
                    }
                    let slot = &mut shortest_predecessor[succ.to_index()];
                    if slot.is_some() {
                        // This vertex was already discovered using a shorter or equivalent path.
                        continue;
                    }
                    *slot = Some(x);
                    new_frontier.push(*succ);
                }
            }

            frontier = new_frontier;
        }

        None
    }

    /// Same as `shortest_cycle`, but in this scenario, only cycles of prescribed `parity`
    /// are considered.
    ///
    /// Cycle parity is calculated over the monotonicity of its edges (i.e. `+` and `-` is
    /// negative, `-` and `-` is positive). Naturally, we only consider simple cycles
    /// (i.e. no vertex appears more than one). Otherwise, a negative parity cycle
    /// can be always made into positive parity cycle by repeating it twice.
    ///
    /// Finally, you can restrict the search to only include cycles of a specific length
    /// by providing an inclusive `upper_bound` (the length is counted as the number of
    /// edges in the cycle, i.e. a cycle is returned only if `edge_count <= upper_bound`).
    pub fn shortest_parity_cycle(
        &self,
        restriction: &HashSet<VariableId>,
        pivot: VariableId,
        target_parity: Sign,
        upper_bound: usize,
    ) -> Option<Vec<VariableId>> {
        assert!(
            restriction.contains(&pivot),
            "Pivot vertex must be present in the restriction set."
        );

        // Shortest_cycle is called so often when computing a feedback vertex set, that this
        // actually helps with performance quite a bit compared to a normal hash map.
        let mut shortest_positive_predecessor: Vec<Option<(VariableId, Sign)>> =
            vec![None; self.successors.len()];
        let mut shortest_negative_predecessor: Vec<Option<(VariableId, Sign)>> =
            vec![None; self.successors.len()];

        // No need for frontier to be a set, because each vertex is inserted only if it is
        // inserted into `shortest_*_predecessor` first, where it is only inserted at most once.
        let mut frontier = vec![(pivot, Positive)];
        let mut length = 0usize;
        while !frontier.is_empty() {
            length += 1;
            if length > upper_bound {
                // There may be a cycle, but it has more than `upper_bound` edges.
                return None;
            }

            let mut new_frontier = Vec::with_capacity(frontier.len());
            for (x, x_sign) in frontier {
                for (succ, succ_sign) in &self.successors[x.to_index()] {
                    let path_sign = x_sign + *succ_sign;
                    if *succ == pivot && path_sign == target_parity {
                        // Found cycle. Because this is BFS, the cycle is minimal,
                        // we just have to back-track. However, it may not be simple: if it
                        // contains the same node twice, it is not a valid cycle.
                        let mut cycle = vec![(x, x_sign)];
                        let mut cycle_set: HashSet<VariableId> = HashSet::from_iter([x]);
                        while let Some((last, last_sign)) = cycle.last() {
                            if *last == pivot {
                                cycle.reverse();
                                return Some(Vec::from_iter(cycle.into_iter().map(|(x, _)| x)));
                            }
                            let next = if *last_sign == Positive {
                                shortest_positive_predecessor[last.to_index()].unwrap()
                            } else {
                                shortest_negative_predecessor[last.to_index()].unwrap()
                            };

                            if cycle_set.contains(&next.0) {
                                // If duplicity is detected, the cycle is invalid.
                                break;
                            } else {
                                // Otherwise extend the cycle with a new node.
                                cycle_set.insert(next.0);
                                cycle.push(next);
                            }
                        }
                    }
                    if *succ == pivot {
                        // Eliminates some spurious cycles with node repetition.
                        continue;
                    }
                    if !restriction.contains(succ) {
                        // We don't want to leave `restriction`.
                        continue;
                    }
                    let slot = if path_sign == Positive {
                        &mut shortest_positive_predecessor[succ.to_index()]
                    } else {
                        &mut shortest_negative_predecessor[succ.to_index()]
                    };
                    if slot.is_some() {
                        // This vertex was already discovered using a shorter or equivalent path.
                        continue;
                    }
                    *slot = Some((x, x_sign));
                    new_frontier.push((*succ, path_sign));
                }
            }

            frontier = new_frontier;
        }

        None
    }
}

#[cfg(test)]
mod tests {
    use crate::RegulatoryGraph;
    use crate::_impl_regulatory_graph::signed_directed_graph::SdGraph;
    use crate::_impl_regulatory_graph::signed_directed_graph::Sign::{Negative, Positive};

    #[test]
    pub fn test_cycle_detection() {
        // Scenario: There are two cycles: x1 -> x2 -> x3 -> x4 and x1 -> x5 -> x4. Finally, x6 can
        // reach x1, but is not on a cycle.
        let rg = RegulatoryGraph::try_from(
            r#"
            x_1 -> x_2
            x_2 -> x_3
            x_3 -> x_4
            x_4 -> x_1
            x_1 -> x_5
            x_5 -> x_4
            x_6 -> x_1
        "#,
        )
        .unwrap();

        let x_1 = rg.find_variable("x_1").unwrap();
        let x_2 = rg.find_variable("x_2").unwrap();
        let x_3 = rg.find_variable("x_3").unwrap();
        let x_4 = rg.find_variable("x_4").unwrap();
        let x_5 = rg.find_variable("x_5").unwrap();
        let x_6 = rg.find_variable("x_6").unwrap();

        let graph = SdGraph::from(&rg);

        let mut vertices = graph.mk_all_vertices();

        let upper_bound = usize::MAX;

        assert_eq!(
            Some(vec![x_1, x_5, x_4]),
            graph.shortest_cycle(&vertices, x_1, upper_bound)
        );
        assert_eq!(
            Some(vec![x_2, x_3, x_4, x_1]),
            graph.shortest_cycle(&vertices, x_2, upper_bound)
        );
        assert_eq!(None, graph.shortest_cycle(&vertices, x_6, upper_bound));

        vertices.remove(&x_5);

        assert_eq!(
            Some(vec![x_1, x_2, x_3, x_4]),
            graph.shortest_cycle(&vertices, x_1, upper_bound)
        );
    }

    #[test]
    pub fn test_parity_cycle_detection() {
        // Scenario: There are two cycles: x1 -> x2 -| x3 -> x4 -| x1 (positive) and
        // x1 -> x5 -> x4 -| x_1 (negative). Finally, x6 can reach x1, but is not a member of a cycle.

        let rg = RegulatoryGraph::try_from(
            r#"
            x_1 -> x_2
            x_2 -| x_3
            x_3 -> x_4
            x_4 -| x_1
            x_1 -> x_5
            x_5 -> x_4
            x_6 -| x_1
        "#,
        )
        .unwrap();

        let x_1 = rg.find_variable("x_1").unwrap();
        let x_2 = rg.find_variable("x_2").unwrap();
        let x_3 = rg.find_variable("x_3").unwrap();
        let x_4 = rg.find_variable("x_4").unwrap();
        let x_5 = rg.find_variable("x_5").unwrap();

        let graph = SdGraph::from(&rg);

        let mut vertices = graph.mk_all_vertices();

        let upper_bound = usize::MAX;

        assert_eq!(
            Some(vec![x_1, x_2, x_3, x_4]),
            graph.shortest_parity_cycle(&vertices, x_1, Positive, upper_bound)
        );
        assert_eq!(
            Some(vec![x_1, x_5, x_4]),
            graph.shortest_parity_cycle(&vertices, x_1, Negative, upper_bound)
        );

        vertices.remove(&x_5);

        assert_eq!(
            Some(vec![x_1, x_2, x_3, x_4]),
            graph.shortest_parity_cycle(&vertices, x_1, Positive, upper_bound)
        );
        assert_eq!(
            None,
            graph.shortest_parity_cycle(&vertices, x_1, Negative, upper_bound)
        );
    }

    #[test]
    pub fn test_simple_parity_cycles() {
        // This tests whether the implementation correctly ignores non-simple cycles. The graph
        // has a positive cycle in which a negative cycle is embedded. We want to test that the
        // smaller inner cycle is never repeated more than once by the larger cycle.

        let rg = RegulatoryGraph::try_from(
            r#"
            x_1 -> x_2
            x_2 -> x_3
            x_3 -| x_2
            x_3 -> x_1
        "#,
        )
        .unwrap();

        let x_1 = rg.find_variable("x_1").unwrap();
        let x_2 = rg.find_variable("x_2").unwrap();
        let x_3 = rg.find_variable("x_3").unwrap();

        let graph = SdGraph::from(&rg);

        let vertices = graph.mk_all_vertices();

        let upper_bound = usize::MAX;

        // Node x_1 could have a negative cycle by repeating the inner cycle multiple times, but
        // this is not allowed.
        assert_eq!(
            Some(vec![x_1, x_2, x_3]),
            graph.shortest_parity_cycle(&vertices, x_1, Positive, upper_bound)
        );
        assert_eq!(
            None,
            graph.shortest_parity_cycle(&vertices, x_1, Negative, upper_bound)
        );

        // However, the negative cycle is still there and is detected for x_2
        assert_eq!(
            Some(vec![x_2, x_3, x_1]),
            graph.shortest_parity_cycle(&vertices, x_2, Positive, upper_bound)
        );
        assert_eq!(
            Some(vec![x_2, x_3]),
            graph.shortest_parity_cycle(&vertices, x_2, Negative, upper_bound)
        );
    }
}
