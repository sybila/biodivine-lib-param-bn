use crate::VariableId;
use crate::_impl_regulatory_graph::signed_directed_graph::Sign::Negative;
use crate::_impl_regulatory_graph::signed_directed_graph::{SdGraph, Sign};
use std::cmp::min;
use std::collections::{HashMap, HashSet};
use Sign::Positive;

impl SdGraph {
    /// Compute the length of the shortest cycle within `restriction` that contains `pivot`.
    /// `None` if no such cycle exists.
    ///
    /// The length is in terms of edges (so cycle of length 1 is a self-loop). Panics if `pivot`
    /// is not a member of `restriction`.
    ///
    /// Finally, you can restrict the search to only include cycles of a specific length
    /// by providing the `upper_bound`.
    pub fn shortest_cycle_length(
        &self,
        restriction: &HashSet<VariableId>,
        pivot: VariableId,
        upper_bound: usize,
    ) -> Option<usize> {
        assert!(restriction.contains(&pivot));

        let mut visited = HashSet::from([pivot]);
        let mut frontier = HashSet::from([pivot]);

        let mut length = 0;
        while !frontier.is_empty() {
            length += 1;
            if length > upper_bound {
                return None;
            }

            let mut new_frontier = HashSet::new();
            for x in frontier {
                for (successor, _) in &self.successors[x.to_index()] {
                    if *successor == pivot {
                        return Some(length);
                    }
                    if restriction.contains(successor) && !visited.contains(successor) {
                        visited.insert(*successor);
                        new_frontier.insert(*successor);
                    }
                }
            }

            frontier = new_frontier;
        }

        None
    }

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
    /// by providing the `upper_bound`.
    pub fn shortest_cycle(
        &self,
        restriction: &HashSet<VariableId>,
        pivot: VariableId,
        upper_bound: usize,
    ) -> Option<Vec<VariableId>> {
        assert!(restriction.contains(&pivot));

        let mut best_cycle: Option<Vec<VariableId>> = None;
        let mut best_cycle_length = usize::MAX;
        let mut distances: HashMap<VariableId, usize> =
            restriction.iter().map(|it| (*it, usize::MAX)).collect();
        distances.insert(pivot, 0);

        fn successor_function(
            graph: &SdGraph,
            restriction: &HashSet<VariableId>,
            vertex: VariableId,
        ) -> Vec<VariableId> {
            graph.successors[vertex.to_index()]
                .iter()
                .map(|(it, _)| *it)
                .filter(|it| restriction.contains(it))
                .collect()
        }

        let mut stack = vec![(pivot, successor_function(self, restriction, pivot))];

        while let Some((vertex, successors)) = stack.last_mut() {
            let vertex_distance = distances[vertex];

            if best_cycle_length <= vertex_distance || upper_bound <= vertex_distance {
                stack.pop();
                continue;
            }

            if let Some(successor) = successors.pop() {
                let successor_distance = distances[&successor];
                let new_successor_distance = min(successor_distance, vertex_distance + 1);
                if new_successor_distance < successor_distance {
                    // Note that this can't happen to the pivot since its distance is always zero.
                    distances.insert(successor, new_successor_distance);
                    stack.push((successor, successor_function(self, restriction, successor)));
                } else if successor == pivot {
                    // Hence we have to handle pivot independently.
                    let cycle_on_stack: Vec<VariableId> = stack.iter().map(|(it, _)| *it).collect();
                    if cycle_on_stack.len() < best_cycle_length {
                        best_cycle_length = cycle_on_stack.len();
                        best_cycle = Some(cycle_on_stack);
                    }
                } else {
                    // Otherwise, do nothing. The successor cannot be improved by this path.
                }
            } else {
                stack.pop();
                continue;
            }
        }

        best_cycle
    }

    /// Same as `shortest_cycle_length`, but in this scenario, only cycles of prescribed `parity`
    /// are considered.
    ///
    /// Cycle parity is calculated over the monotonicity of its edges (i.e. `+` and `-` is
    /// negative, `-` and `-` is positive). Naturally, we only consider simple cycles
    /// (i.e. no vertex appears more than one). Otherwise, a negative parity cycle
    /// can be always made into positive parity cycle by repeating it twice.
    ///
    /// Finally, you can restrict the search to only include cycles of a specific length
    /// by providing the `upper_bound`.
    pub fn shortest_parity_cycle_length(
        &self,
        restriction: &HashSet<VariableId>,
        pivot: VariableId,
        target_parity: Sign,
        upper_bound: usize,
    ) -> Option<usize> {
        // For generic length, it makes sense to compute using BFS, but for parity length,
        // its not actually that straightforward. If we really want to ensure only simple cycles
        // are counted, we have to use the more costly DFS method.
        self.shortest_parity_cycle(restriction, pivot, target_parity, upper_bound)
            .map(|it| it.len())
    }

    /// Same as `shortest_cycle`, but in this scenario, only cycles of prescribed `parity`
    /// are considered.
    ///
    /// See also `shortest_parity_cycle_length` on more discussion about parity.
    ///
    /// Finally, you can restrict the search to only include cycles of a specific length
    /// by providing the `upper_bound`.
    pub fn shortest_parity_cycle(
        &self,
        restriction: &HashSet<VariableId>,
        pivot: VariableId,
        target_parity: Sign,
        upper_bound: usize,
    ) -> Option<Vec<VariableId>> {
        assert!(restriction.contains(&pivot));

        let mut best_cycle: Option<Vec<VariableId>> = None;
        let mut best_cycle_length = usize::MAX;
        let mut distances: HashMap<(VariableId, Sign), usize> = restriction
            .iter()
            .map(|it| ((*it, Positive), usize::MAX))
            .chain(restriction.iter().map(|it| ((*it, Negative), usize::MAX)))
            .collect();
        distances.insert((pivot, Positive), 0);
        distances.insert((pivot, Negative), 0);

        fn successor_function(
            graph: &SdGraph,
            restriction: &HashSet<VariableId>,
            vertex: VariableId,
        ) -> Vec<(VariableId, Sign)> {
            graph.successors[vertex.to_index()]
                .iter()
                .cloned()
                .filter(|(it, _)| restriction.contains(it))
                .collect()
        }

        let mut stack = vec![(
            (pivot, Positive),
            successor_function(self, restriction, pivot),
        )];

        while let Some((item, successors)) = stack.last_mut() {
            let vertex_distance = distances[item];

            if best_cycle_length <= vertex_distance || upper_bound <= vertex_distance {
                stack.pop();
                continue;
            }

            if let Some((successor, edge_sign)) = successors.pop() {
                let path_parity = item.1 + edge_sign;

                let successor_distance = distances[&(successor, path_parity)];
                let new_successor_distance = min(successor_distance, vertex_distance + 1);
                if new_successor_distance < successor_distance {
                    // Note that this can't happen to the pivot since its distance is always zero.

                    // However, we still have to ensure that only simple cycles are explored,
                    // and for this we have to look at the whole stack.
                    let is_on_stack = stack.iter().any(|((x, _), _)| *x == successor);
                    if !is_on_stack {
                        distances.insert((successor, path_parity), new_successor_distance);
                        stack.push((
                            (successor, path_parity),
                            successor_function(self, restriction, successor),
                        ));
                    }
                } else if successor == pivot {
                    // Here, we then have to handle pivot independently.
                    if path_parity == target_parity {
                        let cycle_on_stack: Vec<VariableId> =
                            stack.iter().map(|((it, _), _)| *it).collect();
                        if cycle_on_stack.len() < best_cycle_length {
                            best_cycle_length = cycle_on_stack.len();
                            best_cycle = Some(cycle_on_stack);
                        }
                    }
                } else {
                    // Otherwise, do nothing. The successor cannot be improved by this path.
                }
            } else {
                stack.pop();
                continue;
            }
        }

        best_cycle
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
            Some(3),
            graph.shortest_cycle_length(&vertices, x_1, upper_bound)
        );
        assert_eq!(
            Some(4),
            graph.shortest_cycle_length(&vertices, x_2, upper_bound)
        );
        assert_eq!(
            None,
            graph.shortest_cycle_length(&vertices, x_6, upper_bound)
        );

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
            Some(4),
            graph.shortest_cycle_length(&vertices, x_1, upper_bound)
        );
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
        let x_6 = rg.find_variable("x_6").unwrap();

        let graph = SdGraph::from(&rg);

        let mut vertices = graph.mk_all_vertices();

        let upper_bound = usize::MAX;

        assert_eq!(
            Some(4),
            graph.shortest_parity_cycle_length(&vertices, x_1, Positive, upper_bound)
        );
        assert_eq!(
            Some(3),
            graph.shortest_parity_cycle_length(&vertices, x_1, Negative, upper_bound)
        );

        assert_eq!(
            None,
            graph.shortest_parity_cycle_length(&vertices, x_5, Positive, upper_bound)
        );
        assert_eq!(
            Some(3),
            graph.shortest_parity_cycle_length(&vertices, x_5, Negative, upper_bound)
        );

        assert_eq!(
            Some(4),
            graph.shortest_parity_cycle_length(&vertices, x_2, Positive, upper_bound)
        );
        assert_eq!(
            None,
            graph.shortest_parity_cycle_length(&vertices, x_2, Negative, upper_bound)
        );

        assert_eq!(
            None,
            graph.shortest_parity_cycle_length(&vertices, x_6, Positive, upper_bound)
        );
        assert_eq!(
            None,
            graph.shortest_parity_cycle_length(&vertices, x_6, Negative, upper_bound)
        );

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
}
