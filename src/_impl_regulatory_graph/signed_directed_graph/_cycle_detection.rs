use crate::_impl_regulatory_graph::signed_directed_graph::{SdGraph, Sign};
use crate::Sign::Negative;
use crate::VariableId;
use Sign::Positive;
use fxhash::FxBuildHasher;
use std::collections::{HashMap, HashSet};

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

        /*
           The following algorithm uses BFS to find the shortest cycle. It essentially
           computes the shortest path from pivot to all vertices and terminates if it finds
           a path back towards itself.
        */

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

        /*
           The following algorithm uses dynamic programming to compute a table which specifies
           for each (viable) variable-parity combination the shortest simple path towards the
           pivot. Based on this shortest path, we can decide if there is an appropriate parity
           cycle from pivot or not.

           The table is computed bottom-up, starting from direct predecessors. In each "main"
           iteration, we check if a cycle is possible and terminate early if a cycle is found.

           **Note that this is a tricky problem to solve exactly using pure DFS/BFS, even with
           some clever memoization tricks. In particular, one has to properly save the tree of
           shortest paths and at the same time ensure that these are indeed only simple paths.
           If you ever modify this, test carefully! (random networks with 1000+ nodes seem to
           be a good place to start)**

           **Also note that you will be tempted to cut off a path if a shorter one is known.
           This is not correct! There may be a very short path that goes to pivot but cannot be
           used because we need the result to be a simple path. Instead, you probably really
           need to keep all paths running until they either reach pivot or stop being simple.**

           The use of FxHash is not super critical, but it helps if cycles are computed very
           often (e.g. in FVS detection).
        */

        if upper_bound == 0 {
            // No cycle can have zero edges.
            return None;
        }

        // If pivot has a self-loop, just return it.
        if self.successors[pivot.to_index()].contains(&(pivot, target_parity)) {
            return Some(vec![pivot]);
        }

        if upper_bound == 1 {
            // Only a self-loop can have one edge.
            return None;
        }

        // A vertex in a larger graph where each variable can be visited with a specific sign.
        type Config = (VariableId, Sign);

        let mut reaches_pivot_in_steps: Vec<HashMap<Config, Config, FxBuildHasher>> = Vec::new();
        // Noone can reach pivot in zero steps.
        reaches_pivot_in_steps.push(HashMap::with_hasher(FxBuildHasher::default()));

        // Direct predecessors can reach pivot in zero steps.
        let mut one_step = HashMap::with_hasher(FxBuildHasher::default());
        for (pred, sign) in &self.predecessors[pivot.to_index()] {
            // Pivot should never be inserted here (see also similar condition below), because
            // it is already "on the path". Adding it again would mean the result is not
            // a simple path.
            if restriction.contains(pred) && *pred != pivot {
                one_step.insert((*pred, *sign), (pivot, Positive));
            }
        }
        reaches_pivot_in_steps.push(one_step);

        let mut path_length = 1usize;
        let mut go_through = 'search: loop {
            // There is a negative pivot cycle of length `path_length + 1` if we can get directly
            // from pivot to one of the viable path candidates.
            let path_candidates = &reaches_pivot_in_steps[path_length];
            for (succ, sign) in &self.successors[pivot.to_index()] {
                if restriction.contains(succ) {
                    let path_sign = match (target_parity, *sign) {
                        (Negative, Negative) => Positive,
                        (Negative, Positive) => Negative,
                        (Positive, Negative) => Negative,
                        (Positive, Positive) => Positive,
                    };
                    if path_candidates.contains_key(&(*succ, path_sign)) {
                        break 'search (*succ, path_sign);
                    }
                }
            }

            if path_length + 1 == upper_bound {
                // All cycles from here on have more edges than the upper bound.
                return None;
            }

            // If we haven't found a cycle with the current length, we need to extend the
            // paths and try again.
            path_length += 1;
            let mut next_step = HashMap::with_hasher(FxBuildHasher::default());
            for (x, x_sign) in path_candidates.keys() {
                'pred: for (pred, pred_sign) in &self.predecessors[x.to_index()] {
                    if restriction.contains(pred) && *pred != pivot {
                        let mut check_simple = (*x, *x_sign);
                        let mut check_simple_length = path_length - 1;
                        while check_simple.0 != pivot {
                            if check_simple.0 == *pred {
                                // This predecessor is already used on the path we are at.
                                // We can't use it again.
                                continue 'pred;
                            }
                            check_simple = *reaches_pivot_in_steps[check_simple_length]
                                .get(&check_simple)
                                .unwrap();
                            check_simple_length -= 1;
                        }

                        let pred_path_sign = *x_sign + *pred_sign;
                        next_step.insert((*pred, pred_path_sign), (*x, *x_sign));
                    }
                }
            }
            if next_step.is_empty() {
                // If we haven't found a nicer path for any vertex, there is no cycle.
                return None;
            }
            reaches_pivot_in_steps.push(next_step);
        };

        let mut cycle = vec![pivot];
        while go_through.0 != pivot {
            cycle.push(go_through.0);
            go_through = *reaches_pivot_in_steps[path_length]
                .get(&go_through)
                .unwrap();
            path_length -= 1;
        }

        Some(cycle)
    }
}

#[cfg(test)]
mod tests {
    use crate::_impl_regulatory_graph::signed_directed_graph::SdGraph;
    use crate::_impl_regulatory_graph::signed_directed_graph::Sign::{Negative, Positive};
    use crate::RegulatoryGraph;

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
