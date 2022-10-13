use crate::VariableId;
use crate::_impl_regulatory_graph::signed_directed_graph::{SdGraph, Sign};
use std::collections::HashSet;

impl SdGraph {
    /// Compute a collection of independent cycles of this directed graph within the given
    /// `restriction` set.
    ///
    /// Independent cycles are cycles that do not intersect, but together cover every cycle in
    /// the graph. The method tries to maximize the number of the returned cycles, but the result
    /// is not guaranteed to be maximal.
    ///
    /// The cycles are expected to be sorted by length, but otherwise the result is not guaranteed
    /// to be deterministic.
    pub fn restricted_independent_cycles(
        &self,
        restriction: &HashSet<VariableId>,
    ) -> Vec<Vec<VariableId>> {
        let mut cycles = Vec::new();

        let mut components = self.restricted_strongly_connected_components(restriction);
        while let Some(mut scc) = components.pop() {
            let mut best_cycle = None;
            let mut best_cycle_len = usize::MAX;
            for x in &scc {
                if let Some(cycle) = self.shortest_cycle(&scc, *x, best_cycle_len) {
                    if cycle.len() == 1 {
                        // Cycle of length one will always win, no need to check further.
                        best_cycle = Some(cycle);
                        break;
                    } else if cycle.len() < best_cycle_len {
                        best_cycle_len = cycle.len();
                        best_cycle = Some(cycle);
                    }
                    // Note that for now, we are not breaking ties in any meaningful way, hence
                    // the result is non-deterministic. But I'm not even sure that the result of
                    // cycle detection is deterministic so this might not be a big deal.
                }
            }

            if let Some(best_cycle) = best_cycle {
                for x in &best_cycle {
                    scc.remove(x);
                }
                cycles.push(best_cycle);
                components.append(&mut self.restricted_strongly_connected_components(&scc));
            }
        }

        cycles.sort_by_key(|it| it.len());
        cycles
    }

    /// Compute a collection of independent cycles of the given `parity` within the desired
    /// `restriction` space.
    ///
    /// Independent parity cycles are cycles that are disjoint but together cover every cycle
    /// of the desired parity in the graph. The method tries to maximize the number of the
    /// returned cycles, but the result is not guaranteed to be maximal.
    ///
    /// The cycles are expected to be sorted by length, but otherwise the result is not guaranteed
    /// to be deterministic.
    pub fn restricted_independent_parity_cycles(
        &self,
        restriction: &HashSet<VariableId>,
        parity: Sign,
    ) -> Vec<Vec<VariableId>> {
        let mut cycles = Vec::new();

        let mut components = self.restricted_strongly_connected_components(&restriction);
        while let Some(mut scc) = components.pop() {
            let mut best_cycle = None;
            let mut best_cycle_len = usize::MAX;
            // Not particularly efficient, but keeps this whole thing deterministic.
            let mut scc_iter: Vec<VariableId> = scc.iter().cloned().collect();
            scc_iter.sort();
            for x in &scc_iter {
                if let Some(cycle) = self.shortest_parity_cycle(&scc, *x, parity, best_cycle_len) {
                    if cycle.len() == 1 {
                        // Cycle of length one will always win, no need to check further.
                        best_cycle = Some(cycle);
                        break;
                    } else if cycle.len() < best_cycle_len {
                        best_cycle_len = cycle.len();
                        best_cycle = Some(cycle);
                    }
                }
            }

            if let Some(best_cycle) = best_cycle {
                for x in &best_cycle {
                    scc.remove(x);
                }
                cycles.push(best_cycle);
                components.append(&mut self.restricted_strongly_connected_components(&scc));
            }
        }

        cycles.sort_by_key(|it| it.len());
        cycles
    }
}

#[cfg(test)]
mod tests {
    use crate::_impl_regulatory_graph::signed_directed_graph::SdGraph;
    use crate::_impl_regulatory_graph::signed_directed_graph::Sign::{Negative, Positive};
    use crate::{RegulatoryGraph, VariableId};
    use std::collections::HashSet;

    #[test]
    pub fn test_independent_cycles() {
        // The same graph as used for testing of FVS algorithms.
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

        // c and a do not appear on any cycles.
        let _a = rg.find_variable("a").unwrap();
        let b_1 = rg.find_variable("b_1").unwrap();
        let b_2 = rg.find_variable("b_2").unwrap();
        let _c = rg.find_variable("c").unwrap();
        let d_1 = rg.find_variable("d_1").unwrap();
        let d_2 = rg.find_variable("d_2").unwrap();
        let d_3 = rg.find_variable("d_3").unwrap();
        let e = rg.find_variable("e").unwrap();

        let graph = SdGraph::from(&rg);

        let vertices = graph.mk_all_vertices();
        let ic = graph.restricted_independent_cycles(&vertices);
        let p_ic = graph.restricted_independent_parity_cycles(&vertices, Positive);
        let n_ic = graph.restricted_independent_parity_cycles(&vertices, Negative);

        let b_cycle = HashSet::from([b_1, b_2]);
        let d_pos_cycle = HashSet::from([d_1, d_2]);
        let d_neg_cycle = HashSet::from([d_1, d_2, d_3]);

        assert_eq!(ic.len(), 3);
        assert_eq!(p_ic.len(), 2);
        assert_eq!(n_ic.len(), 2);

        // e is the smallest positive (and overall) cycle
        assert_eq!(ic[0], vec![e]);
        assert_eq!(p_ic[0], vec![e]);
        // b_cycle is the smallest negative cycle
        assert_eq!(b_cycle, n_ic[0].iter().cloned().collect());

        // The second positive cycle is in the d component.
        assert_eq!(d_pos_cycle, p_ic[1].iter().cloned().collect());
        // And the second negative cycle is also in the d component.
        assert_eq!(d_neg_cycle, n_ic[1].iter().cloned().collect());

        // And for the general case, both cycles of length two are included.
        let ic_1: HashSet<VariableId> = ic[1].iter().cloned().collect();
        let ic_2: HashSet<VariableId> = ic[2].iter().cloned().collect();

        assert!(ic_1 == b_cycle || ic_2 == b_cycle);
        assert!(ic_1 == d_pos_cycle || ic_2 == d_pos_cycle);
    }
}
