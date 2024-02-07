use crate::_impl_regulatory_graph::signed_directed_graph::Sign::Positive;
use crate::_impl_regulatory_graph::signed_directed_graph::{SdGraph, Sign};
use crate::{Monotonicity, RegulatoryGraph, VariableId};
use std::collections::HashSet;
use Sign::Negative;

impl SdGraph {
    pub fn mk_all_vertices(&self) -> HashSet<VariableId> {
        let var_count = self.successors.len();
        (0..var_count).map(VariableId::from_index).collect()
    }
}

impl From<&RegulatoryGraph> for SdGraph {
    fn from(rg: &RegulatoryGraph) -> Self {
        let mut successors = Vec::new();
        let mut predecessors = Vec::new();
        for var in rg.variables() {
            let mut next_step = Vec::new();
            let mut prev_step = Vec::new();

            for target in rg.targets(var) {
                let monotonicity = rg.find_regulation(var, target).unwrap().monotonicity;
                if monotonicity != Some(Monotonicity::Activation) {
                    next_step.push((target, Negative));
                }
                if monotonicity != Some(Monotonicity::Inhibition) {
                    next_step.push((target, Positive));
                }
            }

            for regulator in rg.regulators(var) {
                let monotonicity = rg.find_regulation(regulator, var).unwrap().monotonicity;
                if monotonicity != Some(Monotonicity::Activation) {
                    prev_step.push((regulator, Negative));
                }
                if monotonicity != Some(Monotonicity::Inhibition) {
                    prev_step.push((regulator, Positive));
                }
            }

            // Variables should be well-ordered, but just in case...
            assert_eq!(var.to_index(), successors.len());

            successors.push(next_step);
            predecessors.push(prev_step);
        }
        SdGraph {
            successors,
            predecessors,
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::_impl_regulatory_graph::_impl_misc::tests::build_test_regulatory_graph;
    use crate::_impl_regulatory_graph::signed_directed_graph::SdGraph;

    #[test]
    pub fn basic_sd_graph_test() {
        let rg = build_test_regulatory_graph();
        let sd_graph = SdGraph::from(&rg);
        assert_eq!(sd_graph.successors.len(), rg.num_vars());
        assert_eq!(sd_graph.predecessors.len(), rg.num_vars());

        for regulator in rg.variables() {
            for target in rg.targets(regulator) {
                assert!(sd_graph.successors[regulator.to_index()]
                    .iter()
                    .any(|(it, _)| *it == target));
                assert!(sd_graph.predecessors[target.to_index()]
                    .iter()
                    .any(|(it, _)| *it == regulator));
            }
        }

        assert_eq!(sd_graph.mk_all_vertices(), rg.variables().collect());
    }
}
