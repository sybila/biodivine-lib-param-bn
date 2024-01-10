use crate::{SdGraph, VariableId};
use std::collections::HashSet;

impl SdGraph {
    /// The list of all weakly connected components in this graph.
    pub fn weakly_connected_components(&self) -> Vec<HashSet<VariableId>> {
        self.restricted_strongly_connected_components(&self.mk_all_vertices())
    }

    /// Weakly connected components within the sub-graph induced by the given `restriction` set.
    pub fn restricted_weakly_connected_components(
        &self,
        restriction: &HashSet<VariableId>,
    ) -> Vec<HashSet<VariableId>> {
        if restriction.is_empty() {
            return Vec::new();
        }

        let pivot = *restriction.iter().min().unwrap();

        let mut component = HashSet::from([pivot]);
        loop {
            let fwd = self.restricted_forward_reachable(restriction, component.clone());
            let bwd = self.restricted_backward_reachable(restriction, component.clone());
            if fwd.is_subset(&component) && bwd.is_subset(&component) {
                break;
            }
            component.extend(fwd);
            component.extend(bwd);
        }

        let mut result = Vec::new();
        let new_restriction: HashSet<VariableId> =
            restriction.difference(&component).cloned().collect();

        result.push(component);
        result.append(&mut self.restricted_weakly_connected_components(&new_restriction));

        result
    }
}

#[cfg(test)]
mod tests {
    use crate::{RegulatoryGraph, SdGraph, VariableId};
    use std::collections::HashSet;

    #[test]
    fn test_weakly_connected() {
        let rg = RegulatoryGraph::try_from(
            r"
            a -> b
            b -> c
            c -> a
            d -> b
            c -> e
        ",
        )
        .unwrap();
        let sd = SdGraph::from(&rg);

        assert_eq!(sd.weakly_connected_components().len(), 1);
        let restriction =
            HashSet::from_iter([VariableId::from_index(3), VariableId::from_index(4)]);
        assert_eq!(
            sd.restricted_weakly_connected_components(&restriction)
                .len(),
            2
        );
    }
}
