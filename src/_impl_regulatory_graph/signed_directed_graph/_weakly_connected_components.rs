use crate::{LOG_NOTHING, SdGraph, VariableId, should_log};
use cancel_this::{Cancellable, is_cancelled};
use std::collections::HashSet;

impl SdGraph {
    /// The list of all weakly connected components in this graph.
    pub fn weakly_connected_components(&self) -> Vec<HashSet<VariableId>> {
        self.restricted_weakly_connected_components(&self.mk_all_vertices())
    }

    /// Weakly connected components within the sub-graph induced by the given `restriction` set.
    pub fn restricted_weakly_connected_components(
        &self,
        restriction: &HashSet<VariableId>,
    ) -> Vec<HashSet<VariableId>> {
        self._restricted_weakly_connected_components(restriction, LOG_NOTHING)
            .unwrap()
    }

    /// A version of [SdGraph::restricted_weakly_connected_components] with cancellation
    /// and logging.
    ///
    /// Cancellation implemented using [cancel-this](https://crates.io/crates/cancel-this).
    /// For more information, see crate documentation.
    pub fn _restricted_weakly_connected_components(
        &self,
        restriction: &HashSet<VariableId>,
        log_level: usize,
    ) -> Cancellable<Vec<HashSet<VariableId>>> {
        if restriction.is_empty() {
            return Ok(Vec::new());
        }

        let pivot = *restriction.iter().min().unwrap();

        let mut component = HashSet::from([pivot]);
        loop {
            let fwd = self.restricted_forward_reachable(restriction, component.clone());
            is_cancelled!()?;
            let bwd = self.restricted_backward_reachable(restriction, component.clone());
            is_cancelled!()?;
            if fwd.is_subset(&component) && bwd.is_subset(&component) {
                break;
            }
            component.extend(fwd);
            component.extend(bwd);
        }

        let mut result = Vec::new();
        let new_restriction: HashSet<VariableId> =
            restriction.difference(&component).cloned().collect();

        if should_log(log_level) {
            println!("Found weak component with {} vertices.", component.len());
        }

        result.push(component);
        result.append(
            &mut self._restricted_weakly_connected_components(&new_restriction, log_level)?,
        );

        Ok(result)
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

        let rg = RegulatoryGraph::try_from(
            r"
            a -> b
            b -> a
            a -> c
            c -> d
            d -> c
        ",
        )
        .unwrap();
        let sd = SdGraph::from(&rg);

        assert_eq!(sd.weakly_connected_components().len(), 1);
    }
}
