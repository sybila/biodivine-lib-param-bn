use crate::{SdGraph, VariableId};
use std::collections::HashSet;

impl SdGraph {
    /// The list of *non-trivial* weakly connected components in this graph.
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

        let pivot = restriction.iter().cloned().next().unwrap();

        let mut component = HashSet::from([pivot]);
        loop {
            let mut done = true;
            for x in component.clone() {
                for (s, _) in &self.successors[x.to_index()] {
                    if !component.contains(s) {
                        component.insert(*s);
                        done = false;
                    }
                }
                for (p, _) in &self.predecessors[x.to_index()] {
                    if !component.contains(p) {
                        component.insert(*p);
                        done = false;
                    }
                }
            }
            if done {
                break;
            }
        }

        let mut result = Vec::new();
        let new_restriction: HashSet<VariableId> =
            restriction.difference(&component).cloned().collect();

        if component.len() > 1 {
            result.push(component);
        }

        result.append(&mut self.restricted_weakly_connected_components(&new_restriction));

        result
    }
}
