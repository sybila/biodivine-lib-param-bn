use super::util::build_index_map;
use super::{Regulation, RegulatoryGraph, Variable, VariableId};

/// Methods for safely constructing new instances of `RegulatoryGraph`s.
impl RegulatoryGraph {
    /// Create a new `RegulatoryGraph` with variables using the given names
    /// and no regulations.
    ///
    /// The ordering of the variables is preserved.
    pub fn new(variables: Vec<String>) -> RegulatoryGraph {
        return RegulatoryGraph {
            regulations: Vec::new(),
            variable_to_index: build_index_map(&variables, |_, i| VariableId(i)),
            variables: variables
                .into_iter()
                .map(|name| Variable { name })
                .collect(),
        };
    }

    pub fn add_
}

/// Some basic utility methods for inspecting the `RegulatoryGraph`.
impl RegulatoryGraph {
    /// The number of variables in this `RegulatoryGraph`.
    pub fn num_vars(&self) -> usize {
        return self.variables.len();
    }

    /// Find a `VariableId` for the given name, or `None` if the variable does not exist.
    pub fn find_variable(&self, name: &str) -> Option<VariableId> {
        return self.variable_to_index.get(name).map(|id| *id);
    }

    /// Return a `Variable` corresponding to the given `VariableId`
    pub fn get_variable(&self, id: VariableId) -> &Variable {
        return &self.variables[id.0];
    }

    /// Find a `Regulation` between two variables if it exists, `None` otherwise.
    pub fn find_regulation(
        &self,
        regulator: VariableId,
        target: VariableId,
    ) -> Option<&Regulation> {
        for r in &self.regulations {
            if r.regulator == regulator && r.target == target {
                return Some(r);
            }
        }
        return None;
    }
}
