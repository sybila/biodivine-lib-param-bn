use super::util::build_index_map;
use super::{Regulation, RegulatoryGraph, Variable, VariableId};
use crate::{Monotonicity, VariableIdIterator};

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

    /// Add a new `Regulation` to this `RegulatoryGraph`.
    ///
    /// Returns `Err` if `regulator` or `target` are not valid graph variables or when
    /// the regulation between the two variables already exists.
    pub fn add_regulation(
        &mut self,
        regulator: &str,
        target: &str,
        observable: bool,
        monotonicity: Option<Monotonicity>,
    ) -> Result<(), String> {
        let regulator = self.get_regulator(regulator)?;
        let target = self.get_target(target)?;
        self.assert_no_regulation(regulator, target)?;
        self.regulations.push(Regulation {
            regulator,
            target,
            observable,
            monotonicity,
        });
        return Ok(());
    }

    /// **(internal)** Utility method to safely obtain a regulator variable (using an appropriate error message).
    fn get_regulator(&self, name: &str) -> Result<VariableId, String> {
        return self
            .find_variable(name)
            .ok_or(format!("Invalid regulation: Unknown regulator {}.", name));
    }

    /// **(internal)** Utility method to safely obtain a target variable (using an appropriate error message).
    fn get_target(&self, name: &str) -> Result<VariableId, String> {
        return self
            .find_variable(name)
            .ok_or(format!("Invalid regulation: Unknown target {}.", name));
    }

    /// **(internal)** Utility method to ensure there is no regulation between the two variables yet.
    fn assert_no_regulation(
        &self,
        regulator: VariableId,
        target: VariableId,
    ) -> Result<(), String> {
        return if self.find_regulation(regulator, target) == None {
            Ok(())
        } else {
            Err(format!(
                "Invalid regulation: {} already regulates {}.",
                self.get_variable(regulator),
                self.get_variable(target)
            ))
        };
    }
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

    /// Return a `Variable` corresponding to the given `VariableId`.
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

    /// Return a sorted list of variables that regulate the given `target` variable.
    pub fn regulators(&self, target: VariableId) -> Vec<VariableId> {
        let mut regulators: Vec<VariableId> = self
            .regulations
            .iter()
            .filter(|r| r.target == target)
            .map(|r| r.regulator)
            .collect();
        regulators.sort();
        return regulators;
    }

    /// Return an iterator over all ids of this graph.
    pub fn variable_ids(&self) -> VariableIdIterator {
        return (0..self.variables.len()).map(|i| VariableId(i));
    }
}
