use crate::biodivine_std::structs::build_index_map;
use crate::{Monotonicity, RegulationIterator, VariableIdIterator, ID_REGEX};
use crate::{Regulation, RegulatoryGraph, Variable, VariableId};
use std::cmp::Ordering;
use std::collections::HashSet;
use std::ops::Index;

/// Methods for safely constructing new instances of `RegulatoryGraph`s.
impl RegulatoryGraph {
    /// Create a new `RegulatoryGraph` with variables using the given names
    /// and no regulations.
    ///
    /// The ordering of the variables is preserved.
    pub fn new(variables: Vec<String>) -> RegulatoryGraph {
        let variable_set = variables.iter().collect::<HashSet<_>>();
        if variable_set.len() != variables.len() {
            panic!("Variables {:?} contain duplicates.", variables);
        }
        RegulatoryGraph {
            regulations: Vec::new(),
            variable_to_index: build_index_map(&variables, |_, i| VariableId(i)),
            variables: variables
                .into_iter()
                .map(|name| Variable { name })
                .collect(),
        }
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
        Ok(())
    }

    /// Remove a [Regulation] from this [RegulatoryGraph] assuming it exists.
    ///
    /// Note that if there is a [BooleanNetwork] that uses this graph internally, this can make some if its functions
    /// invalid if they depend on the existence of this regulation.
    pub fn remove_regulation(
        &mut self,
        regulator: VariableId,
        target: VariableId,
    ) -> Result<Regulation, String> {
        let index = self
            .regulations
            .iter()
            .position(|r| r.regulator == regulator && r.target == target);
        if let Some(index) = index {
            Ok(self.regulations.remove(index))
        } else {
            Err(format!(
                "Regulation ({:?}, {:?}) does not exist.",
                regulator, target
            ))
        }
    }

    /// Add a new regulation using the [Regulation] object.
    pub fn add_raw_regulation(&mut self, regulation: Regulation) -> Result<(), String> {
        self.assert_no_regulation(regulation.regulator, regulation.target)?;
        self.regulations.push(regulation);
        Ok(())
    }

    /// Set the name of a network variable. The name must not be used by any other variable.
    ///
    /// Note that you don't have to rename anything else in the network, since all other
    /// structures reference variables with ids.
    pub fn set_variable_name(&mut self, id: VariableId, name: &str) -> Result<(), String> {
        if self.find_variable(name).is_some() {
            Err(format!("Variable named `{}` already exists.", name))
        } else if let Some(variable) = self.variables.get_mut(id.0) {
            let mut name_string = name.to_string();
            std::mem::swap(&mut name_string, &mut variable.name);
            self.variable_to_index.remove(&name_string);
            self.variable_to_index.insert(name.to_string(), id);
            Ok(())
        } else {
            Err(format!("Unknown variable id: {:?}", id))
        }
    }

    /// **(internal)** Utility method to safely obtain a regulator variable (using an appropriate error message).
    fn get_regulator(&self, name: &str) -> Result<VariableId, String> {
        self.find_variable(name)
            .ok_or(format!("Invalid regulation: Unknown regulator {}.", name))
    }

    /// **(internal)** Utility method to safely obtain a target variable (using an appropriate error message).
    fn get_target(&self, name: &str) -> Result<VariableId, String> {
        self.find_variable(name)
            .ok_or(format!("Invalid regulation: Unknown target {}.", name))
    }

    /// **(internal)** Utility method to ensure there is no regulation between the two variables yet.
    fn assert_no_regulation(
        &self,
        regulator: VariableId,
        target: VariableId,
    ) -> Result<(), String> {
        if self.find_regulation(regulator, target).is_none() {
            Ok(())
        } else {
            Err(format!(
                "Invalid regulation: {} already regulates {}.",
                self.get_variable(regulator),
                self.get_variable(target)
            ))
        }
    }

    /// Copy the variable names from this graph into a separate vector.
    pub fn variable_names(&self) -> Vec<String> {
        self.variables.iter().map(|it| it.name.clone()).collect()
    }
}

/// Some basic utility methods for inspecting the `RegulatoryGraph`.
impl RegulatoryGraph {
    /// The number of variables in this `RegulatoryGraph`.
    pub fn num_vars(&self) -> usize {
        self.variables.len()
    }

    /// Find a `VariableId` for the given name, or `None` if the variable does not exist.
    pub fn find_variable(&self, name: &str) -> Option<VariableId> {
        self.variable_to_index.get(name).cloned()
    }

    /// Return a `Variable` corresponding to the given `VariableId`.
    pub fn get_variable(&self, id: VariableId) -> &Variable {
        &self.variables[id.0]
    }

    /// Shorthand for `self.get_variable(id).get_name()`.
    pub fn get_variable_name(&self, id: VariableId) -> &String {
        &self.variables[id.0].name
    }

    /// Find a `Regulation` between two variables if it exists, `None` otherwise.
    pub fn find_regulation(
        &self,
        regulator: VariableId,
        target: VariableId,
    ) -> Option<&Regulation> {
        self.regulations
            .iter()
            .find(|r| r.regulator == regulator && r.target == target)
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
        regulators
    }

    /// Return a sorted list of variables that are regulated by the given `regulator` variable.
    pub fn targets(&self, regulator: VariableId) -> Vec<VariableId> {
        let mut targets: Vec<VariableId> = self
            .regulations
            .iter()
            .filter(|r| r.regulator == regulator)
            .map(|r| r.target)
            .collect();
        targets.sort();
        targets
    }

    /// Compute the strongly connected components of this regulatory graph. The components
    /// are sorted topologically based on their position in the graph condensation.
    ///
    ///
    /// When sorting topologically incomparable components, we use component size as
    /// the secondary criterion. Also, note that the algorithm is not particularly efficient,
    /// so it should be used on large networks with caution!
    ///
    /// **Deprecated in favor of `strongly_connected_components`.
    #[deprecated]
    pub fn components(&self) -> Vec<HashSet<VariableId>> {
        let mut components = Vec::new();
        let mut remaining: HashSet<VariableId> = self.variables().collect();
        while let Some(pivot) = remaining.iter().cloned().next() {
            let regulators = self.transitive_regulators(pivot);
            let targets = self.transitive_targets(pivot);
            let mut component = HashSet::new();
            // Compute component as (regulators and targets) + pivot.
            component.extend(&regulators);
            component.retain(|v| targets.contains(v));
            component.insert(pivot);
            // Remove component from remaining.
            remaining.retain(|v| !component.contains(v));
            // And add it to result.
            components.push(component);
        }
        components.sort_by(|a, b| {
            let pivot_a = *a.iter().next().unwrap();
            let pivot_b = *b.iter().next().unwrap();
            if a.contains(&pivot_b) || b.contains(&pivot_a) {
                Ordering::Equal
            } else {
                let targets_a = self.transitive_targets(pivot_a);
                if targets_a.contains(&pivot_b) {
                    // There is a path from a to b, a < b, a is "smaller".
                    return Ordering::Less;
                }
                let targets_b = self.transitive_targets(pivot_b);
                if targets_b.contains(&pivot_a) {
                    // There is a path from b to a, b < a, a is "greater".
                    return Ordering::Greater;
                }
                // The components are not comparable - compare them based on size.
                a.len().cmp(&b.len())
            }
        });
        components
    }

    /// Return an iterator over all variable ids of this graph.
    pub fn variables(&self) -> VariableIdIterator {
        (0..self.variables.len()).map(VariableId)
    }

    /// Return an iterator over all regulations of this graph.
    pub fn regulations(&self) -> RegulationIterator {
        self.regulations.iter()
    }

    /// A static check that allows to verify validity of a variable name.
    pub fn is_valid_name(name: &str) -> bool {
        ID_REGEX.is_match(name)
    }
}

/// Allow indexing `RegulatoryGraph` using `VariableId` objects.
impl Index<VariableId> for RegulatoryGraph {
    type Output = Variable;

    fn index(&self, index: VariableId) -> &Self::Output {
        self.get_variable(index)
    }
}

#[cfg(test)]
pub mod tests {
    use crate::{RegulatoryGraph, Variable, VariableId};
    use std::collections::HashSet;

    /// **(test)** A utility method that returns a simple but non-trivial regulatory graph.
    pub fn build_test_regulatory_graph() -> RegulatoryGraph {
        /*
           The graph has three non-trivial SCCs: {b_1, b_2}, {d_1, d_2, d_3} and {e}.
           Then, between the SCCs, the reachability is as follows:
               * a -> c
               * b -> c
               * c -> d
               * c -> e
        */
        let names = vec!["a", "b_1", "b_2", "c", "d_1", "d_2", "d_3", "e"];
        let mut rg = RegulatoryGraph::new(names.into_iter().map(|s| s.to_string()).collect());
        rg.add_regulation("a", "c", true, None).unwrap();
        rg.add_regulation("b_1", "b_2", true, None).unwrap();
        rg.add_regulation("b_2", "b_1", true, None).unwrap();
        rg.add_regulation("b_2", "c", true, None).unwrap();
        rg.add_regulation("c", "d_2", true, None).unwrap();
        rg.add_regulation("c", "e", true, None).unwrap();
        rg.add_regulation("d_1", "d_3", true, None).unwrap();
        rg.add_regulation("d_3", "d_2", true, None).unwrap();
        rg.add_regulation("d_2", "d_1", true, None).unwrap();
        rg.add_regulation("d_1", "d_2", true, None).unwrap();
        rg.add_regulation("e", "e", true, None).unwrap();
        rg
    }

    #[test]
    fn test_rename() {
        let mut rg = RegulatoryGraph::new(vec!["a".to_string(), "b".to_string()]);
        let a = rg.find_variable("a").unwrap();
        rg.set_variable_name(a, "x1").unwrap();
        let x1 = rg.find_variable("x1").unwrap();
        assert_eq!(a, x1);

        assert!(rg.set_variable_name(a, "b").is_err());
        assert!(rg.set_variable_name(VariableId(5), "z").is_err());
    }

    #[test]
    fn test_regulatory_graph() {
        // First, lets build a simple graph with 8 variables and 5 SCCs.
        let mut rg = build_test_regulatory_graph();

        assert!(rg.add_regulation("a", "c", false, None).is_err());
        assert!(rg.add_regulation("a", "b", true, None).is_err());
        assert!(rg.add_regulation("b_1", "a_1", true, None).is_err());

        // a -> c
        assert!(rg.remove_regulation(VariableId(0), VariableId(3)).is_ok());
        assert!(rg.remove_regulation(VariableId(0), VariableId(3)).is_err());
        assert!(rg.add_regulation("a", "c", true, None).is_ok());

        assert_eq!(rg.num_vars(), 8);
        assert_eq!(rg.find_variable("b_1").unwrap(), VariableId(1));
        assert_eq!(
            rg.get_variable(VariableId(2)),
            &Variable {
                name: "b_2".to_string()
            }
        );
        assert_eq!(rg.get_variable_name(VariableId(2)), "b_2");
        assert!(rg.find_regulation(VariableId(0), VariableId(3)).is_some());
        assert_eq!(
            rg.regulators(VariableId(3)),
            vec![VariableId(0), VariableId(2)]
        );
        assert_eq!(
            rg.targets(VariableId(3)),
            vec![VariableId(5), VariableId(7)]
        );

        #[allow(deprecated)]
        let components = rg.components();
        let expected_components: Vec<HashSet<VariableId>> = vec![
            vec![VariableId(0)].into_iter().collect(),
            vec![VariableId(1), VariableId(2)].into_iter().collect(),
            vec![VariableId(3)].into_iter().collect(),
            vec![VariableId(7)].into_iter().collect(),
            vec![VariableId(4), VariableId(5), VariableId(6)]
                .into_iter()
                .collect(),
        ];
        assert_eq!(components, expected_components);
    }
}
