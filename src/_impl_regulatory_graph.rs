use super::{Regulation, RegulatoryGraph, Variable, VariableId};
use crate::biodivine_std::structs::build_index_map;
use crate::{Monotonicity, RegulationIterator, VariableIdIterator, ID_REGEX};
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
        if self.find_regulation(regulator, target) == None {
            Ok(())
        } else {
            Err(format!(
                "Invalid regulation: {} already regulates {}.",
                self.get_variable(regulator),
                self.get_variable(target)
            ))
        }
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
        for r in &self.regulations {
            if r.regulator == regulator && r.target == target {
                return Some(r);
            }
        }
        None
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

    /// Return the set of direct as well as transitive regulators of `target`.
    pub fn transitive_regulators(&self, target: VariableId) -> HashSet<VariableId> {
        let mut regulators = HashSet::new();
        fn r_regulators(
            rg: &RegulatoryGraph,
            target: VariableId,
            regulators: &mut HashSet<VariableId>,
        ) {
            for regulator in rg.regulators(target) {
                if regulators.insert(regulator) {
                    r_regulators(rg, regulator, regulators);
                }
            }
        }
        r_regulators(self, target, &mut regulators);
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

    /// Return a set of direct as well as transitive targets of `regulator`.
    pub fn transitive_targets(&self, regulator: VariableId) -> HashSet<VariableId> {
        let mut targets = HashSet::new();
        fn r_targets(
            rg: &RegulatoryGraph,
            regulator: VariableId,
            targets: &mut HashSet<VariableId>,
        ) {
            for target in rg.targets(regulator) {
                if targets.insert(target) {
                    r_targets(rg, target, targets);
                }
            }
        }
        r_targets(self, regulator, &mut targets);
        targets
    }

    /// Compute the strongly connected components of this regulatory graph. The components
    /// are sorted topologically based on their position in the graph condensation.
    ///
    ///
    /// When sorting topologically incomparable components, we use component size as
    /// the secondary criterion. Also, note that the algorithm is not particularly efficient,
    /// so it should be used on large networks with caution!
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
        return &self.get_variable(index);
    }
}

#[cfg(test)]
mod tests {
    use crate::{RegulatoryGraph, Variable, VariableId};
    use std::collections::HashSet;

    #[test]
    fn test_regulatory_graph() {
        // First, lets build a simple graph with 8 variables and 5 SCCs.
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

        assert!(rg.add_regulation("a", "c", false, None).is_err());
        assert!(rg.add_regulation("a", "b", true, None).is_err());
        assert!(rg.add_regulation("b_1", "a_1", true, None).is_err());

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
