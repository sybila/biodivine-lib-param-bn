use crate::{BooleanNetwork, FnUpdate, Parameter, ParameterId, RegulatoryGraph, VariableId};
use std::collections::HashMap;

/// Basic methods for safely building `BooleanNetwork`s.
impl BooleanNetwork {
    /// Construct a new `BooleanNetwork` from a `RegulatoryGraph` without any parameters.
    pub fn new(graph: RegulatoryGraph) -> BooleanNetwork {
        return BooleanNetwork {
            update_functions: vec![None; graph.num_vars()],
            graph,
            parameters: Vec::new(),
            parameter_to_index: HashMap::new(),
        };
    }

    /// Add a new `Parameter` to the `BooleanNetwork`.
    ///
    /// The parameter name must be different from other parameters and variables.
    pub fn add_parameter(&mut self, name: &str, cardinality: usize) -> Result<ParameterId, String> {
        self.assert_no_such_variable(name)?;
        self.assert_no_such_parameter(name)?;
        let id = ParameterId(self.parameters.len());
        self.parameter_to_index.insert(name.to_string(), id);
        self.parameters.push(Parameter {
            name: name.to_string(),
            cardinality,
        });
        return Ok(id);
    }

    /// Add a new `UpdateFunction` to the `BooleanNetwork`.
    ///
    /// The variable must not already have an update function. We assume all the variables
    /// and parameters in the function are used correctly. If you are not sure how to safely
    /// build an instance of a `FnUpdate`, look at the variants of this method which parse
    /// the function safely from a string.
    pub fn add_update_function(
        &mut self,
        variable: VariableId,
        function: FnUpdate,
    ) -> Result<(), String> {
        self.assert_no_update_function(variable)?;
        self.assert_arguments_are_valid(variable, function.arguments())?;
        self.update_functions[variable.0] = Some(function);
        return Ok(());
    }

    /// **(internal)** Utility method to ensure that a parameter is also not a variable.
    fn assert_no_such_variable(&self, name: &str) -> Result<(), String> {
        return if self.graph.find_variable(name) == None {
            Ok(())
        } else {
            Err(format!(
                "Cannot add parameter. '{}' is already a variable.",
                name
            ))
        };
    }

    /// **(internal)** Utility method to ensure that a parameter is not a duplicate.
    fn assert_no_such_parameter(&self, name: &str) -> Result<(), String> {
        return if self.find_parameter(name) == None {
            Ok(())
        } else {
            Err(format!("Cannot add parameter. '{}' already added.", name))
        };
    }

    /// **(internal)** Utility method to ensure that an update function is not set yet.
    fn assert_no_update_function(&self, variable: VariableId) -> Result<(), String> {
        return if self.update_functions[variable.0] == None {
            Ok(())
        } else {
            Err(format!(
                "Cannot set update function for {}. Function already set.",
                self.graph.get_variable(variable)
            ))
        };
    }

    /// **(internal)** Utility method to check that the arguments of a function are a subset
    /// of the actual regulators.
    fn assert_arguments_are_valid(
        &self,
        variable: VariableId,
        actual: Vec<VariableId>,
    ) -> Result<(), String> {
        let expected = self.graph.regulators(variable);
        let mut i_expected = 0;
        let mut i_actual = 0;
        while i_expected < expected.len() && i_actual < actual.len() {
            if expected[i_expected] == actual[i_actual] {
                i_actual += 1;
            }
            i_expected += 1;
        }
        return if i_actual == actual.len() {
            Ok(())
        } else {
            let expected_names: Vec<String> = expected
                .into_iter()
                .map(|v| self.graph.get_variable(v).name.clone())
                .collect();
            let actual_names: Vec<String> = actual
                .into_iter()
                .map(|v| self.graph.get_variable(v).name.clone())
                .collect();
            let var_name = self.graph.get_variable(variable);
            Err(format!(
                "Variable '{}' is regulated by {:?}, but {:?} were found as arguments",
                var_name, expected_names, actual_names
            ))
        };
    }
}

/// Some utility methods for accessing the structure of a `BooleanNetwork`.
impl BooleanNetwork {
    /// Obtain a reference to the underlying `RegulatoryGraph` of the `BooleanNetwork`.
    pub fn graph(&self) -> &RegulatoryGraph {
        return &self.graph;
    }

    /// Find a `ParameterId` corresponding to the given parameter `name`.
    pub fn find_parameter(&self, name: &str) -> Option<ParameterId> {
        return self.parameter_to_index.get(name).map(|i| *i);
    }

    /// Get a `Parameter` corresponding to the given `ParameterId`.
    pub fn get_parameter(&self, id: ParameterId) -> &Parameter {
        return &self.parameters[id.0];
    }

    /// Get a `FnUpdate` corresponding to the given `VariableId`.
    pub fn get_update_function(&self, variable: VariableId) -> &Option<FnUpdate> {
        return &self.update_functions[variable.0];
    }
}
