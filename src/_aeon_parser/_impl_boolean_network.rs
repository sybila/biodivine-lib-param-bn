use crate::_aeon_parser::FnUpdateTemp;
use crate::{BooleanNetwork, VariableId};
use std::convert::TryFrom;

/// Methods for parsing `BooleanNetwork`s from string representation.
impl BooleanNetwork {
    /// Add a new `UpdateFunction` to the `BooleanNetwork`. All variables and parameters
    /// must be already present in the network. Furthermore, all parameters must be used
    /// with their correct cardinality.
    pub fn add_string_update_function(
        &mut self,
        variable: &str,
        update_function: &str,
    ) -> Result<(), String> {
        let update_function = FnUpdateTemp::try_from(update_function)?;
        let update_function = *update_function.unknown_variables_to_parameters(&self.graph);
        self.add_template_update_function(variable, update_function)
    }

    /// **(internal)** Utility method used in other parts of the parser.
    pub(crate) fn add_template_update_function(
        &mut self,
        variable: &str,
        update_function: FnUpdateTemp,
    ) -> Result<(), String> {
        let variable = self.get_variable_for_name(variable)?;
        let update_function = *update_function.into_fn_update(self)?;
        self.add_update_function(variable, update_function)?;
        Ok(())
    }

    /// **(internal)** Utility method to safely obtain variable for the update function
    /// with appropriate error message.
    fn get_variable_for_name(&self, name: &str) -> Result<VariableId, String> {
        self.graph.find_variable(name).ok_or(format!(
            "Can't add update function for `{name}`. `{name}` is not a variable."
        ))
    }
}

#[cfg(test)]
mod tests {
    use crate::{BooleanNetwork, RegulatoryGraph};

    #[test]
    fn test_invalid_update_function() {
        let mut rg = RegulatoryGraph::new(vec!["a".to_string(), "b".to_string()]);
        rg.add_string_regulation("a -> b").unwrap();
        rg.add_string_regulation("b -| a").unwrap();

        let mut bn = BooleanNetwork::new(rg);
        bn.add_parameter("p", 0).unwrap();

        // unknown variable
        assert!(bn.add_string_update_function("c", "!a").is_err());
        bn.add_string_update_function("a", "p => b").unwrap();
        // duplicate function
        assert!(bn.add_string_update_function("a", "!a").is_err());
        // name clash
        assert!(bn.add_string_update_function("b", "a & a()").is_err());
        // cardinality clash
        assert!(bn.add_string_update_function("b", "p(a) => a").is_err());
        // missing regulation
        assert!(bn.add_string_update_function("b", "p(b) => a").is_err());
    }
}
