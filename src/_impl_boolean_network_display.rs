use crate::{BooleanNetwork, ModelAnnotation};
use std::fmt::{Display, Error, Formatter};

impl Display for BooleanNetwork {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), Error> {
        let mut ann = ModelAnnotation::new();

        // Save the library version for later, and declare that we want basic integrity checks.
        ann.ensure_value(&["version", "lib_param_bn"], env!("CARGO_PKG_VERSION"));
        ann.ensure_value(&["check_declarations"], "true");

        // Write variable declarations:
        let variable_declarations = ann.ensure_child(&["variable"]);
        let var_names = self
            .variables()
            .map(|it| self.get_variable_name(it).clone())
            .collect::<Vec<_>>();
        // Write all variable names as a multi-line value.
        variable_declarations.write_multiline_value(&var_names);

        // Write parameter declarations:
        let function_declarations = ann.ensure_child(&["function"]);
        // Write names and arities together:
        for param in &self.parameters {
            let p_arity = function_declarations
                .ensure_child(&[param.name.as_str(), "arity"])
                .value_mut();
            *p_arity = Some(param.arity.to_string());
        }

        writeln!(f, "{}", ann)?;

        write!(f, "{}", self.graph)?;
        for var in self.variables() {
            // print all update functions
            if let Some(fun) = self.get_update_function(var) {
                writeln!(f, "${}: {}", self[var], fun.to_string(self))?;
            }
        }
        Ok(())
    }
}
