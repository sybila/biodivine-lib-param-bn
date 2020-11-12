use super::BddParameterEncoder;
use crate::bdd_params::{BddParams, FunctionTableEntry};
use crate::{BooleanNetwork, ParameterId, VariableId};
use biodivine_lib_bdd::{BddValuationIterator, BddVariable, BddVariableSetBuilder};
use biodivine_lib_std::IdState;

impl BddParameterEncoder {
    /// Create a new `BddParameterEncoder` based on information given in a `BooleanNetwork`.
    pub fn new(bn: &BooleanNetwork) -> BddParameterEncoder {
        let mut bdd = BddVariableSetBuilder::new();
        return new_with_custom_variables(bn, bdd);
    }

    /// Create a new `BddParameterEncoder` based on information given in a `BooleanNetwork`
    /// and with variables already provided via `BddVariableSetBuilder`.
    pub fn new_with_custom_variables(bn: &BooleanNetwork, mut bdd: &BddVariableSetBuilder) -> BddParameterEncoder {
        let mut explicit_function_tables: Vec<Vec<BddVariable>> = Vec::new();
        let mut implicit_function_tables: Vec<Vec<BddVariable>> = Vec::new();
        let mut regulators: Vec<Vec<VariableId>> = Vec::new();

        // First, create variables for all the explicit parameters:
        for pid in bn.parameter_ids() {
            let p = bn.get_parameter(pid);
            // Here, we abuse BddValuationIterator to go over all possible valuations
            // of function inputs.

            let p_vars = BddValuationIterator::new(p.cardinality as u16)
                .map(|valuation| {
                    let bdd_name = format!("{}{}", p.name, valuation);
                    bdd.make_variable(&bdd_name)
                })
                .collect();

            explicit_function_tables.push(p_vars);
        }

        // Then create values for anonymous parameters:
        for vid in bn.graph.variable_ids() {
            let v = bn.graph.get_variable(vid);

            if let Some(_) = bn.get_update_function(vid) {
                regulators.push(Vec::new());
                implicit_function_tables.push(Vec::new());
            } else {
                let args = bn.graph.regulators(vid);
                let cardinality = args.len();
                regulators.push(args);

                // Note that if args are empty, one variable is still created because there is
                // an "empty" valuation.
                let p_vars = BddValuationIterator::new(cardinality as u16)
                    .map(|valuation| {
                        let bdd_name = format!("\\{{{}}}{}", v.name, valuation);
                        bdd.make_variable(&bdd_name)
                    })
                    .collect();

                implicit_function_tables.push(p_vars);
            }
        }

        return BddParameterEncoder {
            bdd_variables: bdd.build(),
            regulators,
            explicit_function_tables,
            implicit_function_tables,
        };
    }

    /// A vector of entries in the table of a specific function.
    pub fn implicit_function_table(&self, target: VariableId) -> Vec<FunctionTableEntry> {
        let regulators = &self.regulators[target.0];
        let table = &self.implicit_function_tables[target.0];
        return (0..table.len())
            .map(|i| FunctionTableEntry {
                table: target.0,
                entry_index: i,
                regulators,
            })
            .collect();
    }

    /// Get teh parameters which correspond to a specific table entry being one.
    pub fn get_implicit_for_table(&self, entry: &FunctionTableEntry) -> BddParams {
        let var = self.implicit_function_tables[entry.table][entry.entry_index];
        return BddParams(self.bdd_variables.mk_var(var));
    }

    pub fn get_implicit_var_for_table(&self, entry: &FunctionTableEntry) -> BddVariable {
        return self.implicit_function_tables[entry.table][entry.entry_index];
    }

    /// Find the `BddVariable` corresponding to the value of the `parameter` function
    /// in the given `state` assuming the specified `arguments`.
    pub fn get_explicit(
        &self,
        state: IdState,
        parameter: ParameterId,
        arguments: &Vec<VariableId>,
    ) -> BddVariable {
        let table_index = Self::compute_table_index(state, arguments);
        return self.explicit_function_tables[parameter.0][table_index];
    }

    /// Make a `BddParams` set which corresponds to the valuations for which the value of
    /// `parameter` function given `arguments` is `true` in the given `state`.
    pub fn explicit_true_when(
        &self,
        state: IdState,
        parameter: ParameterId,
        arguments: &Vec<VariableId>,
    ) -> BddParams {
        let var = self.get_explicit(state, parameter, arguments);
        return BddParams(self.bdd_variables.mk_var(var));
    }

    /// Find the `BddVariable` corresponding to the value of the implicit update function
    /// of the given `variable` in the given `state`.
    pub fn get_implicit(&self, state: IdState, variable: VariableId) -> BddVariable {
        let regulators = &self.regulators[variable.0];
        let table = &self.implicit_function_tables[variable.0];
        if regulators.is_empty() && table.is_empty() {
            panic!(
                "Variable {:?} does not have an implicit update function.",
                variable
            );
        }
        if regulators.is_empty() {
            // if regulators are empty but table is not, this is a zero-regulator variable
            return table[0];
        }
        let table_index = Self::compute_table_index(state, regulators);
        return self.implicit_function_tables[variable.0][table_index];
    }

    /// Make a `BddParams` set which corresponds to the valuations for which the value of
    /// an implicit update function of `variable` is true in the given `state`.
    pub fn implicit_true_when(&self, state: IdState, variable: VariableId) -> BddParams {
        let var = self.get_implicit(state, variable);
        return BddParams(self.bdd_variables.mk_var(var));
    }

    // Compute which function table entry does the arguments correspond to in the given `state`.
    fn compute_table_index(state: IdState, args: &Vec<VariableId>) -> usize {
        let mut table_index: usize = 0;
        for i in 0..args.len() {
            if state.get_bit(args[args.len() - 1 - i].0) {
                table_index += 1;
            }
            if i < args.len() - 1 {
                table_index = table_index << 1;
            }
        }
        return table_index;
    }
}

#[cfg(test)]
mod tests {
    use crate::bdd_params::BddParameterEncoder;
    use crate::BooleanNetwork;
    use crate::VariableId;
    use biodivine_lib_std::IdState;
    use std::convert::TryFrom;

    #[test]
    fn explicit_parameter_encoder_test() {
        let network = BooleanNetwork::try_from(
            "
            a -> b
            a -| a
            b -> a
            $a: p(a,b) => q(b)
            $b: q(a)
        ",
        )
        .unwrap();
        let encoder = BddParameterEncoder::new(&network);

        let variables = encoder.bdd_variables.variables();
        assert_eq!(6, variables.len());

        let p = network.find_parameter("p").unwrap();
        let q = network.find_parameter("q").unwrap();

        // The order of parameters is not fixed, so we can't explicitly test exact BddVariables.
        // We can however test that all should appear.

        let mut actual_vars = Vec::new();
        actual_vars.push(encoder.get_explicit(
            IdState::from(0b00),
            p,
            &vec![VariableId(0), VariableId(1)],
        ));
        actual_vars.push(encoder.get_explicit(
            IdState::from(0b01),
            p,
            &vec![VariableId(0), VariableId(1)],
        ));
        actual_vars.push(encoder.get_explicit(
            IdState::from(0b10),
            p,
            &vec![VariableId(0), VariableId(1)],
        ));
        actual_vars.push(encoder.get_explicit(
            IdState::from(0b11),
            p,
            &vec![VariableId(0), VariableId(1)],
        ));
        actual_vars.push(encoder.get_explicit(IdState::from(0b00), q, &vec![VariableId(0)]));
        actual_vars.push(encoder.get_explicit(IdState::from(0b01), q, &vec![VariableId(0)]));
        actual_vars.sort();

        assert_eq!(variables, actual_vars);

        // Also, some basic identities should hold:

        let a = encoder.get_explicit(IdState::from(0b00), p, &vec![VariableId(1), VariableId(0)]);
        let b = encoder.get_explicit(IdState::from(0b00), p, &vec![VariableId(0), VariableId(1)]);
        assert_eq!(a, b);

        let a = encoder.get_explicit(IdState::from(0b10), p, &vec![VariableId(1), VariableId(0)]);
        let b = encoder.get_explicit(IdState::from(0b01), p, &vec![VariableId(0), VariableId(1)]);
        assert_eq!(a, b);

        let a = encoder.get_explicit(IdState::from(0b01), p, &vec![VariableId(1), VariableId(0)]);
        let b = encoder.get_explicit(IdState::from(0b10), p, &vec![VariableId(0), VariableId(1)]);
        assert_eq!(a, b);

        let a = encoder.get_explicit(IdState::from(0b11), p, &vec![VariableId(1), VariableId(0)]);
        let b = encoder.get_explicit(IdState::from(0b11), p, &vec![VariableId(0), VariableId(1)]);
        assert_eq!(a, b);

        let a = encoder.get_explicit(IdState::from(0b01), p, &vec![VariableId(1), VariableId(0)]);
        let b = encoder.get_explicit(IdState::from(0b01), p, &vec![VariableId(0), VariableId(1)]);
        assert_ne!(a, b);

        let a = encoder.get_explicit(IdState::from(0b00), q, &vec![VariableId(0)]);
        let b = encoder.get_explicit(IdState::from(0b10), q, &vec![VariableId(0)]);
        assert_eq!(a, b);

        let a = encoder.get_explicit(IdState::from(0b10), q, &vec![VariableId(1)]);
        let b = encoder.get_explicit(IdState::from(0b11), q, &vec![VariableId(1)]);
        assert_eq!(a, b);

        let a = encoder.get_explicit(IdState::from(0b00), q, &vec![VariableId(0)]);
        let b = encoder.get_explicit(IdState::from(0b01), q, &vec![VariableId(0)]);
        assert_ne!(a, b);
    }

    #[test]
    fn anonymous_parameter_encoder_test() {
        let network = BooleanNetwork::try_from(
            "
            a -> b
            a -| a
            b -> a
        ",
        )
        .unwrap();
        let encoder = BddParameterEncoder::new(&network);

        let variables = encoder.bdd_variables.variables();
        assert_eq!(6, variables.len());

        let a = network.graph.find_variable("a").unwrap();
        let b = network.graph.find_variable("b").unwrap();

        let mut actual_vars = Vec::new();
        actual_vars.push(encoder.get_implicit(IdState::from(0b00), a));
        actual_vars.push(encoder.get_implicit(IdState::from(0b01), a));
        actual_vars.push(encoder.get_implicit(IdState::from(0b10), a));
        actual_vars.push(encoder.get_implicit(IdState::from(0b11), a));
        actual_vars.push(encoder.get_implicit(IdState::from(0b00), b));
        actual_vars.push(encoder.get_implicit(IdState::from(0b01), b));
        actual_vars.sort();

        assert_eq!(variables, actual_vars);

        let v1 = encoder.get_implicit(IdState::from(0b10), b);
        let v2 = encoder.get_implicit(IdState::from(0b00), b);
        assert_eq!(v1, v2);

        let v1 = encoder.get_implicit(IdState::from(0b11), b);
        let v2 = encoder.get_implicit(IdState::from(0b01), b);
        assert_eq!(v1, v2);

        let v1 = encoder.get_implicit(IdState::from(0b01), b);
        let v2 = encoder.get_implicit(IdState::from(0b00), b);
        assert_ne!(v1, v2);
    }

    #[test]
    fn mixed_parameter_encoder_test() {
        let network = BooleanNetwork::try_from(
            "
            a -> b
            a -| a
            b -> a
            $a: b & p(a, b)
        ",
        )
        .unwrap();
        let encoder = BddParameterEncoder::new(&network);

        let variables = encoder.bdd_variables.variables();
        assert_eq!(6, variables.len());

        let p = network.find_parameter("p").unwrap();
        let b = network.graph.find_variable("b").unwrap();

        let mut actual_vars = Vec::new();
        actual_vars.push(encoder.get_explicit(
            IdState::from(0b00),
            p,
            &vec![VariableId(0), VariableId(1)],
        ));
        actual_vars.push(encoder.get_explicit(
            IdState::from(0b01),
            p,
            &vec![VariableId(0), VariableId(1)],
        ));
        actual_vars.push(encoder.get_explicit(
            IdState::from(0b10),
            p,
            &vec![VariableId(0), VariableId(1)],
        ));
        actual_vars.push(encoder.get_explicit(
            IdState::from(0b11),
            p,
            &vec![VariableId(0), VariableId(1)],
        ));
        actual_vars.push(encoder.get_implicit(IdState::from(0b01), b));
        actual_vars.push(encoder.get_implicit(IdState::from(0b00), b));
        actual_vars.sort();

        assert_eq!(variables, actual_vars);
    }
}
