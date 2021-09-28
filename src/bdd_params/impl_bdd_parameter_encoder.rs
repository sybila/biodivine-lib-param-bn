use super::BddParameterEncoder;
use crate::bdd_params::{BddParams, FunctionTableEntry};
use crate::biodivine_std::structs::IdState;
use crate::{BooleanNetwork, ParameterId, VariableId};
use biodivine_lib_bdd::{BddVariable, BddVariableSetBuilder, ValuationsOfClauseIterator};

const MAX_VARIABLES: usize = 8 * std::mem::size_of::<usize>();

impl BddParameterEncoder {
    /// Create a new `BddParameterEncoder` based on information given in a `BooleanNetwork`.
    pub fn new(bn: &BooleanNetwork) -> BddParameterEncoder {
        if bn.graph.num_vars() > MAX_VARIABLES {
            panic!(
                "Only up to {} variables supported by this parameter encoder.",
                MAX_VARIABLES
            );
        }
        let bdd = BddVariableSetBuilder::new();
        Self::new_with_custom_variables(bn, bdd)
    }

    /// Create a new `BddParameterEncoder` based on information given in a `BooleanNetwork`
    /// and with variables already provided via `BddVariableSetBuilder`.
    pub fn new_with_custom_variables(
        bn: &BooleanNetwork,
        mut bdd: BddVariableSetBuilder,
    ) -> BddParameterEncoder {
        BddParameterEncoder {
            regulators: Self::build_regulators_table(bn),
            explicit_function_tables: Self::build_explicit_function_table(bn, &mut bdd),
            implicit_function_tables: Self::build_implicit_function_table(bn, &mut bdd),
            bdd_variables: bdd.build(),
        }
    }

    /*
        These utility functions should probably have some separate module, like static constraint computation,
        but right now this is good enough...
    */

    pub(crate) fn build_explicit_function_table(
        network: &BooleanNetwork,
        bdd: &mut BddVariableSetBuilder,
    ) -> Vec<Vec<BddVariable>> {
        let mut table = Vec::new();
        for pid in network.parameters() {
            let p = network.get_parameter(pid);
            // Here, we abuse BddValuationIterator to go over all possible valuations
            // of function inputs.

            let p_vars = ValuationsOfClauseIterator::new_unconstrained(p.arity as u16)
                .map(|valuation| {
                    let bdd_name = format!("{}{}", p.name, valuation);
                    bdd.make_variable(&bdd_name)
                })
                .collect();

            table.push(p_vars);
        }
        table
    }

    pub(crate) fn build_implicit_function_table(
        network: &BooleanNetwork,
        bdd: &mut BddVariableSetBuilder,
    ) -> Vec<Vec<BddVariable>> {
        let mut table = Vec::new();
        for vid in network.graph.variables() {
            let v = network.graph.get_variable(vid);

            if network.get_update_function(vid).is_some() {
                table.push(Vec::new());
            } else {
                let args = network.graph.regulators(vid);
                let cardinality = args.len();

                // Note that if args are empty, one variable is still created because there is
                // an "empty" valuation.
                let p_vars = ValuationsOfClauseIterator::new_unconstrained(cardinality as u16)
                    .map(|valuation| {
                        let bdd_name = format!("\\{{{}}}{}", v.name, valuation);
                        bdd.make_variable(&bdd_name)
                    })
                    .collect();

                table.push(p_vars);
            }
        }
        table
    }

    pub(crate) fn build_regulators_table(network: &BooleanNetwork) -> Vec<Vec<VariableId>> {
        let mut table = Vec::new();
        for vid in network.graph.variables() {
            if network.get_update_function(vid).is_some() {
                table.push(Vec::new());
            } else {
                let args = network.graph.regulators(vid);
                table.push(args);
            }
        }
        table
    }

    /// A vector of entries in the table of a specific function.
    pub fn implicit_function_table(&self, target: VariableId) -> Vec<FunctionTableEntry> {
        let regulators = &self.regulators[target.0];
        let table = &self.implicit_function_tables[target.0];
        (0..table.len())
            .map(|i| FunctionTableEntry {
                table: target.0,
                entry_index: i,
                regulators,
            })
            .collect()
    }

    /// Get teh parameters which correspond to a specific table entry being one.
    pub fn get_implicit_for_table(&self, entry: &FunctionTableEntry) -> BddParams {
        let var = self.implicit_function_tables[entry.table][entry.entry_index];
        BddParams(self.bdd_variables.mk_var(var))
    }

    pub fn get_implicit_var_for_table(&self, entry: &FunctionTableEntry) -> BddVariable {
        self.implicit_function_tables[entry.table][entry.entry_index]
    }

    /// Find the `BddVariable` corresponding to the value of the `parameter` function
    /// in the given `state` assuming the specified `arguments`.
    pub fn get_explicit(
        &self,
        state: IdState,
        parameter: ParameterId,
        arguments: &[VariableId],
    ) -> BddVariable {
        let table_index = Self::compute_table_index(state, arguments);
        self.explicit_function_tables[parameter.0][table_index]
    }

    /// Make a `BddParams` set which corresponds to the valuations for which the value of
    /// `parameter` function given `arguments` is `true` in the given `state`.
    pub fn explicit_true_when(
        &self,
        state: IdState,
        parameter: ParameterId,
        arguments: &[VariableId],
    ) -> BddParams {
        let var = self.get_explicit(state, parameter, arguments);
        BddParams(self.bdd_variables.mk_var(var))
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
        self.implicit_function_tables[variable.0][table_index]
    }

    /// Make a `BddParams` set which corresponds to the valuations for which the value of
    /// an implicit update function of `variable` is true in the given `state`.
    pub fn implicit_true_when(&self, state: IdState, variable: VariableId) -> BddParams {
        let var = self.get_implicit(state, variable);
        BddParams(self.bdd_variables.mk_var(var))
    }

    // Compute which function table entry does the arguments correspond to in the given `state`.
    fn compute_table_index(state: IdState, args: &[VariableId]) -> usize {
        let mut table_index: usize = 0;
        for i in 0..args.len() {
            if state.get_bit(args[args.len() - 1 - i].0) {
                table_index += 1;
            }
            if i < args.len() - 1 {
                table_index <<= 1;
            }
        }
        table_index
    }
}

#[cfg(test)]
mod tests {
    use crate::bdd_params::BddParameterEncoder;
    use crate::biodivine_std::structs::IdState;
    use crate::BooleanNetwork;
    use crate::VariableId;
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
