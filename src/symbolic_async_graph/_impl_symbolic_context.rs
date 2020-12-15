use crate::symbolic_async_graph::{FunctionTable, SymbolicContext};
use crate::{BinaryOp, BooleanNetwork, FnUpdate, ParameterId, VariableId};
use biodivine_lib_bdd::op_function::{and, and_not};
use biodivine_lib_bdd::{
    bdd, Bdd, BddValuation, BddVariable, BddVariableSet, BddVariableSetBuilder,
};
use std::convert::TryInto;

impl SymbolicContext {
    /// Create a new `SymbolicContext` that is based on the given `BooleanNetwork`.
    pub fn new(network: &BooleanNetwork) -> Result<SymbolicContext, String> {
        // First, check if the network can be encoded using u16::MAX symbolic variables:
        let symbolic_size = network_symbolic_size(network);
        if symbolic_size >= u32::from(u16::MAX) {
            return Err(format!(
                "The network is too large. {} symbolic variables needed, but {} available.",
                symbolic_size,
                u16::MAX
            ));
        }

        let mut builder = BddVariableSetBuilder::new();

        // The order in which we create the symbolic variables is very important, because
        // Bdd cares about this a lot (in terms of efficiency).

        // The approach we take here is to first create Bdd state variable and the create all
        // parameter variables used in the update function of the state variable.
        // This creates "related" symbolic variables near each other.
        // We also do this in the topological order in which the variables appear
        // in the network, since this should make things easier as well...

        let mut state_variables: Vec<BddVariable> = Vec::new();
        let mut implicit_function_tables: Vec<Option<FunctionTable>> =
            vec![None; network.num_vars()];
        let mut explicit_function_tables: Vec<Option<FunctionTable>> =
            vec![None; network.num_parameters()];

        for variable in network.variables() {
            let variable_name = network[variable].get_name();
            let state_variable = builder.make_variable(&variable_name);
            state_variables.push(state_variable);
            if let Some(update_function) = network.get_update_function(variable) {
                // For explicit function, go through all parameters used in the function.
                for parameter in update_function.parameters() {
                    if explicit_function_tables[parameter.0].is_none() {
                        // Only compute if not already handled...
                        let parameter_function = &network[parameter];
                        let arity: u16 = parameter_function.get_arity().try_into().unwrap();
                        let function_table =
                            FunctionTable::new(parameter_function.get_name(), arity, &mut builder);
                        explicit_function_tables[parameter.0] = Some(function_table);
                    }
                }
            } else {
                // Implicit update function.
                let arity: u16 = network.regulators(variable).len().try_into().unwrap();
                let function_name = format!("f_{}", variable_name);
                let function_table = FunctionTable::new(&function_name, arity, &mut builder);
                implicit_function_tables[variable.0] = Some(function_table);
            }
        }

        // Check that all parameter tables are constructed - if not, raise integrity error.
        for i_p in 0..network.num_parameters() {
            if explicit_function_tables[i_p].is_none() {
                let parameter_name = network[ParameterId(i_p)].get_name();
                return Err(format!(
                    "Integrity error: Uninterpreted function {} declared but not used.",
                    parameter_name
                ));
            }
        }

        let explicit_function_tables: Vec<FunctionTable> = explicit_function_tables
            .into_iter()
            .filter_map(|x| x)
            .collect();

        // Finally, collect all parameter BddVariables into one vector.
        let mut parameter_variables: Vec<BddVariable> = Vec::new();
        for table in &explicit_function_tables {
            for p in &table.rows {
                parameter_variables.push(*p);
            }
        }
        for table in &implicit_function_tables {
            if let Some(table) = table {
                for p in &table.rows {
                    parameter_variables.push(*p);
                }
            }
        }

        Ok(SymbolicContext {
            bdd: builder.build(),
            state_variables,
            parameter_variables,
            explicit_function_tables,
            implicit_function_tables,
        })
    }

    /// Provides access to the raw `Bdd` context.
    pub fn bdd_variable_set(&self) -> &BddVariableSet {
        return &self.bdd;
    }

    /// Getter for variables encoding the state variables of the network.
    pub fn state_variables(&self) -> &Vec<BddVariable> {
        return &self.state_variables;
    }

    /// Getter for variables encoding the parameter variables of the network.
    pub fn parameter_variables(&self) -> &Vec<BddVariable> {
        return &self.parameter_variables;
    }

    /// Create a constant true/false `Bdd`.
    pub fn mk_constant(&self, value: bool) -> Bdd {
        if value {
            self.bdd.mk_true()
        } else {
            self.bdd.mk_false()
        }
    }

    /// Create a `Bdd` that is true when given network variable is true.
    pub fn mk_state_variable_is_true(&self, variable: VariableId) -> Bdd {
        self.bdd.mk_var(self.state_variables[variable.0])
    }

    /// Create a `Bdd` that is true when given explicit uninterpreted function (aka parameter)
    /// is true for given arguments.
    pub fn mk_uninterpreted_function_is_true(
        &self,
        parameter: ParameterId,
        args: &Vec<VariableId>,
    ) -> Bdd {
        let table = &self.explicit_function_tables[parameter.0];
        self.mk_function_table_true(table, &self.prepare_args(args))
    }

    /// Create a `Bdd` that is true when given implicit uninterpreted function is true for
    /// given arguments.
    ///
    /// Panic: Variable must have an implicit uninterpreted function.
    pub fn mk_implicit_function_is_true(
        &self,
        variable: VariableId,
        args: &Vec<VariableId>,
    ) -> Bdd {
        let table = &self.implicit_function_tables[variable.0];
        let table = table.as_ref().unwrap_or_else(|| {
            panic!(
                "Variable {:?} does not have an implicit uninterpreted function.",
                variable
            );
        });
        self.mk_function_table_true(table, &self.prepare_args(args))
    }

    /// Create a `Bdd` that is true when given `FnUpdate` evaluates to true.
    pub fn mk_fn_update_true(&self, function: &FnUpdate) -> Bdd {
        match function {
            FnUpdate::Const(value) => self.mk_constant(*value),
            FnUpdate::Var(id) => self.mk_state_variable_is_true(*id),
            FnUpdate::Not(inner) => self.mk_fn_update_true(inner).not(),
            FnUpdate::Param(id, args) => self.mk_uninterpreted_function_is_true(*id, args),
            FnUpdate::Binary(op, left, right) => {
                let l = self.mk_fn_update_true(left);
                let r = self.mk_fn_update_true(right);
                match op {
                    BinaryOp::And => l.and(&r),
                    BinaryOp::Or => l.or(&r),
                    BinaryOp::Xor => l.xor(&r),
                    BinaryOp::Imp => l.imp(&r),
                    BinaryOp::Iff => l.iff(&r),
                }
            }
        }
    }

    /// **(internal)** Create a `Bdd` that is true when given `FunctionTable` evaluates to true,
    /// assuming each argument is true when the corresponding `Bdd` in the `args` array is true.
    ///
    /// Note that this actually allows functions which do not have just variables as arguments.
    //  In the future we can use this to build truly universal uninterpreted functions.
    fn mk_function_table_true(&self, function_table: &FunctionTable, args: &Vec<Bdd>) -> Bdd {
        let mut result = self.bdd.mk_true();
        for (input_row, output) in function_table {
            let row_true = input_row
                .into_iter()
                .zip(args)
                .fold(self.bdd.mk_true(), |result, (i, arg)| {
                    Bdd::binary_op(&result, arg, if i { and } else { and_not })
                });
            let output_true = self.bdd.mk_var(output);
            result = bdd![result & (row_true => output_true)];
        }
        result
    }

    /// Create a `Bdd` which represents an instantiated function table.
    ///
    /// This means the `Bdd` only depends on variables which appear in `args` and the
    /// actual semantics to each row of the `FunctionTable` is assigned based on
    /// the given `valuation`.
    fn instantiate_function_table(
        &self,
        valuation: &BddValuation,
        function_table: &FunctionTable,
        args: &Vec<Bdd>,
    ) -> Bdd {
        let mut result = self.bdd.mk_false();
        for (input_row, output) in function_table {
            if valuation[output] {
                let input_bdd = input_row
                    .into_iter()
                    .zip(args)
                    .fold(self.bdd.mk_true(), |result, (i, arg)| {
                        Bdd::binary_op(&result, arg, if i { and } else { and_not })
                    });
                result = bdd![result | input_bdd];
            }
        }
        result
    }

    /// Create a `Bdd` which represents the instantiated implicit uninterpreted function.
    pub fn instantiate_implicit_function(
        &self,
        valuation: &BddValuation,
        variable: VariableId,
        args: &Vec<VariableId>,
    ) -> Bdd {
        let table = &self.implicit_function_tables[variable.0];
        let table = table.as_ref().unwrap_or_else(|| {
            panic!(
                "Variable {:?} does not have an implicit uninterpreted function.",
                variable
            );
        });
        self.instantiate_function_table(valuation, table, &self.prepare_args(args))
    }

    /// Create a `Bdd` which represents the instantiated explicit uninterpreted function.
    pub fn instantiate_uninterpreted_function(
        &self,
        valuation: &BddValuation,
        parameter: ParameterId,
        args: &Vec<VariableId>,
    ) -> Bdd {
        let table = &self.explicit_function_tables[parameter.0];
        self.instantiate_function_table(valuation, table, &self.prepare_args(args))
    }

    /// Create a `Bdd` which represents the instantiated `FnUpdate`.
    pub fn instantiate_fn_update(&self, valuation: &BddValuation, function: &FnUpdate) -> Bdd {
        match function {
            FnUpdate::Const(value) => self.mk_constant(*value),
            FnUpdate::Var(id) => self.mk_state_variable_is_true(*id),
            FnUpdate::Not(inner) => self.instantiate_fn_update(valuation, inner).not(),
            FnUpdate::Param(id, args) => {
                self.instantiate_uninterpreted_function(valuation, *id, args)
            }
            FnUpdate::Binary(op, left, right) => {
                let l = self.instantiate_fn_update(valuation, left);
                let r = self.instantiate_fn_update(valuation, right);
                match op {
                    BinaryOp::And => l.and(&r),
                    BinaryOp::Or => l.or(&r),
                    BinaryOp::Xor => l.xor(&r),
                    BinaryOp::Imp => l.imp(&r),
                    BinaryOp::Iff => l.iff(&r),
                }
            }
        }
    }

    /// **(internal)** Utility method for converting `VariableId` arguments to `Bdd` arguments.
    fn prepare_args(&self, args: &Vec<VariableId>) -> Vec<Bdd> {
        return args
            .iter()
            .map(|v| self.mk_state_variable_is_true(*v))
            .collect();
    }
}

/// **(internal)** Compute the number of rows necessary to represent a function with given arity.
fn arity_to_row_count(arity: u32) -> u32 {
    1u32.checked_shl(arity).unwrap_or(u32::MAX)
}

/// **(internal)** Compute the number of symbolic variables necessary to represent
/// the given `network`, or `u32::MAX` in case of overflow.
///
/// Note that this actually *also* verifies that arity of every function is at most u16, because
/// anything larger would trigger overflow anyway.
fn network_symbolic_size(network: &BooleanNetwork) -> u32 {
    let mut size: u32 = 0;
    for parameter_id in network.parameters() {
        let arity = network.get_parameter(parameter_id).arity;
        size = size
            .checked_add(arity_to_row_count(arity))
            .unwrap_or(u32::MAX);
    }
    for variable_id in network.variables() {
        if network.get_update_function(variable_id).is_none() {
            let arity: u32 = network
                .regulators(variable_id)
                .len()
                .try_into()
                .unwrap_or(u32::MAX);
            size = size
                .checked_add(arity_to_row_count(arity))
                .unwrap_or(u32::MAX);
        }
    }
    size
}

#[cfg(test)]
mod tests {
    use crate::symbolic_async_graph::SymbolicAsyncGraph;
    use crate::BooleanNetwork;
    use std::convert::TryFrom;

    #[test]
    fn hmox_pathway() {
        let model = std::fs::read_to_string("aeon_models/hmox_pathway.aeon").unwrap();
        let network = BooleanNetwork::try_from(model.as_str()).unwrap();
        let graph = SymbolicAsyncGraph::new(network).unwrap();
        assert!(!graph.unit_vertices().is_empty());
    }
}
