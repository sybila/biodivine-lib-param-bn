use crate::symbolic_async_graph::{FunctionTable, SymbolicContext};
use crate::{BinaryOp, BooleanNetwork, FnUpdate, ParameterId, VariableId};
use biodivine_lib_bdd::op_function::{and, and_not};
use biodivine_lib_bdd::{
    bdd, Bdd, BddValuation, BddVariable, BddVariableSet, BddVariableSetBuilder,
};
use std::collections::HashSet;
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

        // The approach we take here is a bit arbitrary but overall appears to be usable.
        // 1. For every parameter, we compute a set of variables upon which it depends. These
        // are all variables that appear in any function that uses that particular parameter.
        // 2. Once all variables from a particular dependency set are created, we also create
        // the symbolic variables representing the particular parameter.

        // The reason for this is that in our encoding of uninterpreted functions,
        // ordering with `(variables, parameters)` leads to approx. `2^{variables}` BDD nodes,
        // while the reversed ordering `(parameters, variables)` leads to approx. `2^{parameters}`
        // BDD nodes. Since an uninterpreted function with `10` inputs will create `1024`
        // parameters, this would mean `2^{1024}` BDD nodes, which is unacceptable and must
        // be avoided at all cost.

        let mut state_variables: Vec<BddVariable> = Vec::new();
        let mut implicit_function_tables: Vec<Option<FunctionTable>> =
            vec![None; network.num_vars()];
        let mut explicit_function_tables: Vec<Option<FunctionTable>> =
            vec![None; network.num_parameters()];

        // Every explicit parameter with all the variables that
        // its call-site can possibly depend on.
        let mut pending_explicit = network
            .parameters()
            .map(|it| {
                let dependencies = network
                    .variables()
                    .filter(|var| {
                        if let Some(function) = network.get_update_function(*var) {
                            function.collect_parameters().contains(&it)
                        } else {
                            false
                        }
                    })
                    .flat_map(|var| network.as_graph().regulators(var))
                    .collect::<HashSet<_>>();
                (it, dependencies)
            })
            .collect::<Vec<_>>();
        // Every implicit parameter with the variables that it depends on.
        let mut pending_implicit = network
            .implicit_parameters()
            .into_iter()
            .map(|it| {
                let dependencies = network
                    .as_graph()
                    .regulators(it)
                    .into_iter()
                    .collect::<HashSet<_>>();
                (it, dependencies)
            })
            .collect::<Vec<_>>();

        // Note: This implementation is a bit wasteful, but it will not break if we were
        // to chose a different ordering of variables compared to the natural one.

        for variable in network.variables() {
            let state_variable = builder.make_variable(network.get_variable_name(variable));
            state_variables.push(state_variable);

            // Remove the variable from sets tracking dependencies.
            for (_, dependencies) in pending_explicit.iter_mut() {
                dependencies.remove(&variable);
            }
            for (_, dependencies) in pending_implicit.iter_mut() {
                dependencies.remove(&variable);
            }

            // Remove parameters for which all dependencies are already included,
            // and create BDD variables for said parameters.
            pending_explicit.retain(|(id, dependencies)| {
                if !dependencies.is_empty() {
                    true
                } else {
                    assert!(explicit_function_tables[id.0].is_none());
                    let parameter = &network[*id];
                    let arity: u16 = parameter.get_arity().try_into().unwrap();
                    let table = FunctionTable::new(parameter.get_name(), arity, &mut builder);
                    explicit_function_tables[id.0] = Some(table);
                    false
                }
            });
            pending_implicit.retain(|(id, dependencies)| {
                if !dependencies.is_empty() {
                    true
                } else {
                    assert!(implicit_function_tables[id.0].is_none());
                    let arity: u16 = network.regulators(*id).len().try_into().unwrap();
                    let name = format!("f_{}", network.get_variable_name(*id));
                    let table = FunctionTable::new(&name, arity, &mut builder);
                    implicit_function_tables[id.0] = Some(table);
                    false
                }
            });
        }

        assert!(pending_implicit.is_empty());
        assert!(pending_explicit.is_empty());

        let explicit_function_tables: Vec<FunctionTable> =
            explicit_function_tables.into_iter().flatten().collect();

        // Finally, collect all parameter BddVariables into one vector.
        let mut parameter_variables: Vec<BddVariable> = Vec::new();
        for table in &explicit_function_tables {
            for p in &table.rows {
                parameter_variables.push(*p);
            }
        }
        for table in implicit_function_tables.iter().flatten() {
            for p in &table.rows {
                parameter_variables.push(*p);
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
        &self.bdd
    }

    /// Getter for variables encoding the state variables of the network.
    pub fn state_variables(&self) -> &Vec<BddVariable> {
        &self.state_variables
    }

    /// Getter for the entire function table of an implicit update function.
    pub fn get_implicit_function_table(&self, variable: VariableId) -> &FunctionTable {
        let table = &self.implicit_function_tables[variable.0];
        let table = table.as_ref().unwrap_or_else(|| {
            panic!(
                "Variable {:?} does not have an implicit uninterpreted function.",
                variable
            );
        });
        table
    }

    /// Getter for the entire function table of an explicit parameter.
    pub fn get_explicit_function_table(&self, parameter: ParameterId) -> &FunctionTable {
        &self.explicit_function_tables[parameter.0]
    }

    /// Getter for variables encoding the parameter variables of the network.
    pub fn parameter_variables(&self) -> &Vec<BddVariable> {
        &self.parameter_variables
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
        args: &[VariableId],
    ) -> Bdd {
        let table = &self.explicit_function_tables[parameter.0];
        self.mk_function_table_true(table, &self.prepare_args(args))
    }

    /// Create a `Bdd` that is true when given implicit uninterpreted function is true for
    /// given arguments.
    ///
    /// Panic: Variable must have an implicit uninterpreted function.
    pub fn mk_implicit_function_is_true(&self, variable: VariableId, args: &[VariableId]) -> Bdd {
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
    fn mk_function_table_true(&self, function_table: &FunctionTable, args: &[Bdd]) -> Bdd {
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
        args: &[Bdd],
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
        args: &[VariableId],
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
        args: &[VariableId],
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
    fn prepare_args(&self, args: &[VariableId]) -> Vec<Bdd> {
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
        size = size.saturating_add(arity_to_row_count(arity))
    }
    for variable_id in network.variables() {
        if network.get_update_function(variable_id).is_none() {
            let arity: u32 = network
                .regulators(variable_id)
                .len()
                .try_into()
                .unwrap_or(u32::MAX);
            size = size.saturating_add(arity_to_row_count(arity))
        }
    }
    size
}

#[cfg(test)]
mod tests {
    use crate::biodivine_std::traits::Set;
    use crate::symbolic_async_graph::SymbolicAsyncGraph;
    use crate::BooleanNetwork;
    use std::convert::TryFrom;

    #[test]
    fn hmox_pathway() {
        let model = std::fs::read_to_string("aeon_models/hmox_pathway.aeon").unwrap();
        let network = BooleanNetwork::try_from(model.as_str()).unwrap();
        let graph = SymbolicAsyncGraph::new(network).unwrap();
        assert!(!graph.unit_colored_vertices().is_empty());
    }
}
