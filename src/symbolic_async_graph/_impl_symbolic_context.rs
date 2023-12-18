use crate::symbolic_async_graph::{FunctionTable, SymbolicContext};
use crate::{BinaryOp, BooleanNetwork, FnUpdate, ParameterId, VariableId, VariableIdIterator};
use biodivine_lib_bdd::op_function::{and, and_not};
use biodivine_lib_bdd::{
    bdd, Bdd, BddValuation, BddVariable, BddVariableSet, BddVariableSetBuilder,
};
use std::collections::HashMap;
use std::convert::TryInto;

impl SymbolicContext {
    /// Create a new `SymbolicContext` that encodes the given `BooleanNetwork`, but otherwise has
    /// no additional symbolic variables.
    pub fn new(network: &BooleanNetwork) -> Result<SymbolicContext, String> {
        Self::with_extra_state_variables(network, &HashMap::new())
    }

    /// Create a new `SymbolicContext` that is based on the given `BooleanNetwork`, but also
    /// contains additional symbolic variables associated with individual network variables.
    ///
    /// The "symbolic vs. network variable" association is used to provide a place for the
    /// additional variables in the BDD variable ordering. Specifically, the additional variables
    /// are placed directly *after* the corresponding state variable. Consequently, depending
    /// on the actual meaning of these extra variables, you might want to place them close to
    /// the "most related" state variable to reduce BDD size.
    ///
    /// Keep in mind that the total number of symbolic variables cannot exceed `u16::MAX`. The
    /// names of the extra variables will be `"{network_variable}_extra_{i}`, with `i` starting
    /// at zero (in case you want to reference them by name somewhere).
    pub fn with_extra_state_variables(
        network: &BooleanNetwork,
        extra: &HashMap<VariableId, u16>,
    ) -> Result<SymbolicContext, String> {
        // First, check if the network can be encoded using u16::MAX symbolic variables:
        let symbolic_size = network_symbolic_size(network, extra);
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
        let mut extra_state_variables: Vec<Vec<BddVariable>> = vec![Vec::new(); network.num_vars()];
        let mut implicit_function_tables: Vec<Option<FunctionTable>> =
            vec![None; network.num_vars()];
        let mut explicit_function_tables: Vec<Option<FunctionTable>> =
            vec![None; network.num_parameters()];

        for variable in network.variables() {
            let variable_name = network[variable].get_name();
            let state_variable = builder.make_variable(variable_name);
            state_variables.push(state_variable);
            // Create extra state variables.
            if let Some(extra_count) = extra.get(&variable).cloned() {
                for i in 0..extra_count {
                    let extra_name = format!("{}_extra_{}", network[variable].get_name(), i);
                    let extra_variable = builder.make_variable(extra_name.as_str());
                    extra_state_variables[variable.0].push(extra_variable);
                }
            }
            if let Some(update_function) = network.get_update_function(variable) {
                // For explicit function, go through all parameters used in the function.
                for parameter in update_function.collect_parameters() {
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

        // Create a "flattened" version of extra state variables.
        let mut all_extra_state_variables = Vec::new();
        for list in &extra_state_variables {
            all_extra_state_variables.append(&mut list.clone());
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
            extra_state_variables,
            all_extra_state_variables,
            parameter_variables,
            explicit_function_tables,
            implicit_function_tables,
        })
    }

    /// Obtain a [VariableId] of a state variable, assuming such state variable exists.
    pub fn find_network_variable(&self, name: &str) -> Option<VariableId> {
        self.bdd
            .var_by_name(name)
            .and_then(|bdd_var| self.find_state_variable(bdd_var))
    }

    /// Obtain the name of a specific state variable.
    pub fn get_network_variable_name(&self, variable: VariableId) -> String {
        self.bdd.name_of(self.state_variables[variable.to_index()])
    }

    /// Iterator over all [VariableId] network variables managed by this [SymbolicContext].
    pub fn network_variables(&self) -> VariableIdIterator {
        (0..self.num_state_variables()).map(VariableId::from_index)
    }

    /// Create a new [SymbolicContext] which is compatible with the current context (it uses the same
    /// [BddVariableSet]), but is missing the given [VariableId].
    ///
    /// The new context uses the same [ParameterId] identifiers as the old context, but has different
    /// [VariableId] identifiers, since one of the variables is no longer used, and [VariableId] identifiers
    /// must be always a contiguous sequence. You should use variable names to "translate" [VariableId] identifiers
    /// between the two symbolic context. Of course, [SymbolicContext::transfer_from] should also still work.
    ///
    /// Note that the extra state variables and parameter variables do not disappear, even if they are only used
    /// by the eliminated variable. However, you cannot access them using the normal methods
    /// (e.g. [SymbolicContext::get_extra_state_variable]), only through the full list
    /// (i.e. [SymbolicContext::all_extra_state_variables]).
    pub fn eliminate_network_variable(&self, variable: VariableId) -> SymbolicContext {
        let index = variable.to_index();
        let mut result = self.clone();
        // Remove the variable from all variable-indexed lists. The symbolic variables still remain in the
        // general lists though. Explicit parameters are unchanged.
        result.state_variables.remove(index);
        result.extra_state_variables.remove(index);
        result.implicit_function_tables.remove(index);
        result
    }

    /// The number of state variables (should be equal to the number of network variables).
    pub fn num_state_variables(&self) -> usize {
        self.state_variables.len()
    }

    /// The number of symbolic variables encoding network parameters.
    pub fn num_parameter_variables(&self) -> usize {
        self.parameter_variables.len()
    }

    /// The number of extra symbolic variables.
    pub fn num_extra_state_variables(&self) -> usize {
        self.all_extra_state_variables.len()
    }

    /// Provides access to the raw `Bdd` context.
    pub fn bdd_variable_set(&self) -> &BddVariableSet {
        &self.bdd
    }

    /// Getter for variables encoding the state variables of the network.
    pub fn state_variables(&self) -> &Vec<BddVariable> {
        &self.state_variables
    }

    /// Getter for variables encoding the parameter variables of the network.
    pub fn parameter_variables(&self) -> &Vec<BddVariable> {
        &self.parameter_variables
    }

    /// Get the list of all extra symbolic variables across all BN variables.
    pub fn all_extra_state_variables(&self) -> &Vec<BddVariable> {
        &self.all_extra_state_variables
    }

    /// Get the list of extra symbolic variables associated with a particular BN variable.
    pub fn extra_state_variables(&self, variable: VariableId) -> &Vec<BddVariable> {
        &self.extra_state_variables[variable.0]
    }

    /// Retrieve all extra symbolic variables associated with a particular offset across all
    /// network variables. If a variable does not have enough extra symbolic variables, it
    /// is not included in the result.
    pub fn extra_state_variables_by_offset(&self, offset: usize) -> Vec<(VariableId, BddVariable)> {
        let mut result = Vec::new();
        for i in 0..self.num_state_variables() {
            if offset <= self.extra_state_variables[i].len() {
                result.push((
                    VariableId::from_index(i),
                    self.extra_state_variables[i][offset],
                ));
            }
        }
        result
    }

    /// Get the `BddVariable` representing the network variable with the given `VariableId`.
    pub fn get_state_variable(&self, variable: VariableId) -> BddVariable {
        self.state_variables[variable.0]
    }

    /// Try to find a [VariableId] which corresponds to the given [BddVariable], assuming
    /// the [BddVariable] is one of the [Self::state_variables].
    pub fn find_state_variable(&self, symbolic_variable: BddVariable) -> Option<VariableId> {
        self.state_variables
            .iter()
            .position(|it| *it == symbolic_variable)
            .map(VariableId::from_index)
    }

    /// Get the `BddVariable` extra symbolic variable associated with a particular BN variable
    /// and an offset (within the domain of said variable).
    pub fn get_extra_state_variable(&self, variable: VariableId, offset: usize) -> BddVariable {
        self.extra_state_variables[variable.0][offset]
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

    /// Create a `Bdd` that is true when the given extra symbolic variable is true.
    pub fn mk_extra_state_variable_is_true(&self, variable: VariableId, offset: usize) -> Bdd {
        self.bdd
            .mk_var(self.extra_state_variables[variable.0][offset])
    }

    /// Create a `Bdd` that is true when given explicit uninterpreted function (aka parameter)
    /// is true for given arguments.
    pub fn mk_uninterpreted_function_is_true(
        &self,
        parameter: ParameterId,
        args: &[FnUpdate],
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
        let args = args.iter().map(|it| FnUpdate::Var(*it)).collect::<Vec<_>>();
        self.mk_function_table_true(table, &self.prepare_args(&args))
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
        let args = args.iter().map(|it| FnUpdate::Var(*it)).collect::<Vec<_>>();
        self.instantiate_function_table(valuation, table, &self.prepare_args(&args))
    }

    /// Create a `Bdd` which represents the instantiated explicit uninterpreted function.
    pub fn instantiate_uninterpreted_function(
        &self,
        valuation: &BddValuation,
        parameter: ParameterId,
        args: &[FnUpdate],
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

    /// Build a DNF representation of an instantiated update function (given as [Bdd]).
    pub fn mk_instantiated_fn_update(&self, valuation: &BddValuation, function: &Bdd) -> FnUpdate {
        let parameter_valuation = self
            .parameter_variables()
            .iter()
            .map(|it| (*it, valuation[*it]))
            .collect::<Vec<_>>();

        // This should fix all parameters to their respective values.
        let restricted = function.restrict(&parameter_valuation);

        FnUpdate::build_from_bdd(self, &restricted)
    }

    /// **(internal)** Utility method for converting `FnUpdate` arguments to `Bdd` arguments.
    fn prepare_args(&self, args: &[FnUpdate]) -> Vec<Bdd> {
        return args.iter().map(|v| self.mk_fn_update_true(v)).collect();
    }

    /// This is similar to [BddVariableSet::transfer_from], but applied at the level of
    /// symbolic contexts.
    ///
    /// Note that in theory, this method *can* translate between different types of symbolic
    /// objects (e.g. variable to parameter), but it requires that the two use equivalent names.
    /// Hence it is not really possible to create such situation organically, because state,
    /// parameter and extra variables are intentionally created with names that are incompatible.
    ///
    pub fn transfer_from(&self, bdd: &Bdd, ctx: &SymbolicContext) -> Option<Bdd> {
        self.bdd.transfer_from(bdd, &ctx.bdd)
    }
}

/// **(internal)** Compute the number of rows necessary to represent a function with given arity.
fn arity_to_row_count(arity: u32) -> u32 {
    1u32.checked_shl(arity).unwrap_or(u32::MAX)
}

/// **(internal)** Compute the number of symbolic variables necessary to represent
/// the given `network` (including the `extra` variables), or `u32::MAX` in the case
/// of an overflow.
///
/// Note that this actually *also* verifies that the arity of every function is at most `u16`,
/// because anything larger would trigger overflow anyway.
fn network_symbolic_size(network: &BooleanNetwork, extra: &HashMap<VariableId, u16>) -> u32 {
    let mut size: u32 = extra.values().map(|it| u32::from(*it)).sum();
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
    use crate::symbolic_async_graph::{SymbolicAsyncGraph, SymbolicContext};
    use crate::BooleanNetwork;
    use biodivine_lib_bdd::BddPartialValuation;
    use std::collections::{HashMap, HashSet};
    use std::convert::TryFrom;

    #[test]
    fn hmox_pathway() {
        let model = std::fs::read_to_string("aeon_models/hmox_pathway.aeon").unwrap();
        let network = BooleanNetwork::try_from(model.as_str()).unwrap();
        let graph = SymbolicAsyncGraph::new(&network).unwrap();
        assert!(!graph.unit_colored_vertices().is_empty());
    }

    #[test]
    fn test_extra_variables() {
        // The network doesn't really matter, we are only testing encoding of variables.
        let model = BooleanNetwork::try_from(
            r#"
            A -> B
            B -> C
            C -> A
        "#,
        )
        .unwrap();
        let a = model.as_graph().find_variable("A").unwrap();
        let b = model.as_graph().find_variable("B").unwrap();
        let c = model.as_graph().find_variable("C").unwrap();
        let extra_arity = HashMap::from([(a, 3), (c, 5)]);

        let ctx = SymbolicContext::with_extra_state_variables(&model, &extra_arity).unwrap();

        assert_eq!(3, ctx.num_state_variables());
        assert_eq!(6, ctx.num_parameter_variables());
        assert_eq!(8, ctx.num_extra_state_variables());

        // Check that all created variables are unique.
        let mut set = HashSet::new();
        for i in 0..3 {
            let var = ctx.get_extra_state_variable(a, i);
            assert!(set.insert(var));
        }
        for i in 0..5 {
            let var = ctx.get_extra_state_variable(c, i);
            assert!(set.insert(var));
        }

        let mut set2 = HashSet::new();
        for n_var in [a, b, c] {
            for b_var in ctx.extra_state_variables(n_var) {
                assert!(set2.insert(*b_var));
            }
        }

        assert_eq!(set, set2);
    }

    #[test]
    fn dual_encoding() {
        // The purpose of this test is just to have an example of a "dual" encoding that can be
        // useful for trap space computation. However, we are not really testing anything that
        // substantial.

        let bn = BooleanNetwork::try_from_file("aeon_models/g2a_instantiated.aeon").unwrap();

        // For each BN variable, we want to add two extra variables for the new "dual" encoding.
        let extra_variables = bn
            .variables()
            .map(|var| (var, 2))
            .collect::<HashMap<_, _>>();
        let ctx = SymbolicContext::with_extra_state_variables(&bn, &extra_variables).unwrap();

        // We separate the extra variables into "positive" and "negative" so that we can access
        // them later.
        let mut positive_encoded = Vec::new();
        let mut negative_encoded = Vec::new();
        for var in bn.variables() {
            let extra_variables = ctx.extra_state_variables(var);
            positive_encoded.push(extra_variables[0]);
            negative_encoded.push(extra_variables[1]);
        }

        // We also prepare a "reverse" mapping from symbolic state variables to BN variables,
        // so that we can tell which symbolic variable represents which BN variable.
        let reverse_state_variables = ctx
            .state_variables()
            .iter()
            .cloned()
            .zip(bn.variables())
            .collect::<HashMap<_, _>>();

        // A helper function which transforms a DNF clause based on normal "state" variables into
        // a DNF clause which uses the variables of our "dual" encoding.
        let remap_clause = |mut clause: BddPartialValuation| {
            for (bdd_var, is_positive) in clause.to_values() {
                let bn_variable = reverse_state_variables.get(&bdd_var).unwrap();
                let dual_variable = if is_positive {
                    positive_encoded[bn_variable.to_index()]
                } else {
                    negative_encoded[bn_variable.to_index()]
                };
                // Remove old "state" variable.
                clause.unset_value(bdd_var);
                // Add one of the "dual" variables.
                clause.set_value(dual_variable, true);
            }
            clause
        };

        // Now we can convert every function into positive condition (when a variable can
        // grow from 0 to 1) and negative condition (when a variable can fall from 1 to 0).
        for var in bn.variables() {
            let var_update = bn.get_update_function(var).as_ref().unwrap();
            let fn_bdd = ctx.mk_fn_update_true(var_update);

            let positive_dnf = fn_bdd.sat_clauses().map(remap_clause).collect::<Vec<_>>();
            let positive_bdd = ctx.bdd_variable_set().mk_dnf(&positive_dnf);

            // Do the same thing for negation to obtain the negative condition.
            let negative_dnf = fn_bdd
                .not()
                .sat_clauses()
                .map(remap_clause)
                .collect::<Vec<_>>();
            let negative_bdd = ctx.bdd_variable_set().mk_dnf(&negative_dnf);

            // In this particular test, we just assume these BDDs are not false, i.e.
            // every variable can sometimes grow and sometimes fall.
            assert!(!positive_bdd.is_false());
            assert!(!negative_bdd.is_false());
        }
    }
}
