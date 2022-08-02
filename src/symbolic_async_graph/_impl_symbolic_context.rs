use crate::symbolic_async_graph::{FunctionTable, SymbolicContext};
use crate::{BinaryOp, BooleanNetwork, FnUpdate, ParameterId, VariableId};
use biodivine_lib_bdd::op_function::{and, and_not};
use biodivine_lib_bdd::{
    bdd, Bdd, BddValuation, BddVariable, BddVariableSet, BddVariableSetBuilder,
};
use std::cmp::min;
use std::convert::TryInto;
use std::fmt::{Debug, Formatter};

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
            let state_variable = builder.make_variable(variable_name);
            state_variables.push(state_variable);
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

    /// Get the `BddVariable` representing the network variable with the given `VariableId`.
    pub fn get_state_variable(&self, variable: VariableId) -> BddVariable {
        self.state_variables[variable.0]
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
                if l.size() > 1000 || r.size() > 1000 {
                    println!("Mk true: {} / {}", l.size(), r.size());
                }
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

    /// Create a `Bdd` object that is `true` exactly when the given `FnUpdate` evaluates to `true`.
    pub fn mk_fn_update_true_2(&self, function: &FnUpdate) -> Bdd {
        // It is dangerous to strictly follow the syntactic tree of the function, because
        // the efficiency then depends on the combination of function syntax and variable
        // ordering. Instead, this function implements a greedy approach where we build
        // a flattened syntactic tree and evaluate the smallest subtrees first.
        enum PartialEval {
            Bdd(Bdd),
            Not(Box<PartialEval>),
            // Only AND/OR can be vectors, other operators always have length 2.
            Op(BinaryOp, Vec<PartialEval>),
        }

        impl Debug for PartialEval {
            fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
                match self {
                    PartialEval::Bdd(x) => write!(f, "BDD({})", x.size()),
                    PartialEval::Not(inner) => write!(f, "NOT({:?})", inner),
                    PartialEval::Op(op, args) => {
                        write!(
                            f,
                            "OP({:?}){:?}",
                            op,
                            args.iter().map(|it| it).collect::<Vec<_>>()
                        )
                    }
                }
            }
        }

        impl PartialEval {
            fn is_op(&self, op: BinaryOp) -> bool {
                match self {
                    PartialEval::Bdd(_) => false,
                    PartialEval::Not(_) => false,
                    PartialEval::Op(it, _) => *it == op,
                }
            }

            fn args(self) -> Vec<PartialEval> {
                match self {
                    PartialEval::Op(_, args) => args,
                    _ => panic!("Cannot read args of Bdd/Negation node."),
                }
            }

            fn sort(&mut self) {
                if let PartialEval::Op(_, args) = self {
                    args.sort_by_cached_key(|it| match it {
                        PartialEval::Bdd(it) => it.size(),
                        _ => usize::MAX,
                    });
                    // Sort descending, so that pop returns smallest element.
                    args.reverse();
                }
            }

            fn distribute(self) -> (PartialEval, bool) {
                match self {
                    PartialEval::Bdd(x) => (PartialEval::Bdd(x), false),
                    PartialEval::Not(x) => {
                        let (x, c) = x.distribute();
                        (PartialEval::Not(Box::new(x)), c)
                    }
                    PartialEval::Op(BinaryOp::And, mut args) if args.len() == 2 => {
                        let (arg1, c1) = args.pop().unwrap().distribute();
                        let (arg2, c2) = args.pop().unwrap().distribute();
                        match (arg1, arg2) {
                            (PartialEval::Bdd(value), PartialEval::Op(BinaryOp::Or, or_args)) => {
                                let mut new_or_args = Vec::new();
                                for or_arg in or_args {
                                    new_or_args.push(PartialEval::Op(
                                        BinaryOp::And,
                                        vec![or_arg, PartialEval::Bdd(value.clone())],
                                    ))
                                }
                                (PartialEval::Op(BinaryOp::Or, new_or_args), true)
                            }
                            (PartialEval::Op(BinaryOp::Or, or_args), PartialEval::Bdd(value)) => {
                                let mut new_or_args = Vec::new();
                                for or_arg in or_args {
                                    new_or_args.push(PartialEval::Op(
                                        BinaryOp::And,
                                        vec![or_arg, PartialEval::Bdd(value.clone())],
                                    ))
                                }
                                (PartialEval::Op(BinaryOp::Or, new_or_args), true)
                            }
                            (arg1, arg2) => {
                                (PartialEval::Op(BinaryOp::And, vec![arg1, arg2]), c1 | c2)
                            }
                        }
                    }
                    PartialEval::Op(op, args) => {
                        let mut new_args = Vec::new();
                        let mut changed = false;
                        for arg in args {
                            let (arg, c) = arg.distribute();
                            if arg.is_op(op) && (op == BinaryOp::Or || op == BinaryOp::And) {
                                new_args.append(&mut arg.args());
                                changed = true;
                            } else {
                                new_args.push(arg);
                                changed = changed | c;
                            }
                        }
                        (PartialEval::Op(op, new_args), changed)
                    }
                }
            }

            fn eval_up_to(self, limit: usize) -> (PartialEval, bool) {
                match self {
                    PartialEval::Bdd(x) => (PartialEval::Bdd(x), false),
                    PartialEval::Not(inner) => {
                        // There is no point in delaying negation.
                        if let PartialEval::Bdd(inner) = *inner {
                            (PartialEval::Bdd(inner.not()), true)
                        } else {
                            let (inner, changed) = inner.eval_up_to(limit);
                            (PartialEval::Not(Box::new(inner)), changed)
                        }
                    }
                    PartialEval::Op(op, args) => {
                        assert!(args.len() >= 2);
                        // First, eval every child node in the AST, keeping track of changes.
                        let mut changed = false;
                        let mut new_args = Vec::new();
                        for arg in args {
                            let (a, c) = arg.eval_up_to(limit);
                            changed = changed | c;
                            new_args.push(a);
                        }
                        // Then inspect last two arguments.
                        let mut args = new_args;
                        let arg1 = &args[args.len() - 1];
                        let arg2 = &args[args.len() - 2];
                        match (arg1, arg2) {
                            (PartialEval::Bdd(x), PartialEval::Bdd(y))
                                if x.size() + y.size() < limit =>
                            {
                                // If the last two args are BDDs and they are small enough,
                                // we can evaluate them and mark the result as changed.
                                let bdd = match op {
                                    BinaryOp::And => x.and(y),
                                    BinaryOp::Or => x.or(y),
                                    BinaryOp::Xor => x.xor(y),
                                    BinaryOp::Iff => x.iff(y),
                                    BinaryOp::Imp => x.imp(y),
                                };
                                if bdd.size() > 1000 {
                                    println!("{} + {} = {}", x.size(), y.size(), bdd.size());
                                }
                                args.pop();
                                args.pop();
                                args.push(PartialEval::Bdd(bdd));
                                changed = true;
                            }
                            _ => {
                                // Else do nothing.
                            }
                        }
                        let partial = if args.len() < 2 {
                            // If only one arg is remaining, this arg is the result.
                            assert!(args.len() > 0);
                            args.pop().unwrap()
                        } else {
                            let mut partial = PartialEval::Op(op, args);
                            partial.sort();
                            partial
                        };

                        (partial, changed)
                    }
                }
            }
        }

        fn mk_partial_eval(ctx: &SymbolicContext, function: &FnUpdate) -> PartialEval {
            match function {
                FnUpdate::Const(value) => PartialEval::Bdd(ctx.mk_constant(*value)),
                FnUpdate::Var(id) => PartialEval::Bdd(ctx.mk_state_variable_is_true(*id)),
                FnUpdate::Param(id, args) => {
                    PartialEval::Bdd(ctx.mk_uninterpreted_function_is_true(*id, args))
                }
                FnUpdate::Not(inner) => PartialEval::Not(Box::new(mk_partial_eval(ctx, inner))),
                FnUpdate::Binary(op, left, right) => {
                    let mut partial = if *op == BinaryOp::And || *op == BinaryOp::Or {
                        // Try to flatten And/Or operations
                        let mut args = Vec::new();
                        let left = mk_partial_eval(ctx, left);
                        if left.is_op(*op) {
                            args.append(&mut left.args());
                        } else {
                            args.push(left);
                        }
                        let right = mk_partial_eval(ctx, right);
                        if right.is_op(*op) {
                            args.append(&mut right.args());
                        } else {
                            args.push(right);
                        }

                        PartialEval::Op(*op, args)
                    } else {
                        let left = mk_partial_eval(ctx, left);
                        let right = mk_partial_eval(ctx, right);
                        PartialEval::Op(*op, vec![left, right])
                    };
                    partial.sort();
                    partial
                }
            }
        }

        let mut eval = mk_partial_eval(&self, function);

        let mut limit = 1024;
        loop {
            let (r, changed) = eval.eval_up_to(limit);
            eval = r;
            if !changed {
                let (r, changed) = eval.distribute();
                eval = r;
                if !changed {
                    limit = 2 * limit;
                    println!("New limit: {}", limit);
                } else {
                    println!("Distribute as {:?}", eval);
                }
            }
            println!("Eval: {:?}", eval);
            if let PartialEval::Bdd(x) = eval {
                println!("Result size: {}", x.size());
                /*if limit > 1_000_000 {
                    panic!("");
                }*/
                return x;
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
