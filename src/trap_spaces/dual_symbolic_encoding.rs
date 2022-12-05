use crate::symbolic_async_graph::FunctionTable;
use crate::trap_spaces::{ExtendedBoolean, Space};
use crate::{BinaryOp, BooleanNetwork, FnUpdate, ParameterId, VariableId};
use biodivine_lib_bdd::{Bdd, BddVariable, BddVariableSet, BddVariableSetBuilder};

pub struct DualSymbolicContext {
    bdd: BddVariableSet,
    state_variables: Vec<(BddVariable, BddVariable)>,
    parameter_variables: Vec<BddVariable>,
    explicit_function_tables: Vec<FunctionTable>,
    implicit_function_tables: Vec<Option<FunctionTable>>,
}

pub struct Colors {
    bdd: Bdd,
}

pub struct Vertices {
    bdd: Bdd,
}

pub struct ColoredVertices {
    bdd: Bdd,
}

pub struct SymbolicMostPermissiveGraph {
    network: BooleanNetwork,
    symbolic_context: DualSymbolicContext,
    // Empty and unit vertex set.
    vertex_space: (ColoredVertices, ColoredVertices),
    // Empty and unit color set.
    color_space: (Colors, Colors),
    // General symbolic unit bdd.
    unit_bdd: Bdd,
    // For every variable, we store a Bdd of nodes where `p_var` can increase, and where `n_var`
    // can increase.
    update_functions: Vec<(Bdd, Bdd)>,
}

impl SymbolicMostPermissiveGraph {
    pub fn new(network: BooleanNetwork) -> Result<SymbolicMostPermissiveGraph, String> {
        let context = DualSymbolicContext::new(&network)?;

        // For now, we don't apply regulation constraints... once we test the rest, we can port that.
        // So right now, we only require that state variables describe a state or a trap.
        let mut unit_bdd = context.bdd.mk_true();
        for var in network.variables() {
            let (p_var, n_var) = context.state_variables[var.to_index()];
            let p_var = context.bdd.mk_var(p_var);
            let n_var = context.bdd.mk_var(n_var);
            unit_bdd = unit_bdd.and(&p_var.or(&n_var));
        }

        let update_functions: Vec<(Bdd, Bdd)> = network
            .graph
            .variables()
            .map(|variable| {
                if let Some(function) = network.get_update_function(variable) {
                    let negation = function.clone().negation();
                    let can_be_one = context.mk_update_can_become_one(function);
                    let can_be_zero = context.mk_update_can_become_one(&negation);
                    let (p_var, n_var) = context.state_variables()[variable.to_index()];
                    let p_var = context.bdd_variable_set().mk_var(p_var);
                    let n_var = context.bdd_variable_set().mk_var(n_var);
                    (can_be_one.and_not(&p_var), can_be_zero.and_not(&n_var))
                } else {
                    unimplemented!("Implicit update functions are not implemented yet.")
                }
            })
            .collect();

        Ok(SymbolicMostPermissiveGraph {
            vertex_space: (
                ColoredVertices {
                    bdd: context.bdd.mk_false(),
                },
                ColoredVertices {
                    bdd: unit_bdd.clone(),
                },
            ),
            color_space: (
                Colors {
                    bdd: context.bdd.mk_false(),
                },
                Colors {
                    bdd: unit_bdd.clone(),
                },
            ),
            symbolic_context: context,
            unit_bdd,
            network,
            update_functions,
        })
    }

    pub fn fixed_points(&self) -> Bdd {
        let mut to_merge = Vec::new();
        to_merge.push(self.unit_bdd.clone());
        //let mut result = self.unit_bdd.clone();
        for var in self.network.variables() {
            //let (p_var, n_var) = &self.symbolic_context.state_variables[var.to_index()];
            //let p_var = self.symbolic_context.bdd.mk_var(*p_var);
            //let n_var = self.symbolic_context.bdd.mk_var(*n_var);
            let (fn_one, fn_zero) = &self.update_functions[var.to_index()];
            to_merge.push(fn_one.not());
            to_merge.push(fn_zero.not());
            /*result = result.and_not(fn_one);
            result = result.and_not(fn_zero);
            println!("[{:?}] Result: {}/{}", var, result.size(), result.cardinality());
            if result.size() > 100_000 {
                panic!();
            }*/
        }

        while to_merge.len() > 1 {
            to_merge.sort_by_key(|it| it.size());
            to_merge.reverse();

            println!(
                "[{}] Range {}-{}",
                to_merge.len(),
                to_merge.first().unwrap().size(),
                to_merge.last().unwrap().size()
            );

            let item = to_merge.pop().unwrap();
            for x in to_merge.iter_mut() {
                *x = x.and(&item);
            }
        }

        let result = to_merge.into_iter().next().unwrap();
        println!("Result: {}/{}", result.size(), result.cardinality());
        result
        /*for var in self.network.variables() {
            print!("{} ", self.network.get_variable_name(var));
        }
        println!();
        for x in result.sat_valuations() {
            let mut space = Space::new(&self.network);
            for var in self.network.variables() {
                let (p_var, n_var) = self.symbolic_context.state_variables[var.to_index()];
                match (x.value(p_var), x.value(n_var)) {
                    (true, true) => {},
                    (true, false) => space[var] = ExtendedBoolean::One,
                    (false, true) => space[var] = ExtendedBoolean::Zero,
                    (false, false) => panic!(),
                }
            }
            assert!(space.is_trap_space(&self.network), "{}", space);
            //println!("{}", space);
        }
        println!("All results are traps.");*/
        /*for var in self.network.variables() {
            let (p_var, n_var) = &self.symbolic_context.state_variables[var.to_index()];
            let p_var = self.symbolic_context.bdd.mk_var(*p_var);
            let n_var = self.symbolic_context.bdd.mk_var(*n_var);
            result = result.and_not(&p_var.and(&n_var));
        }
        println!("Remaining: {}", result.cardinality());*/
    }

    pub fn var_post(&self, var: VariableId, set: ColoredVertices) -> ColoredVertices {
        let (p_var, n_var) = &self.symbolic_context.state_variables[var.to_index()];
        let (fn_one, fn_zero) = &self.update_functions[var.to_index()];
        let bump_one = Bdd::fused_binary_flip_op(
            (&set.bdd, None),
            (fn_one, None),
            Some(*p_var),
            biodivine_lib_bdd::op_function::and,
        );
        let bump_zero = Bdd::fused_binary_flip_op(
            (&set.bdd, None),
            (fn_zero, None),
            Some(*n_var),
            biodivine_lib_bdd::op_function::and,
        );
        ColoredVertices {
            bdd: bump_zero.or(&bump_one),
        }
    }
}

impl DualSymbolicContext {
    pub fn new(network: &BooleanNetwork) -> Result<DualSymbolicContext, String> {
        let mut builder = BddVariableSetBuilder::new();

        let mut state_variables: Vec<(BddVariable, BddVariable)> = Vec::new();
        let mut implicit_function_tables: Vec<Option<FunctionTable>> =
            vec![None; network.num_vars()];
        let mut explicit_function_tables: Vec<Option<FunctionTable>> =
            vec![None; network.num_parameters()];

        for variable in network.variables() {
            let variable_name = network[variable].get_name();
            let p_state_variable = builder.make_variable(format!("p_{}", variable_name).as_str());
            let n_state_variable = builder.make_variable(format!("n_{}", variable_name).as_str());
            state_variables.push((p_state_variable, n_state_variable));
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
            for p in table.symbolic_variables() {
                parameter_variables.push(*p);
            }
        }
        for table in implicit_function_tables.iter().flatten() {
            for p in table.symbolic_variables() {
                parameter_variables.push(*p);
            }
        }

        Ok(DualSymbolicContext {
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
    pub fn state_variables(&self) -> &Vec<(BddVariable, BddVariable)> {
        &self.state_variables
    }

    /// Get the positive and negative `BddVariable` representing the network variable
    /// with the given `VariableId`.
    pub fn get_state_variable(&self, variable: VariableId) -> (BddVariable, BddVariable) {
        self.state_variables[variable.to_index()]
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
    ///
    /// Keep in mind that in this encoding, you can't really do negations though! (Or, you can,
    /// but they might not what you'd expect) So make sure the thing you are doing is what
    /// you want to be doing.
    pub fn mk_state_variable_literal(&self, variable: VariableId, value: ExtendedBoolean) -> Bdd {
        let (p_var, n_var) = self.state_variables[variable.to_index()];
        let (p_val, n_val) = match value {
            ExtendedBoolean::One => (true, false),
            ExtendedBoolean::Zero => (false, true),
            ExtendedBoolean::Any => (true, true),
        };
        let p = self.bdd.mk_literal(p_var, p_val);
        let n = self.bdd.mk_literal(n_var, n_val);
        p.and(&n)
    }

    /// Return a BDD which is true exactly when the given `update` *can* be true. I.e., for inputs
    /// `x`, which are states, we have `x \in result <=> f(x)`. For inputs `s` which are spaces,
    /// we have that `s \in result <=> \exists x \in s. f(x)`.
    ///
    /// Right now, not everything is supported (in particular, uninterpreted functions)
    pub fn mk_update_can_become_one(&self, update: &FnUpdate) -> Bdd {
        // Remove all operators other than and/or/not, and distribute negation such that it
        // only appears on literals.
        let update = update.to_and_or_normal_form().distribute_negation();

        /// Record which literals appear in the function. For monotonous variables,
        /// we should see one, but not the other.
        fn check_literals(update: &FnUpdate, observed: &mut [(bool, bool)]) {
            match update {
                FnUpdate::Const(_) => (),
                FnUpdate::Param(_, _) => (),
                FnUpdate::Var(x) => {
                    // Positive literal.
                    observed[x.to_index()].0 = true;
                }
                FnUpdate::Not(inner) => {
                    if let Some(x) = inner.as_var() {
                        // Negative literal.
                        observed[x.to_index()].1 = true;
                    } else if let Some((_, _)) = inner.as_param() {
                        // Do nothing for negative parameter literals.
                    } else {
                        unreachable!("Negation elimination did not occur.")
                    }
                }
                FnUpdate::Binary(_, left, right) => {
                    check_literals(left, observed);
                    check_literals(right, observed);
                }
            }
        }

        let mut literals = vec![(false, false); self.state_variables.len()];
        check_literals(&update, &mut literals);
        for (p, n) in literals {
            if p && n {
                unimplemented!("Non-monotonous function detected.");
            }
        }

        // Now we know that update is and-or function with only monotonous inputs.

        fn build_bdd(ctx: &DualSymbolicContext, update: &FnUpdate) -> Bdd {
            match update {
                FnUpdate::Const(value) => ctx.mk_constant(*value),
                FnUpdate::Var(var) => {
                    // Positive literal = p_var
                    ctx.bdd.mk_var(ctx.state_variables[var.to_index()].0)
                }
                FnUpdate::Not(inner) => {
                    if let Some(var) = inner.as_var() {
                        // Negative literal = n_var
                        ctx.bdd.mk_var(ctx.state_variables[var.to_index()].1)
                    } else if let Some((id, args)) = inner.as_param() {
                        // Negative parameter literal
                        if args.is_empty() {
                            let var =
                                ctx.explicit_function_tables[id.to_index()].symbolic_variables()[0];
                            ctx.bdd.mk_literal(var, false)
                        } else {
                            unimplemented!("Non-zero arity parameters are not implemented.");
                        }
                    } else {
                        unreachable!("Negation elimination did not occur.")
                    }
                }
                FnUpdate::Param(id, args) => {
                    if args.is_empty() {
                        let var =
                            ctx.explicit_function_tables[id.to_index()].symbolic_variables()[0];
                        ctx.bdd.mk_literal(var, true)
                    } else {
                        unimplemented!("Non-zero arity parameters are not implemented.");
                    }
                }
                FnUpdate::Binary(op, left, right) => {
                    let left = build_bdd(ctx, left);
                    let right = build_bdd(ctx, right);
                    match op {
                        BinaryOp::And => left.and(&right),
                        BinaryOp::Or => left.or(&right),
                        _ => {
                            unreachable!("Not an AND-OR function.");
                        }
                    }
                }
            }
        }

        build_bdd(&self, &update)
    }

    /*
        TODO: The rest of these methods probably don't work in this encoding... we'll see what we can keep.
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
    */
}
