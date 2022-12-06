use crate::solver_context::{BnSolver, BnSolverContext};
use crate::{BinaryOp, BooleanNetwork, FnUpdate, ParameterId, VariableId};
use crate::{ExtendedBoolean, Space};
use z3::ast::{Ast, Bool};
use z3::{FuncDecl, Solver, Sort};

impl<'z3> BnSolverContext<'z3> {
    /// Wrap a `BooleanNetwork` into a `SolverContext` that is attached to the given Z3
    /// context. `SolverContext` will then create the network variables and parameters in this
    /// Z3 context for future manipulation.
    pub fn new(z3: &'z3 z3::Context, network: BooleanNetwork) -> BnSolverContext<'z3> {
        let bool_sort = Sort::bool(z3);

        let variable_constructors = network
            .variables()
            .map(|it| {
                let name = network.get_variable_name(it);
                FuncDecl::new(z3, name.as_str(), &[], &bool_sort)
            })
            .collect::<Vec<_>>();

        let variable_constants = variable_constructors
            .iter()
            .map(|it| it.apply(&[]).as_bool().unwrap())
            .collect::<Vec<_>>();

        let explicit_parameter_constructors = network
            .parameters()
            .map(|it| {
                let param = network.get_parameter(it);
                let name = param.get_name();
                let domain = (0..param.get_arity())
                    .map(|_| &bool_sort)
                    .collect::<Vec<_>>();
                FuncDecl::new(z3, name.as_str(), &domain, &bool_sort)
            })
            .collect::<Vec<_>>();

        let implicit_parameter_constructors = network
            .variables()
            .map(|it| {
                if network.get_update_function(it).is_none() {
                    let regulators = network.regulators(it);
                    let name = format!("_update_{}", network.get_variable_name(it));
                    let domain = (0..regulators.len())
                        .map(|_| &bool_sort)
                        .collect::<Vec<_>>();
                    Some(FuncDecl::new(z3, name.as_str(), &domain, &bool_sort))
                } else {
                    None
                }
            })
            .collect::<Vec<_>>();

        BnSolverContext {
            network,
            z3,
            variable_constructors,
            variable_constants,
            explicit_parameter_constructors,
            implicit_parameter_constructors,
        }
    }

    /// Create fresh declarations of `n` Boolean variables (zero-arity functions) corresponding
    /// to the `n` network variables, using the given `prefix` when naming the variables.
    pub fn declare_state_variables(&self, prefix: &str) -> Vec<FuncDecl<'z3>> {
        let bool_sort = Sort::bool(self.z3);
        self.network
            .variables()
            .map(|it| {
                let name = format!("{}{}", prefix, self.network.get_variable_name(it));
                FuncDecl::new(self.z3, name.as_str(), &[], &bool_sort)
            })
            .collect::<Vec<_>>()
    }

    /// Low level method to obtain the constructor of the uninterpreted function
    /// corresponding to one of the network variables.
    ///
    /// The function has zero arguments and type `Bool`.
    pub fn get_variable_constructor(&self, var: VariableId) -> &FuncDecl<'z3> {
        &self.variable_constructors[var.to_index()]
    }

    /// Low level method to obtain the constructor of the uninterpreted function
    /// corresponding to one of the network's explicit parameters.
    ///
    /// The function arity is the same as the corresponding parameter and both arguments
    /// and return value are of type `Bool`.
    pub fn get_explicit_parameter_constructor(&self, param: ParameterId) -> &FuncDecl<'z3> {
        &self.explicit_parameter_constructors[param.to_index()]
    }

    /// Low level method to obtain the constructor of the uninterpreted function
    /// corresponding to one of the network's implicit parameters.
    ///
    /// The function arity matches the number of regulators of `var` (the arguments
    /// also follow the order given by `network.regulators(var)`). Argument types and return
    /// type is `Bool`.
    pub fn get_implicit_parameter_constructor(&self, var: VariableId) -> &FuncDecl<'z3> {
        self.implicit_parameter_constructors[var.to_index()]
            .as_ref()
            .unwrap()
    }

    /// Low level method to create a new solver object without any assumptions.
    ///
    /// In particular, this solver does not respect the static constraints of the network's
    /// regulatory graph like monotonicity and observability.
    pub fn mk_empty_solver(&'z3 self) -> BnSolver<'z3> {
        BnSolver {
            context: self,
            solver: Solver::new(self.z3),
        }
    }

    /// Create a `BnSolver` that already contains all pre-existing constraints on the network's
    /// behaviour, such as the observability and monotonicity of individual regulations.
    ///
    /// Note that the constraints should not influence the network variables in any way, but they
    /// do eliminate invalid uninterpreted function instantiations.
    pub fn mk_network_solver(&'z3 self) -> BnSolver<'z3> {
        let solver = self.mk_empty_solver();

        for reg in self.network.as_graph().regulations() {
            let source = reg.get_regulator();
            let target = reg.get_target();
            if reg.is_observable() {
                solver.assert_regulation_observability(source, target);
            }
            if let Some(monotonicity) = reg.get_monotonicity() {
                solver.assert_regulation_monotonicity(source, target, monotonicity);
            }
        }

        solver
    }

    /// Get an existing AST node representing the validity of the given network variable.
    pub fn var(&self, var: VariableId) -> &Bool<'z3> {
        &self.variable_constants[var.to_index()]
    }

    /// Create a new AST node representing the validity of the given network variable.
    pub fn mk_var(&self, var: VariableId) -> Bool<'z3> {
        self.variable_constructors[var.to_index()]
            .apply(&[])
            .as_bool()
            .unwrap()
    }

    /// Create an AST node representing the validity of the given explicit parameter
    /// under the given arguments.
    pub fn mk_explicit_parameter(&self, parameter: ParameterId, args: &[VariableId]) -> Bool<'z3> {
        // I have no idea if this is the best way to do this, but right now, I've got
        // nothing better.
        let args: Vec<Bool> = args.iter().map(|it| self.mk_var(*it)).collect::<Vec<_>>();
        let arg_refs: Vec<&dyn Ast<'z3>> = args.iter().map(|it| it as &dyn Ast).collect();
        self.explicit_parameter_constructors[parameter.to_index()]
            .apply(&arg_refs)
            .as_bool()
            .unwrap()
    }

    /// Create an AST node representing the validity of the given explicit parameter
    /// under the given constant arguments.
    pub fn mk_explicit_const_parameter(
        &'z3 self,
        parameter: ParameterId,
        args: &[bool],
    ) -> Bool<'z3> {
        let args: Vec<Bool<'z3>> = args
            .iter()
            .map(|it| Bool::from_bool(self.as_z3(), *it))
            .collect::<Vec<_>>();
        let arg_refs: Vec<&dyn Ast<'z3>> = args.iter().map(|it| it as &dyn Ast).collect();
        self.explicit_parameter_constructors[parameter.to_index()]
            .apply(&arg_refs)
            .as_bool()
            .unwrap()
    }

    /// Create an AST node representing the validity of the given implicit parameter
    /// under the regulators declared in the associated network.
    pub fn mk_implicit_parameter(&self, var: VariableId) -> Bool<'z3> {
        assert!(self.network.get_update_function(var).is_none());
        let args = self
            .network
            .regulators(var)
            .into_iter()
            .map(|it| self.mk_var(it))
            .collect::<Vec<_>>();
        let arg_refs: Vec<&dyn Ast> = args.iter().map(|it| it as &dyn Ast).collect();
        self.implicit_parameter_constructors[var.to_index()]
            .as_ref()
            .unwrap()
            .apply(&arg_refs)
            .as_bool()
            .unwrap()
    }

    /// Create an AST node representing the validity of the given implicit parameter
    /// under the given constant values.
    pub fn mk_implicit_const_parameter(&'z3 self, var: VariableId, args: &[bool]) -> Bool<'z3> {
        assert!(self.network.get_update_function(var).is_none());
        let args = args
            .iter()
            .map(|it| Bool::from_bool(self.as_z3(), *it))
            .collect::<Vec<_>>();
        let arg_refs: Vec<&dyn Ast> = args.iter().map(|it| it as &dyn Ast).collect();
        self.implicit_parameter_constructors[var.to_index()]
            .as_ref()
            .unwrap()
            .apply(&arg_refs)
            .as_bool()
            .unwrap()
    }

    /// Create an AST node representing the update function (or implicit parameter) of the
    /// given network variable.
    pub fn mk_update_function(&self, var: VariableId) -> Bool<'z3> {
        if let Some(function) = self.network.get_update_function(var) {
            self.translate_update_function(
                function,
                &self.variable_constructors,
                &self.explicit_parameter_constructors,
            )
        } else {
            self.mk_implicit_parameter(var)
        }
    }

    /// Build a formula that is satisfied by all states which belong to the given subspace.
    pub fn mk_space(&'z3 self, space: &Space) -> Bool<'z3> {
        self.translate_space(space, &self.variable_constructors)
    }

    /// A helper method for translating between a `Space` and Z3 AST.
    ///
    /// You can supply your own variable constructors.
    pub fn translate_space(
        &'z3 self,
        space: &Space,
        variable_constructors: &[FuncDecl<'z3>],
    ) -> Bool<'z3> {
        let mut args = Vec::new();
        for var in self.as_network().variables() {
            let term = variable_constructors[var.to_index()]
                .apply(&[])
                .as_bool()
                .unwrap();
            match space[var] {
                ExtendedBoolean::One => args.push(term),
                ExtendedBoolean::Zero => {
                    args.push(term.not());
                }
                ExtendedBoolean::Any => (),
            }
        }
        let args: Vec<&Bool<'z3>> = args.iter().collect();
        Bool::and(self.as_z3(), &args)
    }

    /// A helper method for translating between update functions and Z3 AST.
    ///
    /// It explicitly takes as arguments the variable and parameter constructors such that you
    /// can build the AST using other than the default set of variables if you so desire.
    pub fn translate_update_function(
        &self,
        update: &FnUpdate,
        variable_constructors: &[FuncDecl<'z3>],
        parameter_constructors: &[FuncDecl<'z3>],
    ) -> Bool<'z3> {
        match update {
            FnUpdate::Const(value) => Bool::from_bool(self.z3, *value),
            FnUpdate::Var(id) => {
                // Call the variable constructor - result must be a Bool because variables
                // are declared as Bools
                variable_constructors[id.to_index()]
                    .apply(&[])
                    .as_bool()
                    .unwrap()
            }
            FnUpdate::Param(id, args) => {
                let args: Vec<Bool> = args
                    .iter()
                    .map(|it| {
                        variable_constructors[it.to_index()]
                            .apply(&[])
                            .as_bool()
                            .unwrap()
                    })
                    .collect::<Vec<_>>();
                let arg_refs: Vec<&dyn Ast<'z3>> = args.iter().map(|it| it as &dyn Ast).collect();
                parameter_constructors[id.to_index()]
                    .apply(&arg_refs)
                    .as_bool()
                    .unwrap()
            }
            FnUpdate::Not(inner) => {
                let inner = self.translate_update_function(
                    inner,
                    variable_constructors,
                    parameter_constructors,
                );
                inner.not()
            }
            FnUpdate::Binary(op, left, right) => {
                let left = self.translate_update_function(
                    left,
                    variable_constructors,
                    parameter_constructors,
                );
                let right = self.translate_update_function(
                    right,
                    variable_constructors,
                    parameter_constructors,
                );
                match op {
                    BinaryOp::And => Bool::and(self.z3, &[&left, &right]),
                    BinaryOp::Or => Bool::or(self.z3, &[&left, &right]),
                    BinaryOp::Xor => left.xor(&right),
                    BinaryOp::Iff => left.iff(&right),
                    BinaryOp::Imp => left.implies(&right),
                }
            }
        }
    }

    pub fn as_z3(&self) -> &z3::Context {
        self.z3
    }

    pub fn as_network(&self) -> &BooleanNetwork {
        &self.network
    }
}
