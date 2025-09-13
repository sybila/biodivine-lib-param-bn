use crate::solver_context::{BnSolver, BnSolverContext, BnSolverModel};
use crate::{Monotonicity, Space, VariableId};
use std::ops::Not;
use z3::ast::{Ast, Bool, forall_const};
use z3::{FuncDecl, SatResult, Solver};

impl BnSolver {
    pub fn as_z3(&self) -> &z3::Context {
        &self.context.data.z3
    }

    pub fn as_z3_solver(&self) -> &Solver {
        &self.solver
    }

    pub fn as_context(&self) -> &BnSolverContext {
        &self.context
    }

    pub fn check(&self) -> SatResult {
        self.solver.check()
    }

    /// Retrieve the model which was created during the last `check` operation.
    ///
    /// The result is `None` if last check was not `Sat`, or if `check` was not called
    /// after last assertions were added.
    pub fn get_model(&self) -> Option<BnSolverModel> {
        self.solver.get_model().map(|it| BnSolverModel {
            context: self.context.clone(),
            model: it,
        })
    }

    /// Retrieve the native model stored by the solver. All restrictions and caveats
    /// of `get_model` apply as well.
    pub fn get_z3_model(&self) -> Option<z3::Model> {
        self.solver.get_model()
    }

    pub fn push(&self) {
        self.solver.push();
    }

    pub fn pop(&self) {
        self.solver.pop(1);
    }

    /// Add an assertion to this solver that the results must be within
    /// some of the given subspaces.
    pub fn assert_within_spaces(&self, spaces: &[Space]) {
        let spaces: Vec<Bool> = spaces
            .iter()
            .map(|space| self.context.mk_space(space))
            .collect();
        let spaces: Vec<&Bool> = spaces.iter().collect();
        let assertion = Bool::or(&spaces);
        self.solver.assert(&assertion);
    }

    /// Add an assertion to this solver that the results must **not** be within any of the
    /// given subspaces.
    pub fn assert_not_within_spaces(&self, spaces: &[Space]) {
        let spaces: Vec<Bool> = spaces
            .iter()
            .map(|space| self.context.mk_space(space))
            .collect();
        let spaces: Vec<&Bool> = spaces.iter().collect();
        let assertion = Bool::or(&spaces).not();
        self.solver.assert(&assertion);
    }

    /// Add an assertion to this solver which states that the `source` variable must be an
    /// observable input in the update function of the `target` variable.
    ///
    /// The function panics if `source` is not an input of the `target` update function.
    pub fn assert_regulation_observability(&self, source: VariableId, target: VariableId) {
        let regulators = self.context.data.network.regulators(target);
        assert!(regulators.contains(&source));

        let mut positive_update = self.context.mk_update_function(target);
        let mut negative_update = self.context.mk_update_function(target);

        for reg in regulators {
            let reg_var = self.context.mk_var(reg);

            if reg == source {
                let one = Bool::from_bool(true);
                let zero = Bool::from_bool(false);
                positive_update = positive_update.substitute(&[(&reg_var, &one)]);
                negative_update = negative_update.substitute(&[(&reg_var, &zero)]);
            } else {
                let fresh = Bool::fresh_const("_o_");
                positive_update = positive_update.substitute(&[(&reg_var, &fresh)]);
                negative_update = negative_update.substitute(&[(&reg_var, &fresh)]);
            }
        }

        let assertion = positive_update.iff(&negative_update).not();
        self.solver.assert(&assertion);
    }

    /// Add assertion to this solver which states that the `source` variable must be a monotonous
    /// input in the update function of the `target` variable.
    ///
    /// The function panics if `source` is not an input of the `target` update function.
    pub fn assert_regulation_monotonicity(
        &self,
        source: VariableId,
        target: VariableId,
        monotonicity: Monotonicity,
    ) {
        let regulators = self.context.data.network.regulators(target);
        assert!(regulators.contains(&source));

        let mut positive_update = self.context.mk_update_function(target);
        let mut negative_update = self.context.mk_update_function(target);

        let mut bounds: Vec<Bool> = Vec::new();

        for reg in regulators {
            let reg_var = self.context.mk_var(reg);

            if reg == source {
                let one = Bool::from_bool(true);
                let zero = Bool::from_bool(false);
                positive_update = positive_update.substitute(&[(&reg_var, &one)]);
                negative_update = negative_update.substitute(&[(&reg_var, &zero)]);
            } else {
                let fresh = Bool::fresh_const("_m_");
                positive_update = positive_update.substitute(&[(&reg_var, &fresh)]);
                negative_update = negative_update.substitute(&[(&reg_var, &fresh)]);
                bounds.push(fresh);
            }
        }

        let assertion = if monotonicity == Monotonicity::Activation {
            // negative <= positive, i.e. negative implies positive
            negative_update.implies(&positive_update)
        } else {
            // positive <= negative, i.e. positive implies negative
            positive_update.implies(&negative_update)
        };

        let bounds: Vec<&dyn Ast> = bounds.iter().map(|it| it as &dyn Ast).collect();

        let assertion = forall_const(&bounds, &[], &assertion);

        self.solver.assert(&assertion);
    }

    /// Add an assertion to this solver that the `i`-th argument of the given Boolean `function`
    /// must be observable.
    ///
    /// Panics if the argument is outside of function arity, or the function isn't Boolean.
    pub fn assert_function_observability(&self, function: &FuncDecl, i: usize) {
        assert!(i < function.arity());
        // (exists) x1...x(n-1) such that f(x1,...,x(n-1),1) != f(x1,...,x(n-1),0)
        let fresh_args: Vec<Bool> = (0..function.arity())
            .map(|_| Bool::fresh_const("_o_"))
            .collect();
        let mut positive_args: Vec<&dyn Ast> = Vec::new();
        let mut negative_args: Vec<&dyn Ast> = Vec::new();

        let one = Bool::from_bool(true);
        let zero = Bool::from_bool(false);

        for (j, arg) in fresh_args.iter().enumerate() {
            if i == j {
                positive_args.push(&one as &dyn Ast);
                negative_args.push(&zero as &dyn Ast);
            } else {
                positive_args.push(arg as &dyn Ast);
                negative_args.push(arg as &dyn Ast);
            }
        }

        let pos_invoke = function.apply(&positive_args).as_bool().unwrap();
        let neg_invoke = function.apply(&negative_args).as_bool().unwrap();

        self.solver.assert(&pos_invoke.iff(&neg_invoke).not());
    }

    /// Add an assertion to this solver that the `i`-th argument of the given Boolean function must
    /// be positively or negatively monotonous.
    ///
    /// Panics if the argument is outside of function arity, or the function isn't Boolean.
    pub fn assert_function_monotonicity(
        &self,
        function: &FuncDecl,
        i: usize,
        monotonicity: Monotonicity,
    ) {
        assert!(i < function.arity());
        // (forall) x1...x(n-1) holds that f(x1,...,x(n-1),1) <= f(x1,...,x(n-1),0) (or >=)
        let fresh_args: Vec<Bool> = (0..function.arity())
            .map(|_| Bool::fresh_const("_m_"))
            .collect();
        let mut positive_args: Vec<&dyn Ast> = Vec::new();
        let mut negative_args: Vec<&dyn Ast> = Vec::new();

        let one = Bool::from_bool(true);
        let zero = Bool::from_bool(false);

        for (j, arg) in fresh_args.iter().enumerate() {
            if i == j {
                positive_args.push(&one as &dyn Ast);
                negative_args.push(&zero as &dyn Ast);
            } else {
                positive_args.push(arg as &dyn Ast);
                negative_args.push(arg as &dyn Ast);
            }
        }

        let pos_invoke = function.apply(&positive_args).as_bool().unwrap();
        let neg_invoke = function.apply(&negative_args).as_bool().unwrap();

        let assertion = if monotonicity == Monotonicity::Activation {
            // negative <= positive, i.e. negative implies positive
            neg_invoke.implies(&pos_invoke)
        } else {
            // positive <= negative, i.e. positive implies negative
            pos_invoke.implies(&neg_invoke)
        };

        let bounds: Vec<&dyn Ast> = fresh_args.iter().map(|it| it as &dyn Ast).collect();

        let assertion = forall_const(&bounds, &[], &assertion);

        self.solver.assert(&assertion);
    }
}

#[cfg(test)]
mod tests {
    use crate::solver_context::BnSolverContext;
    use crate::{BooleanNetwork, Monotonicity};
    use z3::SatResult;

    #[test]
    pub fn test_solver_regulation_constraints() {
        let bn = BooleanNetwork::try_from(
            r"
            a -?? b
            a -?? a
            b -?? c
            b -?? b
            c -?? a
            c -?? c
            $a: f(a)
            $b: !b & !a
            $c: c <=> b
        ",
        )
        .unwrap();

        let a = bn.as_graph().find_variable("a").unwrap();
        let b = bn.as_graph().find_variable("b").unwrap();
        let c = bn.as_graph().find_variable("c").unwrap();

        let ctx = BnSolverContext::new(bn.clone());
        let solver = ctx.mk_empty_solver();

        // Regulation `c -> a` is declared but not used.

        solver.push();
        solver.assert_regulation_observability(c, a);
        assert_eq!(solver.check(), SatResult::Unsat);
        solver.pop();

        // Regulation a -> b is negatively monotonous

        solver.push();
        solver.assert_regulation_monotonicity(a, b, Monotonicity::Inhibition);
        assert_eq!(solver.check(), SatResult::Sat);
        solver.pop();

        solver.push();
        solver.assert_regulation_monotonicity(a, b, Monotonicity::Activation);
        assert_eq!(solver.check(), SatResult::Unsat);
        solver.pop();

        // There is an f such that `a -> a` is observable.

        solver.push();
        solver.assert_regulation_observability(a, a);
        assert_eq!(solver.check(), SatResult::Sat);
        solver.pop();

        // Regulation c -> c is neither positive nor negative.

        solver.push();
        solver.assert_regulation_monotonicity(c, c, Monotonicity::Activation);
        assert_eq!(solver.check(), SatResult::Unsat);
        solver.pop();

        solver.push();
        solver.assert_regulation_monotonicity(c, c, Monotonicity::Inhibition);
        assert_eq!(solver.check(), SatResult::Unsat);
        solver.pop();
    }

    #[test]
    pub fn test_solver_function_constraints() {
        let bn = BooleanNetwork::try_from(
            r"
            a -?? b
            a -?? a
            b -?? c
            b -?? b
            c -?? a
            c -?? c
            $a: f(a, c)
            $b: g(a, b)
            $c: f(b, c)
        ",
        )
        .unwrap();

        let a = bn.as_graph().find_variable("a").unwrap();
        let b = bn.as_graph().find_variable("b").unwrap();
        let f = bn.find_parameter("f").unwrap();
        let g = bn.find_parameter("g").unwrap();

        let ctx = BnSolverContext::new(bn.clone());
        let solver = ctx.mk_empty_solver();

        let f_z3 = ctx.get_explicit_parameter_constructor(f);
        let g_z3 = ctx.get_explicit_parameter_constructor(g);

        // Check that f can be positively monotonous in the first and negatively monotonous in
        // the second argument, while being observable in both.
        solver.push();
        solver.assert_function_monotonicity(f_z3, 0, Monotonicity::Activation);
        solver.assert_function_monotonicity(f_z3, 1, Monotonicity::Inhibition);
        solver.assert_function_observability(f_z3, 0);
        solver.assert_function_observability(f_z3, 1);
        assert_eq!(solver.check(), SatResult::Sat);

        // However, at the same time, a -> a cannot be an inhibition.
        solver.push();
        solver.assert_regulation_monotonicity(a, a, Monotonicity::Inhibition);
        assert_eq!(solver.check(), SatResult::Unsat);
        solver.pop();

        // Meanwhile, g is unaffected by f:
        solver.assert_function_monotonicity(g_z3, 0, Monotonicity::Inhibition);
        solver.assert_regulation_monotonicity(b, b, Monotonicity::Activation);
        assert_eq!(solver.check(), SatResult::Sat);
        solver.pop();
    }
}
