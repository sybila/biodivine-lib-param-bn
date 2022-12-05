use crate::solver_context::{BnSolver, BnSolverContext, BnSolverModel, RawBnModelIterator};
use crate::trap_spaces::ExtendedBoolean::{One, Zero};
use crate::trap_spaces::{ExtendedBoolean, Space};
use crate::{BinaryOp, FnUpdate, VariableId};
use std::collections::HashSet;
use z3::ast::{Ast, Bool};
use z3::{FuncDecl, Params, SatResult};
use ExtendedBoolean::Any;

pub struct SolverIterator<'z3> {
    positive_constructors: Vec<FuncDecl<'z3>>,
    negative_constructors: Vec<FuncDecl<'z3>>,
    positive_variables: Vec<Bool<'z3>>,
    negative_variables: Vec<Bool<'z3>>,
    sub_positive: Vec<Bool<'z3>>,
    sub_negative: Vec<Bool<'z3>>,
    context: &'z3 BnSolverContext<'z3>,
    inner: RawBnModelIterator<'z3>,
}

impl<'z3> SolverIterator<'z3> {
    pub fn recursive_iteration(context: &'z3 BnSolverContext<'z3>) {
        let solver = context.mk_network_solver();

        let positive_constructors = context.declare_state_variables("p_");
        let negative_constructors = context.declare_state_variables("n_");

        let positive_variables: Vec<Bool<'z3>> = positive_constructors
            .iter()
            .map(|it| it.apply(&[]).as_bool().unwrap())
            .collect::<Vec<_>>();

        let negative_variables: Vec<Bool<'z3>> = negative_constructors
            .iter()
            .map(|it| it.apply(&[]).as_bool().unwrap())
            .collect::<Vec<_>>();

        let mut non_trivial = Vec::new();

        let mut ones = Vec::new();
        let mut zeros = Vec::new();

        let mut sub_ones = Vec::new();
        let mut sub_zeros = Vec::new();

        for var in context.as_network().variables() {
            let p_var = &positive_variables[var.to_index()];
            let n_var = &negative_variables[var.to_index()];
            // (p_x | n_x)
            let consistency = Bool::or(context.as_z3(), &[p_var, n_var]);
            solver.as_z3_solver().assert(&consistency);

            non_trivial.push(Bool::and(context.as_z3(), &[p_var, n_var]));

            // p_x <=> positive(update) and n_x <=> negative(update)
            if let Some(function) = context.as_network().get_update_function(var) {
                let normal_form = function.to_and_or_normal_form();
                let fn_is_one = normal_form.distribute_negation();
                let fn_is_zero = normal_form.negation().distribute_negation();

                let fn_is_one = Self::positive_biased_function(
                    context.as_z3(),
                    &fn_is_one,
                    &positive_constructors,
                    &negative_constructors,
                );

                let fn_is_zero = Self::positive_biased_function(
                    context.as_z3(),
                    &fn_is_zero,
                    &positive_constructors,
                    &negative_constructors,
                );

                //solver.as_z3_solver().assert(&p_var.iff(&fn_is_one));
                //solver.as_z3_solver().assert(&n_var.iff(&fn_is_zero));
                sub_ones.push(fn_is_one.substitute::<Bool>(&[])); // lazy way to copy
                sub_zeros.push(fn_is_zero.substitute::<Bool>(&[]));
                ones.push(fn_is_one);
                zeros.push(fn_is_zero);
            } else {
                unimplemented!()
            }
        }

        for i in 0usize..(context.as_network().num_vars() - 1) {
            println!("Start {}/{}", i + 1, context.as_network().num_vars() - 1);

            let mut substitutions = Vec::new();

            for var in context.as_network().variables() {
                let p_var = &positive_variables[var.to_index()];
                let n_var = &negative_variables[var.to_index()];

                let var_one = &sub_ones[var.to_index()];
                let var_zero = &sub_zeros[var.to_index()];

                substitutions.push((p_var, var_one));
                substitutions.push((n_var, var_zero));
            }

            let mut new_sub_ones = Vec::new();
            let mut new_sub_zeros = Vec::new();

            for var in context.as_network().variables() {
                //println!("Start var {:?}.", var);
                let f_one: &Bool<'z3> = &ones[var.to_index()];
                let f_zero: &Bool<'z3> = &zeros[var.to_index()];

                let new_f_one = f_one.substitute(&substitutions).simplify();
                let new_f_zero = f_zero.substitute(&substitutions).simplify();

                new_sub_ones.push(new_f_one);
                new_sub_zeros.push(new_f_zero);
            }

            sub_ones = new_sub_ones;
            sub_zeros = new_sub_zeros;
        }

        let mut not_s_var = Vec::new();
        for var in context.as_network().variables() {
            let s_var = context.var(var);
            not_s_var.push(s_var.not());
        }

        let mut p_var_sub = Vec::new();
        let mut n_var_sub = Vec::new();
        for var in context.as_network().variables() {
            let s_var: &Bool<'z3> = context.var(var);
            let ns_var: &Bool<'z3> = &not_s_var[var.to_index()];

            let p_var: &Bool<'z3> = &positive_variables[var.to_index()];
            let n_var: &Bool<'z3> = &negative_variables[var.to_index()];

            p_var_sub.push((p_var, s_var));
            n_var_sub.push((n_var, ns_var));
        }

        for var in context.as_network().variables() {
            let p_var: &Bool<'z3> = &positive_variables[var.to_index()];
            let n_var: &Bool<'z3> = &negative_variables[var.to_index()];

            let f_one: &Bool<'z3> = &sub_ones[var.to_index()];
            let f_zero: &Bool<'z3> = &sub_zeros[var.to_index()];

            let f_one = f_one.substitute(&p_var_sub).substitute(&n_var_sub);
            let f_zero = f_zero.substitute(&p_var_sub).substitute(&n_var_sub);

            solver.as_z3_solver().assert(&p_var.iff(&f_one));
            solver.as_z3_solver().assert(&n_var.iff(&f_zero));
        }

        solver
            .as_z3_solver()
            .assert(&context.var(VariableId::from_index(4)).not());
        solver
            .as_z3_solver()
            .assert(&context.var(VariableId::from_index(0)).not());

        solver.check();
        let model = solver.get_model().unwrap();
        println!("{:?}", model.get_state());
        println!(
            "{:?}",
            model.get_space(&positive_variables, &negative_variables)
        );

        panic!("Done substitution.");

        //let non_trivial_args = non_trivial.iter().collect::<Vec<_>>();
        //solver.as_z3_solver().assert(&Bool::or(context.as_z3(), &non_trivial_args));

        // Now we have consistency, non-triviality and trap property for p_* and n_* vars.

        fn recursive<'a>(
            solver: &BnSolver<'a>,
            positive: &[Bool<'a>],
            negative: &[Bool<'a>],
            results: &mut HashSet<Space>,
        ) -> bool {
            if solver.check() == SatResult::Sat {
                let model = solver.get_model().unwrap();
                let space = model.get_space(&positive, &negative);
                println!("Found space[{}]", space.count_any());
                // First, test if there is a sub-space inside this space.
                println!(" > Test inside.");
                solver.push();
                let mut different = Vec::new();
                for var in solver.as_context().as_network().variables() {
                    let p_var = &positive[var.to_index()];
                    let n_var = &negative[var.to_index()];
                    match space[var] {
                        One => {
                            solver.as_z3_solver().assert(p_var);
                            solver.as_z3_solver().assert(&n_var.not());
                        }
                        Zero => {
                            solver.as_z3_solver().assert(&p_var.not());
                            solver.as_z3_solver().assert(n_var);
                        }
                        Any => {
                            different.push(p_var.xor(n_var));
                        }
                    }
                }
                // At least one "any" value is no longer "any".
                let different_args = different.iter().collect::<Vec<_>>();
                let different = Bool::or(solver.as_z3(), &different_args);
                solver.as_z3_solver().assert(&different);
                let has_inside = recursive(solver, positive, negative, results);
                if !has_inside {
                    println!("Minimal space[{}]: {}", space.count_any(), space);
                    if results.contains(&space) {
                        panic!("Duplicate.");
                    } else {
                        assert!(space.is_trap_space(solver.as_context().as_network()));
                        for x in results.iter() {
                            if x.intersect(&space).is_some() {
                                println!("{}", x);
                                println!("{}", space);
                                panic!("Intersection.");
                            }
                        }
                        results.insert(space.clone());
                        println!("Results: {}", results.len());
                    }
                }
                solver.pop();
                // Then test if there is a space outside this space.
                let mut different = Vec::new();
                for var in solver.as_context().as_network().variables() {
                    let p_var = &positive[var.to_index()];
                    let n_var = &negative[var.to_index()];
                    match space[var] {
                        One => {
                            let not_p_var = p_var.not();
                            different.push(Bool::and(solver.as_z3(), &[&not_p_var, &n_var]));
                        }
                        Zero => {
                            let not_n_var = n_var.not();
                            different.push(Bool::and(solver.as_z3(), &[p_var, &not_n_var]));
                        }
                        Any => {
                            // Do nothing.
                        }
                    }
                }
                println!(" > Test minus.");
                //solver.push();
                let different_args = different.iter().collect::<Vec<_>>();
                let different = Bool::or(solver.as_z3(), &different_args);
                solver.as_z3_solver().assert(&different);
                let _has_outside = recursive(solver, positive, negative, results);
                //solver.pop();
                // Either this space was minimal, or there was a minimal space in it.
                return true; //has_inside | has_outside;
            } else {
                println!("No space found.");
                return false;
            }
        }

        let mut results = HashSet::new();
        recursive(
            &solver,
            &positive_variables,
            &negative_variables,
            &mut results,
        );
    }

    pub fn new(context: &'z3 BnSolverContext<'z3>) -> SolverIterator<'z3> {
        let solver = context.mk_network_solver();

        let positive_constructors = context.declare_state_variables("p_");
        let negative_constructors = context.declare_state_variables("n_");

        let positive_variables = positive_constructors
            .iter()
            .map(|it| it.apply(&[]).as_bool().unwrap())
            .collect::<Vec<_>>();

        let negative_variables = negative_constructors
            .iter()
            .map(|it| it.apply(&[]).as_bool().unwrap())
            .collect::<Vec<_>>();

        let mut non_trivial = Vec::new();

        for var in context.as_network().variables() {
            let p_var = &positive_variables[var.to_index()];
            let n_var = &negative_variables[var.to_index()];
            // (p_x | n_x)
            let consistency = Bool::or(context.as_z3(), &[p_var, n_var]);
            solver.as_z3_solver().assert(&consistency);

            non_trivial.push(Bool::and(context.as_z3(), &[p_var, n_var]));

            // p_x <=> positive(update) and n_x <=> negative(update)
            if let Some(function) = context.as_network().get_update_function(var) {
                let normal_form = function.to_and_or_normal_form();
                let fn_is_one = normal_form.distribute_negation();
                let fn_is_zero = normal_form.negation().distribute_negation();

                let fn_is_one = Self::positive_biased_function(
                    context.as_z3(),
                    &fn_is_one,
                    &positive_constructors,
                    &negative_constructors,
                );

                let fn_is_zero = Self::positive_biased_function(
                    context.as_z3(),
                    &fn_is_zero,
                    &positive_constructors,
                    &negative_constructors,
                );

                solver.as_z3_solver().assert(&p_var.iff(&fn_is_one));
                solver.as_z3_solver().assert(&n_var.iff(&fn_is_zero));
            } else {
                unimplemented!()
            }
        }

        let non_trivial_args = non_trivial.iter().collect::<Vec<_>>();
        //solver.as_z3_solver().assert(&Bool::or(context.as_z3(), &non_trivial_args));

        let sub_positive_constructors = context.declare_state_variables("sub_p_");
        let sub_negative_constructors = context.declare_state_variables("sub_n_");

        let sub_positive_variables = sub_positive_constructors
            .iter()
            .map(|it| it.apply(&[]).as_bool().unwrap())
            .collect::<Vec<_>>();

        let sub_negative_variables = sub_negative_constructors
            .iter()
            .map(|it| it.apply(&[]).as_bool().unwrap())
            .collect::<Vec<_>>();

        let mut subspace_args = Vec::new();
        let mut trap_args = Vec::new();
        let mut is_different = Vec::new();
        let mut consistency = Vec::new();

        for var in context.as_network().variables() {
            let sub_p_var = &sub_positive_variables[var.to_index()];
            let sub_n_var = &sub_negative_variables[var.to_index()];
            consistency.push(Bool::or(context.as_z3(), &[sub_p_var, sub_n_var]));

            // p_x != sub_p_x | n_x != sub_n_x
            is_different.push(sub_p_var.xor(&positive_variables[var.to_index()]));
            is_different.push(sub_n_var.xor(&negative_variables[var.to_index()]));

            // (sub_p_x => p_x) & (sub_n_x => n_x)
            subspace_args.push(sub_p_var.implies(&positive_variables[var.to_index()]));
            subspace_args.push(sub_n_var.implies(&negative_variables[var.to_index()]));

            // sub_p_x <=> positive(update) and sub_n_x <=> negative(update)
            if let Some(function) = context.as_network().get_update_function(var) {
                let normal_form = function.to_and_or_normal_form();
                let fn_is_one = normal_form.distribute_negation();
                let fn_is_zero = normal_form.negation().distribute_negation();

                let fn_is_one = Self::positive_biased_function(
                    context.as_z3(),
                    &fn_is_one,
                    &sub_positive_constructors,
                    &sub_negative_constructors,
                );

                let fn_is_zero = Self::positive_biased_function(
                    context.as_z3(),
                    &fn_is_zero,
                    &sub_positive_constructors,
                    &sub_negative_constructors,
                );

                trap_args.push(sub_p_var.iff(&fn_is_one));
                trap_args.push(sub_n_var.iff(&fn_is_zero));
            } else {
                unimplemented!()
            }
        }

        let subspace_arg_refs = subspace_args.iter().collect::<Vec<_>>();
        let trap_arg_refs = trap_args.iter().collect::<Vec<_>>();
        let is_different_refs = is_different.iter().collect::<Vec<_>>();
        let consistency_args = consistency.iter().collect::<Vec<_>>();

        let is_subspace = Bool::and(context.as_z3(), &subspace_arg_refs);
        let is_trap = Bool::and(context.as_z3(), &trap_arg_refs);
        let is_different = Bool::or(context.as_z3(), &is_different_refs);
        let consistency = Bool::and(context.as_z3(), &consistency_args);

        let mut quantified = Vec::new();
        for var in context.as_network().variables() {
            quantified.push(&sub_positive_variables[var.to_index()] as &dyn Ast);
            quantified.push(&sub_negative_variables[var.to_index()] as &dyn Ast);
        }

        let exists_trap_subspace = z3::ast::exists_const(
            context.as_z3(),
            &quantified,
            &[],
            &Bool::and(
                context.as_z3(),
                &[&is_subspace, &is_trap, &is_different, &consistency],
            ),
        );

        solver.as_z3_solver().assert(&exists_trap_subspace.not());

        let mut enumeration_terms = Vec::new();
        for var in context.as_network().variables() {
            enumeration_terms.push(
                positive_constructors[var.to_index()]
                    .apply(&[])
                    .as_bool()
                    .unwrap(),
            );
            enumeration_terms.push(
                negative_constructors[var.to_index()]
                    .apply(&[])
                    .as_bool()
                    .unwrap(),
            );
        }

        let iterator = RawBnModelIterator::new(solver, enumeration_terms);

        SolverIterator {
            context,
            positive_constructors,
            negative_constructors,
            positive_variables,
            negative_variables,
            sub_positive: sub_positive_variables,
            sub_negative: sub_negative_variables,
            inner: iterator,
        }
    }

    fn positive_biased_function(
        z3: &'z3 z3::Context,
        update: &FnUpdate,
        positive: &[FuncDecl<'z3>],
        negative: &[FuncDecl<'z3>],
    ) -> Bool<'z3> {
        match update {
            FnUpdate::Const(value) => Bool::from_bool(z3, *value),
            FnUpdate::Var(var) => positive[var.to_index()].apply(&[]).as_bool().unwrap(),
            FnUpdate::Param(_, _) => {
                unimplemented!()
            }
            FnUpdate::Not(inner) => {
                if let Some(var) = inner.as_var() {
                    negative[var.to_index()].apply(&[]).as_bool().unwrap()
                } else {
                    println!("{:?}", inner);
                    unimplemented!()
                }
            }
            FnUpdate::Binary(op, left, right) => {
                let left = Self::positive_biased_function(z3, left, positive, negative);
                let right = Self::positive_biased_function(z3, right, positive, negative);
                match op {
                    BinaryOp::And => Bool::and(z3, &[&left, &right]),
                    BinaryOp::Or => Bool::or(z3, &[&left, &right]),
                    _ => {
                        panic!("The function must be in AND-OR normal form.")
                    }
                }
            }
        }
    }
}

impl<'z3> Iterator for SolverIterator<'z3> {
    type Item = Space;

    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next().map(|it| {
            //println!("{}", it);
            let model = BnSolverModel::new(self.context, it);
            let mut space = Space::new(self.context.as_network());
            let ones = model.get_raw_state(&self.positive_variables);
            let zeros = model.get_raw_state(&self.negative_variables);
            for var in self.context.as_network().variables() {
                if ones[var.to_index()] && !zeros[var.to_index()] {
                    space[var] = One;
                }
                if !ones[var.to_index()] && zeros[var.to_index()] {
                    space[var] = Zero;
                }
            }
            /*let mut space_2 = Space::new(self.context.as_network());
            let ones = model.get_raw_state(&self.sub_positive);
            let zeros = model.get_raw_state(&self.sub_negative);
            for var in self.context.as_network().variables() {
                if ones[var.to_index()] && !zeros[var.to_index()] {
                    space_2[var] = One;
                }
                if !ones[var.to_index()] && zeros[var.to_index()] {
                    space_2[var] = Zero;
                }
            }
            println!("{:?} / {:?}", ones, zeros);
            println!("Second space: {}", space_2);*/
            space
        })
    }
}
