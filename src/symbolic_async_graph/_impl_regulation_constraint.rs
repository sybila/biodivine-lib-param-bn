use crate::symbolic_async_graph::{RegulationConstraint, SymbolicContext};
use crate::{BooleanNetwork, Monotonicity, Regulation, VariableId};
use biodivine_lib_bdd::{Bdd, bdd};
impl RegulationConstraint {
    /// Compute a BDD representing all instantiations of a (partial) function where the given
    /// `input` is observable (also called essential).
    ///
    /// In particular:
    ///  - `ctx` is a symbolic encoding of a [BooleanNetwork].
    ///  - `fn_is_true` is a BDD representing a (partially unknown) function.
    ///  - `input` refers to the function input which should be considered observable.
    ///
    /// Note that if `fn_is_true` is fully specified, then the result is always `true` or `false`.
    /// If `input` does not appear in `fn_is_true` at all, the result is always `false`.
    ///
    /// The main point of this function is that you can build an observability constraint for
    /// an arbitrary symbolic function. Hence, it can be used both to validate an existing
    /// regulatory graph, and to infer observability of an otherwise unspecified
    /// regulation.
    ///
    pub fn mk_observability(ctx: &SymbolicContext, fn_is_true: &Bdd, input: VariableId) -> Bdd {
        /*
                  "Exists an input vector where output of `f` changes due to the input `r`."
           (implicit \exists p_1, ..., p_m):
               \exists s_1, ..., s_n:
                   a <- \exists s_r: F(s_1, ..., s_r, ..., s_n, p_1, ..., p_m) = 1 and s_r = 1
                   b <- \exists s_r: F(s_1, ..., s_r, ..., s_n, p_1, ..., p_m) = 1 and s_r = 0
                   a != b
        */
        let input = ctx.get_state_variable(input);
        let input_is_true = ctx.bdd_variable_set().mk_var(input);
        let input_is_false = input_is_true.not();
        // \exists x_r : F(x_1, ..., x_r, ..., x_n) & x_r | Context where F is one for x_r, but with x_r erased.
        let fn_x1_to_1 = bdd!(fn_is_true & input_is_true).var_exists(input);
        // \exists x_r : F(x_1, ..., x_r, ..., x_m) & !x_r | Context where F is one for !x_r, but with x_r erased.
        let fn_x0_to_1 = bdd!(fn_is_true & input_is_false).var_exists(input);
        // Context where F for x_r is not equal F for !x_r (i.e. all witnesses of observability)
        // and then with all states erased.
        bdd!(fn_x1_to_1 ^ fn_x0_to_1).exists(ctx.state_variables())
    }

    /// Compute a BDD representing all instantiations of a (partial) function where the given
    /// `input` is an activator (also called positively monotonic).
    ///
    /// In particular:
    ///  - `ctx` is a symbolic encoding of a [BooleanNetwork].
    ///  - `fn_is_true` is a BDD representing a (partially unknown) function.
    ///  - `input` refers to the function input which should be an activator.
    ///
    /// Note that if `fn_is_true` is fully specified, then the result is always `true` or `false`.
    /// If `input` does not appear in `fn_is_true` at all, the result is always `true`.
    ///
    /// The main point of this function is that you can build an activator constraint for
    /// an arbitrary symbolic function. Hence, it can be used both to validate an existing
    /// regulatory graph, and to infer observability of an otherwise unspecified
    /// regulation.
    ///
    pub fn mk_activation(ctx: &SymbolicContext, fn_is_true: &Bdd, input: VariableId) -> Bdd {
        /*
               "Exists an input where the functions monotonicity in `r` is reversed."
           (implicit \exists p_1, ..., p_m):
               not \exists s_1, ..., s_m:
                   a <- \exists s_r: F(s_1, ..., s_r, ..., s_n, p_1, ..., p_m) = 0 and s_r = 1
                   b <- \exists s_r: F(s_1, ..., s_r, ..., s_n, p_1, ..., p_m) = 1 and s_r = 0
                   a & b   // "I can go from 1 to 0 by increasing s_r."
        */
        let input = ctx.get_state_variable(input);
        let input_is_true = ctx.bdd_variable_set().mk_var(input);
        let input_is_false = input_is_true.not();
        let fn_is_false = fn_is_true.not();
        let fn_x1_to_0 = bdd!(fn_is_false & input_is_true).var_exists(input);
        let fn_x0_to_1 = bdd!(fn_is_true & input_is_false).var_exists(input);
        bdd!(fn_x0_to_1 & fn_x1_to_0)
            .exists(ctx.state_variables())
            .not()
    }

    /// The same as [RegulationConstraint::mk_activation], but with negative monotonicity instead
    /// of positive monotonicity.
    pub fn mk_inhibition(ctx: &SymbolicContext, fn_is_true: &Bdd, input: VariableId) -> Bdd {
        let input = ctx.get_state_variable(input);
        let input_is_true = ctx.bdd_variable_set().mk_var(input);
        let input_is_false = input_is_true.not();
        let fn_is_false = fn_is_true.not();
        let fn_x0_to_0 = bdd!(fn_is_false & input_is_false).var_exists(input);
        let fn_x1_to_1 = bdd!(fn_is_true & input_is_true).var_exists(input);
        bdd!(fn_x0_to_0 & fn_x1_to_1)
            .exists(ctx.state_variables())
            .not()
    }

    /// Infer the *most specific* [Regulation] which is still sufficient to correctly
    /// cover the relationship between `regulator` and `target` in the provided function
    /// (represented as a `fn_is_true` [Bdd]).
    ///
    /// In particular:
    ///  - If `regulator` has no effect on `target`, return `None`.
    ///  - If `regulator` has an effect on `target` only for some instantiations of
    ///    `fn_is_true`, return a regulation with `observable = false`.
    ///  - If `regulator` impacts `target` in every instantiation of `fn_is_true`,
    ///    return `observable = true`.
    ///  - If all instantiations are positively/negatively monotonous, return a monotonic
    ///    regulation, otherwise return `monotonicity = None`.
    pub fn infer_sufficient_regulation(
        ctx: &SymbolicContext,
        regulator: VariableId,
        target: VariableId,
        fn_is_true: &Bdd,
    ) -> Option<Regulation> {
        let inputs = ctx.input_parameter_variables();

        let obs = Self::mk_observability(ctx, fn_is_true, regulator);
        let obs = obs.exists(&inputs);
        let observable = if obs.is_true() {
            true
        } else if !obs.is_false() {
            false
        } else {
            return None;
        };

        let act = Self::mk_activation(ctx, fn_is_true, regulator);
        let act = act.for_all(&inputs);
        let inh = Self::mk_inhibition(ctx, fn_is_true, regulator);
        let inh = inh.for_all(&inputs);

        let monotonicity = if act.is_true() {
            Some(Monotonicity::Activation)
        } else if inh.is_true() {
            Some(Monotonicity::Inhibition)
        } else {
            None
        };

        Some(Regulation {
            regulator,
            target,
            observable,
            monotonicity,
        })
    }

    /// Similar to [Self::infer_sufficient_regulation], but it tries to keep the constraints
    /// from the given `old_regulation` assuming they are satisfiable and more restrictive
    /// than the inferred constraints.
    pub fn fix_regulation(
        ctx: &SymbolicContext,
        old_regulation: &Regulation,
        fn_is_true: &Bdd,
    ) -> Option<Regulation> {
        let inputs = ctx.input_parameter_variables();

        let obs = Self::mk_observability(ctx, fn_is_true, old_regulation.regulator);
        let obs = obs.exists(&inputs);

        let observable = if obs.is_true() {
            // The regulation is used by every possible instantiation, it is always observable.
            true
        } else if !obs.is_false() {
            // The regulation is used by *some* instantiations. It is observable if the old
            // regulation is observable.
            old_regulation.observable
        } else {
            // The regulation is *never* used, hence the regulation is irrelevant.
            return None;
        };

        let act = Self::mk_activation(ctx, fn_is_true, old_regulation.regulator);
        let act = act.for_all(&inputs);
        let inh = Self::mk_inhibition(ctx, fn_is_true, old_regulation.regulator);
        let inh = inh.for_all(&inputs);

        let monotonicity = if act.is_true() {
            // The function is *always* an activation.
            Some(Monotonicity::Activation)
        } else if inh.is_true() {
            // The function is *always* an inhibition.
            Some(Monotonicity::Inhibition)
        } else {
            // The function can have instantiations with different monotonicity, or possibly
            // even dual monotonicity.
            if old_regulation.monotonicity == Some(Monotonicity::Activation) && !act.is_false() {
                // Old regulation is an activation and there are *some* activating instantiations.
                // We can propagate the old constraint.
                Some(Monotonicity::Activation)
            } else if old_regulation.monotonicity == Some(Monotonicity::Inhibition)
                && !inh.is_false()
            {
                // Old regulation is an inhibition and there are *some* inhibiting instantiations.
                // We can propagate the old constraint.
                Some(Monotonicity::Inhibition)
            } else {
                // Either the old activation is also non-monotonic, or the function contradicts
                // the old monotonicity requirement.
                None
            }
        };

        Some(Regulation {
            regulator: old_regulation.regulator,
            target: old_regulation.target,
            observable,
            monotonicity,
        })
    }
}

/// Compute a `Bdd` which is a subset of the `initial` valuations that satisfies all
/// constraints imposed by the given Boolean `network`.
///
/// If there are no satisfying valuations, this function should return a human-readable
/// message which explains problem (often in several lines). However, in some complex
/// cases (inter-dependent parameters), this can be very hard and the error messages
/// are thus purely a "best effort service".
pub(crate) fn apply_regulation_constraints(
    initial: Bdd,
    network: &BooleanNetwork,
    context: &SymbolicContext,
) -> Result<Bdd, String> {
    // Detect "input parameters". For these, we don't actually want to apply any restrictions,
    // as these are typically just variables that are converted into parameters. Therefore,
    // they *can* have both values, even though one of them would make a particular constraint
    // not satisfied.
    let inputs = context.input_parameter_variables();

    // For each variable, compute Bdd that is true exactly when its update function is true.
    let update_function_is_true: Vec<Bdd> = network
        .variables()
        .map(|variable| {
            if let Some(function) = network.get_update_function(variable) {
                context.mk_fn_update_true(function)
            } else {
                context.mk_implicit_function_is_true(variable, &network.regulators(variable))
            }
        })
        .collect();

    let mut error_message = String::new();
    let mut unit_bdd = initial;
    for regulation in &network.graph.regulations {
        let regulator = regulation.regulator;
        let fn_is_true = &update_function_is_true[regulation.target.to_index()];

        let observability = if regulation.observable {
            RegulationConstraint::mk_observability(context, fn_is_true, regulator)
        } else {
            context.mk_constant(true)
        };

        // The regulation is observable if it is observable for at least one input valuation.
        let observability = observability.exists(&inputs);

        /* If observability failed, report error and continue. */
        if observability.is_false() {
            let problem = format!(
                " - {} has no effect in {}.\n",
                network.get_variable_name(regulation.regulator),
                network.get_variable_name(regulation.target),
            );
            error_message = format!("{}{}", error_message, problem);
        }

        let monotonicity = match regulation.monotonicity {
            Some(Monotonicity::Activation) => {
                RegulationConstraint::mk_activation(context, fn_is_true, regulator)
            }
            Some(Monotonicity::Inhibition) => {
                RegulationConstraint::mk_inhibition(context, fn_is_true, regulator)
            }
            None => context.mk_constant(true),
        };

        // The input parameter either makes the regulation not observable,
        // or it must be monotonic.
        let monotonicity = monotonicity.for_all(&inputs);

        if monotonicity.is_false() {
            let monotonicity_str = match regulation.monotonicity {
                Some(Monotonicity::Activation) => "activating",
                Some(Monotonicity::Inhibition) => "inhibiting",
                None => "monotonous",
            };
            let problem = format!(
                " - {} not {} in {}.\n",
                network.get_variable_name(regulation.regulator),
                monotonicity_str,
                network.get_variable_name(regulation.target),
            );
            error_message = format!("{}{}", error_message, problem);
        }

        unit_bdd = bdd!(unit_bdd & (monotonicity & observability));
    }

    if unit_bdd.is_false() {
        Err(format!(
            "No update functions satisfy given constraints: \n{}",
            error_message
        ))
    } else {
        Ok(unit_bdd)
    }
}

#[cfg(test)]
mod tests {
    use crate::Monotonicity::{Activation, Inhibition};
    use crate::symbolic_async_graph::_impl_regulation_constraint::apply_regulation_constraints;
    use crate::symbolic_async_graph::{RegulationConstraint, SymbolicAsyncGraph, SymbolicContext};
    use crate::{BooleanNetwork, Regulation, VariableId};

    #[test]
    fn input_parameter_constraints() {
        // For "inputs", both values are always allowed.
        let bn = BooleanNetwork::try_from(
            r"
            a -> b
            a -| c
            # p1 has to be false for a to be observable.
            $b: p1 | a
            # p1 has to be true for a to be observable.
            $c: !p1 | !a
        ",
        )
        .unwrap();

        let ctx = SymbolicContext::new(&bn).unwrap();
        let unit = ctx.mk_constant(true);
        let constraint = apply_regulation_constraints(unit.clone(), &bn, &ctx);
        assert_eq!(constraint, Ok(unit));

        // This behaviour should also apply to the inference methods:
        let stg = SymbolicAsyncGraph::new(&bn).unwrap();
        let a = VariableId(0);
        let b = VariableId(1);
        let c = VariableId(2);
        let reg = RegulationConstraint::infer_sufficient_regulation(
            &ctx,
            a,
            b,
            stg.get_symbolic_fn_update(b),
        )
        .unwrap();
        assert!(reg.observable);
        assert_eq!(reg.monotonicity, Some(Activation));
        let empty_reg = Regulation {
            regulator: a,
            target: b,
            observable: false,
            monotonicity: None,
        };
        let reg =
            RegulationConstraint::fix_regulation(&ctx, &empty_reg, stg.get_symbolic_fn_update(b))
                .unwrap();
        assert!(reg.observable);
        assert_eq!(reg.monotonicity, Some(Activation));

        let reg = RegulationConstraint::infer_sufficient_regulation(
            &ctx,
            a,
            c,
            stg.get_symbolic_fn_update(c),
        )
        .unwrap();
        assert!(reg.observable);
        assert_eq!(reg.monotonicity, Some(Inhibition));
        let empty_reg = Regulation {
            regulator: a,
            target: c,
            observable: false,
            monotonicity: None,
        };
        let reg =
            RegulationConstraint::fix_regulation(&ctx, &empty_reg, stg.get_symbolic_fn_update(c))
                .unwrap();
        assert!(reg.observable);
        assert_eq!(reg.monotonicity, Some(Inhibition));

        // For other functions, the constraints still apply.
        let bn = BooleanNetwork::try_from(
            r"
            a -> b
            a -> c
            $b: f(a)
            $c: !f(a)
        ",
        )
        .unwrap();

        let ctx = SymbolicContext::new(&bn).unwrap();
        let unit = ctx.mk_constant(true);
        let constraint = apply_regulation_constraints(unit.clone(), &bn, &ctx);
        assert!(constraint.is_err());
    }
}
