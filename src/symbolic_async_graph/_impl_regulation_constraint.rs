use crate::symbolic_async_graph::{RegulationConstraint, SymbolicContext, SizeLimitExceeded};
use crate::{BooleanNetwork, Monotonicity, Regulation, VariableId};
use biodivine_lib_bdd::op_function::{and, xor};
use biodivine_lib_bdd::Bdd;

impl RegulationConstraint {
    /// A version of [RegulationConstraint::mk_observability] that accepts a node limit for
    /// the underlying BDD operations.
    ///
    /// If the limit is exceeded, this function returns an error.
    pub fn mk_observability_with_limit(
        ctx: &SymbolicContext,
        fn_is_true: &Bdd,
        input: VariableId,
        limit: usize,
    ) -> Result<Bdd, SizeLimitExceeded> {
        /*
                  "Exists an input vector where output of `f` changes due to the input `r`."
           (implicit \exists p_1, ..., p_m):
               \exists s_1, ..., s_n:
                   a <- \exists s_r: F(s_1, ..., s_r, ..., s_n, p_1, ..., p_m) = 1 and s_r = 1
                   b <- \exists s_r: F(s_1, ..., s_r, ..., s_n, p_1, ..., p_m) = 1 and s_r = 0
                   a != b
        */
        let input_variable = ctx.get_state_variable(input);
        let input_is_true = ctx.bdd_variable_set().mk_var(input_variable);
        // Negation does not increase node count.
        let input_is_false = input_is_true.not();

        // Constrain the function to when input is true.
        let fn_is_true_then_input_true =
            Bdd::binary_op_with_limit(limit, fn_is_true, &input_is_true, and)
                .ok_or_else(|| SizeLimitExceeded::new(limit))?;
        // Remove the input variable from the BDD.
        // TODO: This can be a source of memory issues.
        let fn_x1_to_1 = fn_is_true_then_input_true.var_exists(input_variable);

        // Constrain the function to when input is false.
        let fn_is_true_then_input_false =
            Bdd::binary_op_with_limit(limit, fn_is_true, &input_is_false, and)
                .ok_or_else(|| SizeLimitExceeded::new(limit))?;
        // Remove the input variable from the BDD.
        // TODO: This can be a source of memory issues.
        let fn_x0_to_1 = fn_is_true_then_input_false.var_exists(input_variable);

        // Check for what parameter valuations the two versions of the function can differ.
        let result = Bdd::binary_op_with_limit(limit, &fn_x1_to_1, &fn_x0_to_1, xor)
            .ok_or_else(|| SizeLimitExceeded::new(limit))?;

        // Finally, remove all state variables, leaving only parameters.
        // TODO: This can be a source of memory issues.
        Ok(result.exists(ctx.state_variables()))
    }

    /// Compute a BDD representing all instantiations of a (partial) function where the given
    /// `input` is observable (also called essential).
    ///
    /// Note that this version panics if the underlying BDD operations exceed the default memory
    /// limit. If you want to handle this case gracefully, use
    /// [RegulationConstraint::mk_observability_with_limit].
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
        Self::mk_observability_with_limit(ctx, fn_is_true, input, usize::MAX).unwrap()
    }

    /// A version of [RegulationConstraint::mk_activation] that accepts a node limit for
    /// the underlying BDD operations.
    ///
    /// If the limit is exceeded, this function returns an error.
    pub fn mk_activation_with_limit(
        ctx: &SymbolicContext,
        fn_is_true: &Bdd,
        input: VariableId,
        limit: usize,
    ) -> Result<Bdd, SizeLimitExceeded> {
        /*
               "Exists an input where the functions monotonicity in `r` is reversed."
           (implicit \exists p_1, ..., p_m):
               not \exists s_1, ..., s_m:
                   a <- \exists s_r: F(s_1, ..., s_r, ..., s_n, p_1, ..., p_m) = 0 and s_r = 1
                   b <- \exists s_r: F(s_1, ..., s_r, ..., s_n, p_1, ..., p_m) = 1 and s_r = 0
                   a & b   // "I can go from 1 to 0 by increasing s_r."
        */
        let input_variable = ctx.get_state_variable(input);
        let input_is_true = ctx.bdd_variable_set().mk_var(input_variable);
        let input_is_false = input_is_true.not();
        let fn_is_false = fn_is_true.not();

        let fn_is_false_then_input_true =
            Bdd::binary_op_with_limit(limit, &fn_is_false, &input_is_true, and)
                .ok_or_else(|| SizeLimitExceeded::new(limit))?;
        // TODO: This can be a source of memory issues.
        let fn_x1_to_0 = fn_is_false_then_input_true.var_exists(input_variable);

        let fn_is_true_then_input_false =
            Bdd::binary_op_with_limit(limit, fn_is_true, &input_is_false, and)
                .ok_or_else(|| SizeLimitExceeded::new(limit))?;
        // TODO: This can be a source of memory issues.
        let fn_x0_to_1 = fn_is_true_then_input_false.var_exists(input_variable);

        let result = Bdd::binary_op_with_limit(limit, &fn_x0_to_1, &fn_x1_to_0, and)
            .ok_or_else(|| SizeLimitExceeded::new(limit))?;

        // TODO: This can be a source of memory issues.
        Ok(result.exists(ctx.state_variables()).not())
    }

    /// Compute a BDD representing all instantiations of a (partial) function where the given
    /// `input` is an activator (also called positively monotonic).
    ///
    /// Note that this version panics if the underlying BDD operations exceed the default memory
    /// limit. If you want to handle this case gracefully, use
    /// [RegulationConstraint::mk_activation_with_limit].
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
        Self::mk_activation_with_limit(ctx, fn_is_true, input, usize::MAX).unwrap()
    }

    /// A version of [RegulationConstraint::mk_inhibition] that accepts a node limit for
    /// the underlying BDD operations.
    ///
    /// If the limit is exceeded, this function returns an error.
    pub fn mk_inhibition_with_limit(
        ctx: &SymbolicContext,
        fn_is_true: &Bdd,
        input: VariableId,
        limit: usize,
    ) -> Result<Bdd, SizeLimitExceeded> {
        let input_variable = ctx.get_state_variable(input);
        let input_is_true = ctx.bdd_variable_set().mk_var(input_variable);
        let input_is_false = input_is_true.not();
        let fn_is_false = fn_is_true.not();

        let fn_is_false_then_input_false =
            Bdd::binary_op_with_limit(limit, &fn_is_false, &input_is_false, and)
                .ok_or_else(|| SizeLimitExceeded::new(limit))?;
        // TODO: This can be a source of memory issues.
        let fn_x0_to_0 = fn_is_false_then_input_false.var_exists(input_variable);

        let fn_is_true_then_input_true =
            Bdd::binary_op_with_limit(limit, fn_is_true, &input_is_true, and)
                .ok_or_else(|| SizeLimitExceeded::new(limit))?;
        // TODO: This can be a source of memory issues.
        let fn_x1_to_1 = fn_is_true_then_input_true.var_exists(input_variable);

        let result = Bdd::binary_op_with_limit(limit, &fn_x0_to_0, &fn_x1_to_1, and)
            .ok_or_else(|| SizeLimitExceeded::new(limit))?;

        // TODO: This can be a source of memory issues.
        Ok(result.exists(ctx.state_variables()).not())
    }

    /// The same as [RegulationConstraint::mk_activation], but with negative monotonicity instead
    /// of positive monotonicity.
    ///
    /// Note that this version panics if the underlying BDD operations exceed the default memory
    /// limit. If you want to handle this case gracefully, use
    /// [RegulationConstraint::mk_inhibition_with_limit].
    pub fn mk_inhibition(ctx: &SymbolicContext, fn_is_true: &Bdd, input: VariableId) -> Bdd {
        Self::mk_inhibition_with_limit(ctx, fn_is_true, input, usize::MAX).unwrap()
    }

    /// A version of [RegulationConstraint::infer_sufficient_regulation] that accepts a node
    /// limit for the underlying BDD operations.
    ///
    /// If the limit is exceeded, this function returns an error.
    pub fn infer_sufficient_regulation_with_limit(
        ctx: &SymbolicContext,
        regulator: VariableId,
        target: VariableId,
        fn_is_true: &Bdd,
        limit: usize,
    ) -> Result<Option<Regulation>, SizeLimitExceeded> {
        let inputs = ctx.input_parameter_variables();

        let obs = Self::mk_observability_with_limit(ctx, fn_is_true, regulator, limit)?;
        // TODO: This can be a source of memory issues.
        let obs = obs.exists(&inputs);
        let observable = if obs.is_true() {
            true
        } else if !obs.is_false() {
            false
        } else {
            return Ok(None);
        };

        let act = Self::mk_activation_with_limit(ctx, fn_is_true, regulator, limit)?;
        // TODO: This can be a source of memory issues.
        let act = act.for_all(&inputs);
        let inh = Self::mk_inhibition_with_limit(ctx, fn_is_true, regulator, limit)?;
        // TODO: This can be a source of memory issues.
        let inh = inh.for_all(&inputs);

        let monotonicity = if act.is_true() {
            Some(Monotonicity::Activation)
        } else if inh.is_true() {
            Some(Monotonicity::Inhibition)
        } else {
            None
        };

        Ok(Some(Regulation {
            regulator,
            target,
            observable,
            monotonicity,
        }))
    }

    /// Infer the *most specific* [Regulation] which is still sufficient to correctly
    /// cover the relationship between `regulator` and `target` in the provided function
    /// (represented as a `fn_is_true` [Bdd]).
    ///
    /// Note that this version panics if the underlying BDD operations exceed the default memory
    /// limit. If you want to handle this case gracefully, use
    /// [RegulationConstraint::infer_sufficient_regulation_with_limit].
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
        Self::infer_sufficient_regulation_with_limit(ctx, regulator, target, fn_is_true, usize::MAX)
            .unwrap()
    }

    /// A version of [RegulationConstraint::fix_regulation] that accepts a node limit for
    /// the underlying BDD operations.
    ///
    /// If the limit is exceeded, this function returns an error.
    pub fn fix_regulation_with_limit(
        ctx: &SymbolicContext,
        old_regulation: &Regulation,
        fn_is_true: &Bdd,
        limit: usize,
    ) -> Result<Option<Regulation>, SizeLimitExceeded> {
        let inputs = ctx.input_parameter_variables();

        let obs =
            Self::mk_observability_with_limit(ctx, fn_is_true, old_regulation.regulator, limit)?;
        // TODO: This can be a source of memory issues.
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
            return Ok(None);
        };

        let act =
            Self::mk_activation_with_limit(ctx, fn_is_true, old_regulation.regulator, limit)?;
        // TODO: This can be a source of memory issues.
        let act = act.for_all(&inputs);
        let inh =
            Self::mk_inhibition_with_limit(ctx, fn_is_true, old_regulation.regulator, limit)?;
        // TODO: This can be a source of memory issues.
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

        Ok(Some(Regulation {
            regulator: old_regulation.regulator,
            target: old_regulation.target,
            observable,
            monotonicity,
        }))
    }

    /// Similar to [Self::infer_sufficient_regulation], but it tries to keep the constraints
    /// from the given `old_regulation` assuming they are satisfiable and more restrictive
    /// than the inferred constraints.
    ///
    /// Note that this version panics if the underlying BDD operations exceed the default memory
    /// limit. If you want to handle this case gracefully, use
    /// [RegulationConstraint::fix_regulation_with_limit].
    pub fn fix_regulation(
        ctx: &SymbolicContext,
        old_regulation: &Regulation,
        fn_is_true: &Bdd,
    ) -> Option<Regulation> {
        Self::fix_regulation_with_limit(ctx, old_regulation, fn_is_true, usize::MAX).unwrap()
    }
}

/// A version of `apply_regulation_constraints` that accepts a `limit` for node count of the
/// underlying BDD operations.
///
/// If the limit is exceeded, this function returns an error.
pub(crate) fn apply_regulation_constraints_with_limit(
    initial: Bdd,
    network: &BooleanNetwork,
    context: &SymbolicContext,
    limit: usize,
) -> Result<Result<Bdd, String>, SizeLimitExceeded> {
    // Detect "input parameters". For these, we don't actually want to apply any restrictions,
    // as these are typically just variables that are converted into parameters. Therefore,
    // they *can* have both values, even though one of them would make a particular constraint
    // not satisfied.
    let inputs = context.input_parameter_variables();

    // For each variable, compute Bdd that is true exactly when its update function is true.
    let mut update_function_is_true: Vec<Bdd> = Vec::new();
    for variable in network.variables() {
        let function_bdd = if let Some(function) = network.get_update_function(variable) {
            context.mk_fn_update_true_with_limit(function, limit)?
        } else {
            context.mk_implicit_function_is_true_with_limit(
                variable,
                &network.regulators(variable),
                limit,
            )?
        };
        update_function_is_true.push(function_bdd);
    }

    let mut error_message = String::new();
    let mut unit_bdd = initial;
    for regulation in &network.graph.regulations {
        let regulator = regulation.regulator;
        let fn_is_true = &update_function_is_true[regulation.target.to_index()];

        let observability = if regulation.observable {
            RegulationConstraint::mk_observability_with_limit(context, fn_is_true, regulator, limit)?
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
                RegulationConstraint::mk_activation_with_limit(context, fn_is_true, regulator, limit)?
            }
            Some(Monotonicity::Inhibition) => {
                RegulationConstraint::mk_inhibition_with_limit(context, fn_is_true, regulator, limit)?
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

        let both = Bdd::binary_op_with_limit(limit, &monotonicity, &observability, and)
            .ok_or_else(|| SizeLimitExceeded::new(limit))?;
        unit_bdd = Bdd::binary_op_with_limit(limit, &unit_bdd, &both, and)
            .ok_or_else(|| SizeLimitExceeded::new(limit))?;
    }

    if unit_bdd.is_false() {
        Ok(Err(format!(
            "No update functions satisfy given constraints: \n{}",
            error_message
        )))
    } else {
        Ok(Ok(unit_bdd))
    }
}

/// Compute a `Bdd` which is a subset of the `initial` valuations that satisfies all
/// constraints imposed by the given Boolean `network`.
///
/// Note that this version panics if the underlying BDD operations exceed the default memory
/// limit. If you want to handle this case gracefully, use
/// [apply_regulation_constraints_with_limit].
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
    apply_regulation_constraints_with_limit(initial, network, context, usize::MAX).unwrap()
}

#[cfg(test)]
mod tests {
    use crate::symbolic_async_graph::_impl_regulation_constraint::apply_regulation_constraints;
    use crate::symbolic_async_graph::{
        RegulationConstraint, SizeLimitExceeded, SymbolicAsyncGraph, SymbolicContext,
    };
    use crate::Monotonicity::{Activation, Inhibition};
    use crate::{BooleanNetwork, Regulation, VariableId};

    #[test]
    fn test_observability_limit() {
        let bn = BooleanNetwork::try_from(
            r"
            a -> b
            $b: a & a & a & a & a & a & a & a & a & a & a & a & a & a & a & a & a & a & a
        ",
        )
        .unwrap();
        let ctx = SymbolicContext::new(&bn).unwrap();
        let graph = SymbolicAsyncGraph::new(&bn).unwrap();
        let a = bn.as_graph().find_variable("a").unwrap();
        let b = bn.as_graph().find_variable("b").unwrap();
        let b_is_true = graph.get_symbolic_fn_update(b);
        let result =
            RegulationConstraint::mk_observability_with_limit(&ctx, b_is_true, a, 100);
        assert!(result.is_ok());
        let result = result.unwrap();
        assert!(!result.is_false());
        let result = RegulationConstraint::mk_observability_with_limit(&ctx, b_is_true, a, 2);
        assert!(matches!(result, Err(SizeLimitExceeded { .. })));
    }

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
