use crate::symbolic_async_graph::{RegulationConstraint, SymbolicContext};
use crate::{BooleanNetwork, Monotonicity, Regulation, VariableId};
use biodivine_lib_bdd::{bdd, Bdd};
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
    /// an arbitrary symbolic function. Hence it can be used both to validate an existing
    /// regulatory graph, as well as to infer observability of an otherwise unspecified
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
    /// an arbitrary symbolic function. Hence it can be used both to validate an existing
    /// regulatory graph, as well as to infer observability of an otherwise unspecified
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
        let obs = Self::mk_observability(ctx, fn_is_true, regulator);
        let observable = if obs.is_true() {
            true
        } else if !obs.is_false() {
            false
        } else {
            return None;
        };

        let act = Self::mk_activation(ctx, fn_is_true, regulator);
        let inh = Self::mk_inhibition(ctx, fn_is_true, regulator);

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
}

/// Compute a `Bdd` which is a subset of the `initial` valuations that satisfies all
/// constraints imposed by the given Boolean `network`.
///
/// If there are no satisfying valuations, this function should return a human-readable
/// message which explains problem (often in several lines). However, in some complex
/// cases (inter-dependent parameters), this can be very hard and the error messages
/// are thus purely best effort service.
pub(crate) fn apply_regulation_constraints(
    initial: Bdd,
    network: &BooleanNetwork,
    context: &SymbolicContext,
) -> Result<Bdd, String> {
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
