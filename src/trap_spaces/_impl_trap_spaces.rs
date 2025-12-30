use crate::biodivine_std::traits::Set;
use crate::fixed_points::FixedPoints;
use crate::symbolic_async_graph::{GraphColoredVertices, SymbolicAsyncGraph};
use crate::trap_spaces::{NetworkColoredSpaces, SymbolicSpaceContext, TrapSpaces};
use crate::{global_log_level, log_essential, should_log};
use biodivine_lib_bdd::bdd;
use cancel_this::{Cancellable, is_cancelled};
use std::collections::HashSet;

impl TrapSpaces {
    /// Computes the coloured subset of "essential" trap spaces of a Boolean network.
    ///
    /// A trap space is essential if it cannot be reduced to a smaller trap space through
    /// percolation. In general, every minimal trap space is always essential.
    ///
    /// Note that this set corresponds exactly to the vertices of a
    /// [succession diagram](https://jcrozum.github.io/biobalm/autoapi/biobalm/index.html).
    pub fn essential_symbolic(
        ctx: &SymbolicSpaceContext,
        graph: &SymbolicAsyncGraph,
        restriction: &NetworkColoredSpaces,
    ) -> NetworkColoredSpaces {
        Self::_essential_symbolic(ctx, graph, restriction, global_log_level()).unwrap()
    }

    /// A version of [TrapSpaces::essential_symbolic] with cancellation
    /// and logging.
    ///
    /// Cancellation implemented using [cancel-this](https://crates.io/crates/cancel-this).
    /// For more information, see crate documentation.
    pub fn _essential_symbolic(
        ctx: &SymbolicSpaceContext,
        graph: &SymbolicAsyncGraph,
        restriction: &NetworkColoredSpaces,
        log_level: usize,
    ) -> Cancellable<NetworkColoredSpaces> {
        if should_log(log_level) {
            println!(
                "Start symbolic essential trap space search with {}[nodes:{}] candidates.",
                restriction.approx_cardinality(),
                restriction.symbolic_size()
            );
        }

        let bdd_ctx = ctx.bdd_variable_set();

        // We always start with the restriction set because it should carry the information
        // about valid encoding of spaces.
        let mut to_merge = vec![restriction.as_bdd().clone()];
        for var in graph.variables() {
            let update_bdd = graph.get_symbolic_fn_update(var);
            let not_update_bdd = update_bdd.not();
            is_cancelled!()?;

            let has_up_transition = ctx._mk_can_go_to_true(update_bdd, log_level)?;
            is_cancelled!()?;

            let has_down_transition = ctx._mk_can_go_to_true(&not_update_bdd, log_level)?;
            is_cancelled!()?;

            let true_var = ctx.get_positive_variable(var);
            let false_var = ctx.get_negative_variable(var);

            let is_trap_1 = has_up_transition.imp(&bdd_ctx.mk_var(true_var));
            let is_trap_2 = has_down_transition.imp(&bdd_ctx.mk_var(false_var));
            let is_trap = is_trap_1.and(&is_trap_2);
            is_cancelled!()?;

            let is_essential_1 = bdd_ctx.mk_var(true_var).and(&bdd_ctx.mk_var(false_var));
            let is_essential_2 = has_up_transition.and(&has_down_transition);
            let is_essential = is_essential_1.imp(&is_essential_2);
            is_cancelled!()?;

            // This will work in next version of lib-bdd:
            // let is_trap = bdd!(bdd_ctx, (has_up_transition => true_var) & (has_down_transition => false_var));
            // let is_essential = bdd!(bdd_ctx, (true_var & false_var) => (has_up_transition & has_down_transition));

            if log_essential(log_level, is_trap.size() + is_essential.size()) {
                println!(
                    " > Created initial sets for {:?} using {}+{} BDD nodes.",
                    var,
                    is_trap.size(),
                    is_essential.size(),
                );
            }

            to_merge.push(is_trap.and(&is_essential));
        }

        let trap_spaces =
            FixedPoints::_symbolic_merge(bdd_ctx, to_merge, HashSet::default(), log_level)?;
        let trap_spaces = NetworkColoredSpaces::new(trap_spaces, ctx);
        is_cancelled!()?;

        if should_log(log_level) {
            println!(
                "Found {}x{}[nodes:{}] essential trap spaces.",
                trap_spaces.colors().approx_cardinality(),
                trap_spaces.spaces().approx_cardinality(),
                trap_spaces.symbolic_size(),
            );
        }

        Ok(trap_spaces)
    }

    /// Compute the set of long-lived subspaces of the given networ.
    ///
    /// A subspace is long-lived if:
    ///  - It contains both up and down transitions in every free variable.
    ///  - For every fixed variable, there is at least one state where this value can be obtained
    ///    as a result of the corresponding update function (it cannot be escaped by percolation).
    ///
    /// Intuitively, such trap spaces over-approximate possible oscillations across different
    /// update schemes of the Boolean network. **Currently, this is an experimental feature
    /// and the semantics of this function can change in the future.**
    pub fn long_lived_symbolic(
        ctx: &SymbolicSpaceContext,
        graph: &SymbolicAsyncGraph,
        restriction: &NetworkColoredSpaces,
    ) -> NetworkColoredSpaces {
        Self::_long_lived_symbolic(ctx, graph, restriction, global_log_level()).unwrap()
    }
    /// A version of [TrapSpaces::long_lived_symbolic] with cancellation
    /// and logging.
    ///
    /// Cancellation implemented using [cancel-this](https://crates.io/crates/cancel-this).
    /// For more information, see crate documentation.
    pub fn _long_lived_symbolic(
        ctx: &SymbolicSpaceContext,
        graph: &SymbolicAsyncGraph,
        restriction: &NetworkColoredSpaces,
        log_level: usize,
    ) -> Cancellable<NetworkColoredSpaces> {
        if should_log(log_level) {
            println!(
                "Start symbolic long-lived trap space search with {}[nodes:{}] candidates.",
                restriction.approx_cardinality(),
                restriction.symbolic_size()
            );
        }

        let bdd_ctx = ctx.bdd_variable_set();

        // We always start with the restriction set because it should carry the information
        // about valid encoding of spaces.
        let mut to_merge = vec![restriction.as_bdd().clone()];
        for var in graph.variables() {
            let bdd_var = ctx.get_state_variable(var);
            let update_bdd = graph.get_symbolic_fn_update(var);
            let not_update_bdd = &update_bdd.not();
            is_cancelled!()?;

            let has_one = ctx._mk_can_go_to_true(update_bdd, log_level)?;
            let has_zero = ctx._mk_can_go_to_true(not_update_bdd, log_level)?;
            is_cancelled!()?;

            let up_states = update_bdd.var_select(bdd_var, false);
            let goes_up = ctx._mk_can_go_to_true(&up_states, log_level)?;
            is_cancelled!()?;

            let down_states = not_update_bdd.var_select(bdd_var, true);
            let goes_down = ctx._mk_can_go_to_true(&down_states, log_level)?;
            is_cancelled!()?;

            let true_var = ctx.get_positive_variable(var);
            let false_var = ctx.get_negative_variable(var);

            // Is essential: If subspace has var=*, then it must contain up and down transitions.
            let is_live = bdd!(bdd_ctx, (true_var & false_var) => (goes_up & goes_down));
            is_cancelled!()?;

            // Cannot percolate (0): If var=0, then f(x)=0 for some state x.
            // Cannot percolate (1): If var=1, then f(x)=1 for some state x.
            let cannot_percolate_0 = bdd!(bdd_ctx, ((!true_var) & false_var) => has_zero);
            let cannot_percolate_1 = bdd!(bdd_ctx, (true_var & (!false_var)) => has_one);
            let cannot_percolate = bdd!(cannot_percolate_0 & cannot_percolate_1);
            is_cancelled!()?;

            if log_essential(log_level, cannot_percolate.size() + is_live.size()) {
                println!(
                    " > Created initial sets for {:?} using {}+{} BDD nodes.",
                    var,
                    cannot_percolate.size(),
                    is_live.size(),
                );
            }

            to_merge.push(cannot_percolate.and(&is_live));
        }

        let live_spaces =
            FixedPoints::_symbolic_merge(bdd_ctx, to_merge, HashSet::default(), log_level)?;
        let long_lived_spaces = NetworkColoredSpaces::new(live_spaces, ctx);
        is_cancelled!()?;

        if should_log(log_level) {
            println!(
                "Found {}x{}[nodes:{}] long-lived spaces.",
                long_lived_spaces.colors().approx_cardinality(),
                long_lived_spaces.spaces().approx_cardinality(),
                long_lived_spaces.symbolic_size(),
            );
        }

        Ok(long_lived_spaces)
    }

    /// Computes the minimal colored trap spaces of the provided `network` within the specified
    /// `restriction` set.
    ///
    /// This is similar to running [Self::essential_symbolic] and [Self::minimize], but the
    /// method adds an extra optional optimization step. Before computing all "non-trivial"
    /// minimal trap spaces, it can first exclude all trap spaces that are already known to
    /// contain a fixed-point (given as the `exclude_fixed_points` parameter). **These fixed points
    /// then won't be part of the result.** In some cases, this can help speed up trap space
    /// search. However, it is not universally better and is therefore left as an
    /// optional parameter (if the set of fixed points is very complex, it can complicate the
    /// trap space search, even though the number of results is strictly smaller). Note that
    /// the method assumes the provided `exclude_fixed_points` set is correct, i.e., it won't check
    /// that it only contains fixed points. In theory, you can also use this to exclude
    /// super-spaces of any vertex.
    ///
    pub fn minimal_symbolic(
        ctx: &SymbolicSpaceContext,
        graph: &SymbolicAsyncGraph,
        restriction: &NetworkColoredSpaces,
        exclude_fixed_points: Option<&GraphColoredVertices>,
    ) -> NetworkColoredSpaces {
        Self::_minimal_symbolic(
            ctx,
            graph,
            restriction,
            exclude_fixed_points,
            global_log_level(),
        )
        .unwrap()
    }

    /// A version of [TrapSpaces::minimal_symbolic] with cancellation
    /// and logging.
    ///
    /// Cancellation implemented using [cancel-this](https://crates.io/crates/cancel-this).
    /// For more information, see crate documentation.
    pub fn _minimal_symbolic(
        ctx: &SymbolicSpaceContext,
        graph: &SymbolicAsyncGraph,
        restriction: &NetworkColoredSpaces,
        exclude_fixed_points: Option<&GraphColoredVertices>,
        log_level: usize,
    ) -> Cancellable<NetworkColoredSpaces> {
        let restriction = if let Some(exclude_fixed_points) = exclude_fixed_points {
            if should_log(log_level) {
                println!(
                    "Prepare for minimal trap space computation by first eliminating provided fixed-points."
                );
            }
            let fixed_points = exclude_fixed_points.to_singleton_spaces(ctx);
            let fix_super_spaces = ctx._mk_super_spaces(fixed_points.as_bdd(), log_level)?;
            let fix_super_spaces = NetworkColoredSpaces::new(fix_super_spaces, ctx);
            let restriction = restriction.minus(&fix_super_spaces);
            if should_log(log_level) {
                println!(
                    "Fixed points eliminated. Restriction set reduced to {} elements.",
                    restriction.exact_cardinality()
                );
            }
            restriction
        } else {
            restriction.clone()
        };
        let essential = Self::_essential_symbolic(ctx, graph, &restriction, log_level)?;
        Self::_minimize(ctx, &essential, log_level)
    }

    /// Compute the minimal spaces within a particular subset.
    pub fn minimize(
        ctx: &SymbolicSpaceContext,
        spaces: &NetworkColoredSpaces,
    ) -> NetworkColoredSpaces {
        Self::_minimize(ctx, spaces, global_log_level()).unwrap()
    }

    /// A version of [TrapSpaces::minimize] with cancellation
    /// and logging.
    ///
    /// Cancellation implemented using [cancel-this](https://crates.io/crates/cancel-this).
    /// For more information, see crate documentation.
    pub fn _minimize(
        ctx: &SymbolicSpaceContext,
        spaces: &NetworkColoredSpaces,
        log_level: usize,
    ) -> Cancellable<NetworkColoredSpaces> {
        let mut remaining = spaces.clone();
        let mut minimal = ctx.mk_empty_colored_spaces();
        if should_log(log_level) {
            println!(
                "Start minimal subspace search with {}x{}[nodes:{}] candidates.",
                remaining.colors().approx_cardinality(),
                remaining.spaces().approx_cardinality(),
                remaining.symbolic_size()
            );
        }
        is_cancelled!()?;

        while !remaining.is_empty() {
            let most_fixed_path = remaining
                .spaces()
                .as_bdd()
                .most_negative_valuation()
                .unwrap();

            let mut free_vars = 0;
            for (t_var, f_var) in &ctx.dual_variables {
                if most_fixed_path[*t_var] && most_fixed_path[*f_var] {
                    free_vars += 1;
                }
            }

            let k_free = ctx.mk_exactly_k_free_spaces(free_vars);
            let k_minimal = remaining.intersect_spaces(&k_free);
            assert!(!k_minimal.is_empty());
            is_cancelled!()?;

            minimal = minimal.union(&k_minimal);
            is_cancelled!()?;

            let super_spaces = ctx._mk_super_spaces(k_minimal.as_bdd(), log_level)?;
            let super_spaces = NetworkColoredSpaces::new(super_spaces, ctx);
            remaining = remaining.minus(&super_spaces);
            is_cancelled!()?;

            if should_log(log_level) {
                println!(
                    "Minimization in progress: {}x{}[nodes:{}] unprocessed, {}x{}[nodes:{}] minimal spaces found, at most {} free variables tested.",
                    remaining.colors().approx_cardinality(),
                    remaining.spaces().approx_cardinality(),
                    remaining.symbolic_size(),
                    minimal.colors().approx_cardinality(),
                    minimal.spaces().approx_cardinality(),
                    minimal.symbolic_size(),
                    free_vars,
                );
            }
        }

        if should_log(log_level) {
            println!(
                "Found {}[nodes:{}] minimal spaces.",
                minimal.exact_cardinality(),
                minimal.symbolic_size(),
            );
        }

        Ok(minimal)
    }

    /// The same as [Self::minimize], but searches for maximal spaces within `spaces`.
    pub fn maximize(
        ctx: &SymbolicSpaceContext,
        spaces: &NetworkColoredSpaces,
    ) -> NetworkColoredSpaces {
        Self::_maximize(ctx, spaces, global_log_level()).unwrap()
    }

    /// A version of [TrapSpaces::maximize] with cancellation
    /// and logging.
    ///
    /// Cancellation implemented using [cancel-this](https://crates.io/crates/cancel-this).
    /// For more information, see crate documentation.
    pub fn _maximize(
        ctx: &SymbolicSpaceContext,
        spaces: &NetworkColoredSpaces,
        log_level: usize,
    ) -> Cancellable<NetworkColoredSpaces> {
        let mut remaining = spaces.clone();
        let mut maximal = ctx.mk_empty_colored_spaces();
        if should_log(log_level) {
            println!(
                "Start maximal subspace search with {}x{}[nodes:{}] candidates.",
                remaining.colors().approx_cardinality(),
                remaining.spaces().approx_cardinality(),
                remaining.symbolic_size()
            );
        }
        is_cancelled!()?;

        while !remaining.is_empty() {
            let most_free_path = remaining
                .spaces()
                .as_bdd()
                .most_positive_valuation()
                .unwrap();

            let mut free_vars = 0;
            for (t_var, f_var) in &ctx.dual_variables {
                if most_free_path[*t_var] && most_free_path[*f_var] {
                    free_vars += 1;
                }
            }

            let k_free = ctx.mk_exactly_k_free_spaces(free_vars);
            let k_maximal = remaining.intersect_spaces(&k_free);
            assert!(!k_maximal.is_empty());
            is_cancelled!()?;

            maximal = maximal.union(&k_maximal);
            is_cancelled!()?;

            let sub_spaces = ctx._mk_sub_spaces(k_maximal.as_bdd(), log_level)?;
            let sub_spaces = NetworkColoredSpaces::new(sub_spaces, ctx);
            remaining = remaining.minus(&sub_spaces);
            is_cancelled!()?;

            if should_log(log_level) {
                println!(
                    "Maximization in progress: {}x{}[nodes:{}] unprocessed, {}x{}[nodes:{}] maximal spaces found, at least {} free variables tested.",
                    remaining.colors().approx_cardinality(),
                    remaining.spaces().approx_cardinality(),
                    remaining.symbolic_size(),
                    maximal.colors().approx_cardinality(),
                    maximal.spaces().approx_cardinality(),
                    maximal.symbolic_size(),
                    free_vars,
                );
            }
        }

        if should_log(log_level) {
            println!(
                "Found {}[nodes:{}] maximal spaces.",
                maximal.exact_cardinality(),
                maximal.symbolic_size(),
            );
        }

        Ok(maximal)
    }
}

#[cfg(test)]
mod tests {
    use crate::BooleanNetwork;
    use crate::biodivine_std::traits::Set;
    use crate::fixed_points::FixedPoints;
    use crate::symbolic_async_graph::SymbolicAsyncGraph;
    use crate::trap_spaces::{SymbolicSpaceContext, TrapSpaces};

    #[test]
    fn test_trap_spaces() {
        let network = BooleanNetwork::try_from_file("./aeon_models/005.aeon").unwrap();
        let ctx = SymbolicSpaceContext::new(&network);
        let stg = SymbolicAsyncGraph::with_space_context(&network, &ctx).unwrap();
        let unit = ctx.mk_unit_colored_spaces(&stg);

        let fix = FixedPoints::symbolic(&stg, stg.unit_colored_vertices());
        let essential_traps = TrapSpaces::essential_symbolic(&ctx, &stg, &unit);
        let long_lived_traps = TrapSpaces::long_lived_symbolic(&ctx, &stg, &unit);
        let minimal_traps = TrapSpaces::minimal_symbolic(&ctx, &stg, &unit, None);
        let minimal_traps_minus_fix = TrapSpaces::minimal_symbolic(&ctx, &stg, &unit, Some(&fix));
        let maximal_traps = TrapSpaces::maximize(&ctx, &essential_traps);

        assert_eq!(
            minimal_traps_minus_fix,
            minimal_traps.minus(&fix.to_singleton_spaces(&ctx))
        );

        assert!(minimal_traps.is_subset(&essential_traps));
        assert!(maximal_traps.is_subset(&essential_traps));
        assert!(minimal_traps.is_subset(&long_lived_traps));
        assert_eq!(7.0, essential_traps.approx_cardinality());
        assert_eq!(7, essential_traps.spaces().iter().count());
        assert_eq!(1.0, minimal_traps.approx_cardinality());
        assert_eq!(1.0, maximal_traps.approx_cardinality());
        // The number of long-lived traps is quite high in this model...
        assert_eq!(16853358.0, long_lived_traps.approx_cardinality());

        assert!(minimal_traps.is_singleton());
        assert!(maximal_traps.is_singleton());
        assert!(!essential_traps.is_singleton());
    }
}
