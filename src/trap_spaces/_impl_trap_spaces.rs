use crate::biodivine_std::traits::Set;
use crate::fixed_points::FixedPoints;
use crate::symbolic_async_graph::{GraphColoredVertices, SymbolicAsyncGraph};
use crate::trap_spaces::{NetworkColoredSpaces, SymbolicSpaceContext, TrapSpaces};
use crate::{global_log_level, log_essential, never_stop, should_log};
use std::collections::HashSet;

impl TrapSpaces {
    /// Computes the coloured subset of "essential" trap spaces of a Boolean network.
    ///
    /// A trap space is essential if it cannot be reduced through percolation. In general, every
    /// minimal trap space is always essential.
    pub fn essential_symbolic(
        ctx: &SymbolicSpaceContext,
        graph: &SymbolicAsyncGraph,
        restriction: &NetworkColoredSpaces,
    ) -> NetworkColoredSpaces {
        Self::_essential_symbolic(ctx, graph, restriction, global_log_level(), &never_stop).unwrap()
    }

    /// A version of [TrapSpaces::essential_symbolic] with cancellation
    /// and logging.
    pub fn _essential_symbolic<E, F: Fn() -> Result<(), E>>(
        ctx: &SymbolicSpaceContext,
        graph: &SymbolicAsyncGraph,
        restriction: &NetworkColoredSpaces,
        log_level: usize,
        interrupt: &F,
    ) -> Result<NetworkColoredSpaces, E> {
        if should_log(log_level) {
            println!(
                "Start symbolic essential trap space search with {}[nodes:{}] candidates.",
                restriction.approx_cardinality(),
                restriction.symbolic_size()
            );
        }

        let bdd_ctx = ctx.bdd_variable_set();

        // We always start with the restriction set, because it should carry the information
        // about valid encoding of spaces.
        let mut to_merge = vec![restriction.as_bdd().clone()];
        for var in graph.variables() {
            let update_bdd = graph.get_symbolic_fn_update(var);
            let not_update_bdd = update_bdd.not();
            interrupt()?;

            let has_up_transition = ctx._mk_can_go_to_true(update_bdd, log_level, interrupt)?;
            interrupt()?;

            let has_down_transition =
                ctx._mk_can_go_to_true(&not_update_bdd, log_level, interrupt)?;
            interrupt()?;

            let true_var = ctx.get_positive_variable(var);
            let false_var = ctx.get_negative_variable(var);

            let is_trap_1 = has_up_transition.imp(&bdd_ctx.mk_var(true_var));
            let is_trap_2 = has_down_transition.imp(&bdd_ctx.mk_var(false_var));
            let is_trap = is_trap_1.and(&is_trap_2);
            interrupt()?;

            let is_essential_1 = bdd_ctx.mk_var(true_var).and(&bdd_ctx.mk_var(false_var));
            let is_essential_2 = has_up_transition.and(&has_down_transition);
            let is_essential = is_essential_1.imp(&is_essential_2);
            interrupt()?;

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

        let trap_spaces = FixedPoints::_symbolic_merge(
            bdd_ctx,
            to_merge,
            HashSet::default(),
            log_level,
            interrupt,
        )?;
        let trap_spaces = NetworkColoredSpaces::new(trap_spaces, ctx);
        interrupt()?;

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

    /// Computes the minimal coloured trap spaces of the provided `network` within the specified
    /// `restriction` set.
    ///
    /// This is similar to running [Self::essential_symbolic] and [Self::minimize], but the
    /// method adds an extra optional optimization step. Before computing all "non-trivial"
    /// minimal trap spaces, it can first exclude all trap spaces that are already known to
    /// contain a fixed-point (given as `exclude_fixed_points` parameter). **These fixed points
    /// then won't be part of the result.** In some cases, this can help speed up trap space
    /// search. However, it is not universally better and is therefore left as an
    /// optional parameter (if the set of fixed points is very complex, it can complicate the
    /// trap space search, even though the number of results is strictly smaller). Note that
    /// the method assumes the provided `exclude_fixed_points` set is correct, i.e. it won't check
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
            &never_stop,
        )
        .unwrap()
    }

    /// A version of [TrapSpaces::minimal_symbolic] with cancellation
    /// and logging.
    pub fn _minimal_symbolic<E, F: Fn() -> Result<(), E>>(
        ctx: &SymbolicSpaceContext,
        graph: &SymbolicAsyncGraph,
        restriction: &NetworkColoredSpaces,
        exclude_fixed_points: Option<&GraphColoredVertices>,
        log_level: usize,
        interrupt: &F,
    ) -> Result<NetworkColoredSpaces, E> {
        let restriction = if let Some(exclude_fixed_points) = exclude_fixed_points {
            if should_log(log_level) {
                println!(
                    "Prepare for minimal trap space computation by first eliminating provided fixed-points."
                );
            }
            let fixed_points = exclude_fixed_points.to_singleton_spaces(ctx);
            let fix_super_spaces =
                ctx._mk_super_spaces(fixed_points.as_bdd(), log_level, interrupt)?;
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
        let essential = Self::_essential_symbolic(ctx, graph, &restriction, log_level, interrupt)?;
        Self::_minimize(ctx, &essential, log_level, interrupt)
    }

    /// Compute the minimal spaces within a particular subset.
    pub fn minimize(
        ctx: &SymbolicSpaceContext,
        spaces: &NetworkColoredSpaces,
    ) -> NetworkColoredSpaces {
        Self::_minimize(ctx, spaces, global_log_level(), &never_stop).unwrap()
    }

    /// A version of [TrapSpaces::minimize] with cancellation
    /// and logging.
    pub fn _minimize<E, F: Fn() -> Result<(), E>>(
        ctx: &SymbolicSpaceContext,
        spaces: &NetworkColoredSpaces,
        log_level: usize,
        interrupt: &F,
    ) -> Result<NetworkColoredSpaces, E> {
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
        interrupt()?;

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
            interrupt()?;

            minimal = minimal.union(&k_minimal);
            interrupt()?;

            let super_spaces = ctx.mk_super_spaces(minimal.as_bdd());
            let super_spaces = NetworkColoredSpaces::new(super_spaces, ctx);
            remaining = remaining.minus(&super_spaces);
            interrupt()?;

            if log_essential(
                log_level,
                remaining.symbolic_size() + minimal.symbolic_size(),
            ) {
                println!(
                    "Minimization in progress: {}x{}[nodes:{}] unprocessed, {}x{}[nodes:{}] minimal traps found, at most {} free variables tested.",
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
        Self::_maximize(ctx, spaces, global_log_level(), &never_stop).unwrap()
    }

    /// A version of [TrapSpaces::maximize] with cancellation
    /// and logging.
    pub fn _maximize<E, F: Fn() -> Result<(), E>>(
        ctx: &SymbolicSpaceContext,
        spaces: &NetworkColoredSpaces,
        log_level: usize,
        interrupt: &F,
    ) -> Result<NetworkColoredSpaces, E> {
        let mut original = spaces.clone();
        let mut maximal = ctx.mk_empty_colored_spaces();

        if should_log(log_level) {
            println!(
                "Start maximal subspace search with {}x{}[nodes:{}] candidates.",
                original.colors().approx_cardinality(),
                original.spaces().approx_cardinality(),
                original.symbolic_size()
            );
        }

        while !original.is_empty() {
            let maximum_candidate = original.pick_space();
            interrupt()?;

            // Compute the set of strict sub spaces.
            let super_spaces = ctx.mk_sub_spaces(maximum_candidate.as_bdd());
            let super_spaces = NetworkColoredSpaces::new(super_spaces, ctx);
            interrupt()?;

            original = original.minus(&super_spaces);
            maximal = maximal.minus(&super_spaces).union(&maximum_candidate);
            interrupt()?;

            if log_essential(
                log_level,
                original.symbolic_size() + maximal.symbolic_size(),
            ) {
                println!(
                    "Maximization in progress: {}x{}[nodes:{}] unprocessed, {}x{}[nodes:{}] candidates.",
                    original.colors().approx_cardinality(),
                    original.spaces().approx_cardinality(),
                    original.symbolic_size(),
                    maximal.colors().approx_cardinality(),
                    maximal.spaces().approx_cardinality(),
                    maximal.symbolic_size(),
                );
            }
        }

        if should_log(log_level) {
            println!(
                "Found {}[nodes:{}] maximal spaces.",
                maximal.approx_cardinality(),
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
        let minimal_traps = TrapSpaces::minimal_symbolic(&ctx, &stg, &unit, None);
        let minimal_traps_minus_fix = TrapSpaces::minimal_symbolic(&ctx, &stg, &unit, Some(&fix));
        let maximal_traps = TrapSpaces::maximize(&ctx, &essential_traps);

        assert_eq!(
            minimal_traps_minus_fix,
            minimal_traps.minus(&fix.to_singleton_spaces(&ctx))
        );

        assert!(minimal_traps.is_subset(&essential_traps));
        assert!(maximal_traps.is_subset(&essential_traps));
        assert_eq!(7.0, essential_traps.approx_cardinality());
        assert_eq!(7, essential_traps.spaces().iter().count());
        assert_eq!(1.0, minimal_traps.approx_cardinality());
        assert_eq!(1.0, maximal_traps.approx_cardinality());

        assert!(minimal_traps.is_singleton());
        assert!(maximal_traps.is_singleton());
        assert!(!essential_traps.is_singleton());
    }
}
