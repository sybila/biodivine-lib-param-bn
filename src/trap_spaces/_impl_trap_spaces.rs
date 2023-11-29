use crate::biodivine_std::traits::Set;
use crate::fixed_points::FixedPoints;
use crate::trap_spaces::{NetworkColoredSpaces, SymbolicSpaceContext, TrapSpaces};
use crate::BooleanNetwork;
use std::collections::HashSet;

impl TrapSpaces {
    /// Computes the coloured subset of "essential" trap spaces of a Boolean network.
    ///
    /// A trap space is essential if it cannot be reduced through percolation. In general, every
    /// minimal trap space is always essential.
    pub fn essential_symbolic(
        network: &BooleanNetwork,
        ctx: &SymbolicSpaceContext,
        restriction: &NetworkColoredSpaces,
    ) -> NetworkColoredSpaces {
        if cfg!(feature = "print-progress") {
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
        for var in network.variables() {
            let update_bdd = if let Some(update) = network.get_update_function(var) {
                ctx.inner_context().mk_fn_update_true(update)
            } else {
                let regulators = network.regulators(var);
                ctx.inner_context()
                    .mk_implicit_function_is_true(var, &regulators)
            };
            let not_update_bdd = update_bdd.not();

            let has_up_transition = ctx.mk_can_go_to_true(&update_bdd);
            let has_down_transition = ctx.mk_can_go_to_true(&not_update_bdd);

            let true_var = ctx.get_positive_variable(var);
            let false_var = ctx.get_negative_variable(var);
            let is_trap_1 = has_up_transition.imp(&bdd_ctx.mk_var(true_var));
            let is_trap_2 = has_down_transition.imp(&bdd_ctx.mk_var(false_var));
            let is_trap = is_trap_1.and(&is_trap_2);
            let is_essential_1 = bdd_ctx.mk_var(true_var).and(&bdd_ctx.mk_var(false_var));
            let is_essential_2 = has_up_transition.and(&has_down_transition);
            let is_essential = is_essential_1.imp(&is_essential_2);
            // This will work in next version of lib-bdd:
            // let is_trap = bdd!(bdd_ctx, (has_up_transition => true_var) & (has_down_transition => false_var));
            // let is_essential = bdd!(bdd_ctx, (true_var & false_var) => (has_up_transition & has_down_transition));

            if cfg!(feature = "print-progress") {
                println!(
                    " > Created initial sets for {:?} using {}+{} BDD nodes.",
                    var,
                    is_trap.size(),
                    is_essential.size(),
                );
            }

            to_merge.push(is_trap.and(&is_essential));
            //to_merge.push(is_essential);
        }

        let trap_spaces = FixedPoints::symbolic_merge(bdd_ctx, to_merge, HashSet::default());

        let trap_spaces = NetworkColoredSpaces::new(trap_spaces, ctx);

        if cfg!(feature = "print-progress") {
            println!(
                "Found {}[nodes:{}] essential trap spaces.",
                trap_spaces.approx_cardinality(),
                trap_spaces.symbolic_size(),
            );
        }

        trap_spaces
    }

    /// Computes the minimal coloured trap spaces of the provided `network` within the specified
    /// `restriction` set.
    ///
    /// This method currently uses [Self::essential_symbolic], hence is always slower than
    /// this method.
    pub fn minimal_symbolic(
        network: &BooleanNetwork,
        ctx: &SymbolicSpaceContext,
        restriction: &NetworkColoredSpaces,
    ) -> NetworkColoredSpaces {
        let essential = Self::essential_symbolic(network, ctx, restriction);
        Self::minimize(ctx, &essential)
    }

    /// Compute the minimal spaces within a particular subset.
    pub fn minimize(
        ctx: &SymbolicSpaceContext,
        spaces: &NetworkColoredSpaces,
    ) -> NetworkColoredSpaces {
        let mut original = spaces.clone();
        let mut minimal = ctx.mk_empty_colored_spaces();

        if cfg!(feature = "print-progress") {
            println!(
                "Start minimal space search with {}[nodes:{}] candidates.",
                original.approx_cardinality(),
                original.symbolic_size()
            );
        }

        while !original.is_empty() {
            // TODO:
            //  The pick-space process could probably be optimized somewhat to prioritize
            //  the most specific trap spaces (most "false" dual variables) instead of any
            //  just any trap space. On the other hand, the pick method already favors "lower"
            //  valuations, so there might not be that much space for improvement.

            // TODO:
            //  The other option would be to also consider sub-spaces and basically do something
            //  like normal attractor search, where next candidate is picked only from the
            //  sub-spaces of the original pick. This would guarantee that every iteration always
            //  discovers a minimal trap space, but it could just mean extra overhead if the
            //  "greedy" method using pick is good enough. Initial tests indicate that the
            //  greedy approach is enough.
            let minimum_candidate = original.pick_space();
            // Compute the set of strict super spaces.
            // TODO:
            //  This can take a long time if there are colors and a lot of traps, e.g.
            //  fixed-points, even though individual colors are easy. We should probably
            //  find a way to get rid of fixed points and any related super-spaces first,
            //  as these are clearly minimal. The other option would be to tune the super
            //  space enumeration to avoid spaces that are clearly irrelevant anyway.
            let super_spaces = ctx.mk_super_spaces(minimum_candidate.as_bdd());
            let super_spaces = NetworkColoredSpaces::new(super_spaces, ctx);

            original = original.minus(&super_spaces);
            minimal = minimal.minus(&super_spaces).union(&minimum_candidate);

            if cfg!(feature = "print-progress") {
                println!(
                    "Minimization in progress: {}[nodes:{}] unprocessed, {}[nodes:{}] candidates.",
                    original.approx_cardinality(),
                    original.symbolic_size(),
                    minimal.approx_cardinality(),
                    minimal.symbolic_size(),
                );
            }
        }

        if cfg!(feature = "print-progress") {
            println!(
                "Found {}[nodes:{}] minimal spaces.",
                minimal.approx_cardinality(),
                minimal.symbolic_size(),
            );
        }

        minimal
    }
}

#[cfg(test)]
mod tests {
    use crate::biodivine_std::traits::Set;
    use crate::symbolic_async_graph::SymbolicAsyncGraph;
    use crate::trap_spaces::{SymbolicSpaceContext, TrapSpaces};
    use crate::BooleanNetwork;

    #[test]
    fn test_trap_spaces() {
        let network = BooleanNetwork::try_from_file("./aeon_models/005.aeon").unwrap();
        let ctx = SymbolicSpaceContext::new(&network);
        let stg = SymbolicAsyncGraph::with_space_context(network.clone(), &ctx).unwrap();
        let unit = ctx.mk_unit_colored_spaces(&stg);

        let essential_traps = TrapSpaces::essential_symbolic(&network, &ctx, &unit);
        let minimal_traps = TrapSpaces::minimal_symbolic(&network, &ctx, &unit);

        assert!(minimal_traps.is_subset(&essential_traps));
        assert_eq!(7.0, essential_traps.approx_cardinality());
        assert_eq!(1.0, minimal_traps.approx_cardinality());

        assert!(minimal_traps.is_singleton());
        assert!(!essential_traps.is_singleton());
    }
}
