use crate::biodivine_std::traits::Set;
use crate::symbolic_async_graph::reachability::Reachability;
use crate::symbolic_async_graph::{GraphColoredVertices, SymbolicAsyncGraph};
use crate::{ExtendedBoolean, Space, VariableId};

/// Here, we provide several basic symbolic algorithms for exploring the `SymbolicAsyncGraph`.
/// This mainly includes reachability and similar fixed-point properties.
///
/// In some cases, you may want to re-implement these algorithms, since they do not have
/// more advanced features, like logging or cancellation. But for most general use-cases, these
/// should be the best we can do right now in terms of performance.
impl SymbolicAsyncGraph {
    /// Compute the set of forward-reachable vertices from the given `initial` set.
    ///
    /// In other words, the result is the smallest forward-closed superset of `initial`.
    pub fn reach_forward(&self, initial: &GraphColoredVertices) -> GraphColoredVertices {
        Reachability::reach_fwd(self, initial)
    }

    /// Compute the set of backward-reachable vertices from the given `initial` set.
    ///
    /// In other words, the result is the smallest backward-closed superset of `initial`.
    pub fn reach_backward(&self, initial: &GraphColoredVertices) -> GraphColoredVertices {
        Reachability::reach_bwd(self, initial)
    }

    /// Compute the subset of `initial` vertices that can only reach other vertices within
    /// the `initial` set.
    ///
    /// In other words, the result is the largest forward-closed subset of `initial`.
    pub fn trap_forward(&self, initial: &GraphColoredVertices) -> GraphColoredVertices {
        let mut result = initial.clone();
        'fwd: loop {
            for var in self.variables().rev() {
                let step = self.var_can_post_out(var, &result);
                if !step.is_empty() {
                    result = result.minus(&step);
                    continue 'fwd;
                }
            }

            return result;
        }
    }

    /// Compute the subset of `initial` vertices that can only be reached from vertices within
    /// the `initial` set.
    ///
    /// In other words, the result is the largest backward-closed subset of `initial`.
    pub fn trap_backward(&self, initial: &GraphColoredVertices) -> GraphColoredVertices {
        let mut result = initial.clone();
        'bwd: loop {
            for var in self.variables().rev() {
                let step = self.var_can_pre_out(var, &result);
                if !step.is_empty() {
                    result = result.minus(&step);
                    continue 'bwd;
                }
            }

            return result;
        }
    }

    /// Returns `true` if the update function of [VariableId] can evaluate to `false` in the given space.
    pub fn space_has_var_false(&self, var: VariableId, space: &Space) -> bool {
        let space = space.to_symbolic_values(self.symbolic_context());
        !self.get_symbolic_fn_update(var).restrict(&space).is_true()
    }

    /// Returns `true` if the update function of [VariableId] can evaluate to `true` in the given space.
    pub fn space_has_var_true(&self, var: VariableId, space: &Space) -> bool {
        let space = space.to_symbolic_values(self.symbolic_context());
        !self.get_symbolic_fn_update(var).restrict(&space).is_false()
    }

    /// Compute a percolation of the given space.
    ///
    /// The method has two modes: If `fix_subspace` is set to `true`, the method will only try to update
    /// variables that are not fixed yet. If `fix_subspace` is `false`, the method can also update variables
    /// that are fixed in the original space.
    ///
    /// If the input is a trap space, these two modes should give the same result.
    pub fn percolate_space(&self, space: &Space, fix_subspace: bool) -> Space {
        let mut result = space.clone();
        'percolate: loop {
            let symbolic_space = result.to_symbolic_values(self.symbolic_context());
            for var in self.variables().rev() {
                if fix_subspace && space[var].is_fixed() {
                    // In fixed mode, we do not propagate values that are fixed in the original space.
                    continue;
                }

                let update = self.get_symbolic_fn_update(var);
                let restricted = update.restrict(&symbolic_space);
                let new_value = if restricted.is_true() {
                    ExtendedBoolean::One
                } else if restricted.is_false() {
                    ExtendedBoolean::Zero
                } else {
                    ExtendedBoolean::Any
                };

                if result[var] != new_value {
                    // If we can update result, we do it and restart the percolation process.
                    result[var] = new_value;
                    continue 'percolate;
                }
            }
            // If nothing changed, we are done.
            break;
        }

        result
    }
}

#[cfg(test)]
mod tests {
    use crate::biodivine_std::traits::Set;
    use crate::symbolic_async_graph::SymbolicAsyncGraph;
    use crate::ExtendedBoolean::Zero;
    use crate::{BooleanNetwork, ExtendedBoolean, Space};
    use ExtendedBoolean::One;

    #[test]
    pub fn basic_algorithms_test() {
        // Right now, there isn't really a strategy on how this should be tested, so for now
        // we only test if we can run through all the code and get reasonable results.
        let bn = BooleanNetwork::try_from(
            r"
            b ->? a
            c ->? a
            a -|? a
            a -> b
            a -> c
            c -| b
        ",
        )
        .unwrap();

        let stg = SymbolicAsyncGraph::new(&bn).unwrap();

        let pivot = stg.unit_colored_vertices().pick_vertex();
        let fwd = stg.reach_forward(&pivot);
        let bwd = stg.reach_backward(&pivot);
        let scc = fwd.intersect(&bwd);

        // Should contain all cases where pivot is in an attractor.
        let attractor_basin = stg.trap_forward(&bwd);
        // Should contain all cases where pivot is in a repeller.
        let repeller_basin = stg.trap_backward(&fwd);

        assert!(fwd.approx_cardinality() > pivot.approx_cardinality());
        assert!(bwd.approx_cardinality() > pivot.approx_cardinality());
        assert!(scc.approx_cardinality() > pivot.approx_cardinality());
        assert!(attractor_basin.approx_cardinality() > pivot.approx_cardinality());
        // For some reason, there is only a very small number of parameter valuations
        // where this is not empty -- less than in the pivot in fact.
        assert!(!repeller_basin.is_empty());
    }

    #[test]
    fn basic_percolation_test() {
        let bn = BooleanNetwork::try_from_bnet(
            r"
            targets,factors
            a, a | b
            b, c & a
            c, (a & b) | (a & c)
            ",
        )
        .unwrap();
        let stg = SymbolicAsyncGraph::new(&bn).unwrap();

        let a = bn.as_graph().find_variable("a").unwrap();
        let b = bn.as_graph().find_variable("b").unwrap();
        let c = bn.as_graph().find_variable("c").unwrap();

        let mut a_true = Space::new(&bn);
        a_true[a] = One;

        let mut a_false = Space::new(&bn);
        a_false[a] = Zero;

        let a_true_percolated = stg.percolate_space(&a_true, false);
        assert_eq!(a_true, a_true_percolated);

        let a_false_percolated = stg.percolate_space(&a_false, false);
        let mut expected = Space::new(&bn);
        expected[a] = Zero;
        expected[b] = Zero;
        expected[c] = Zero;
        assert_eq!(expected, a_false_percolated);

        let mut unstable = Space::new(&bn);
        unstable[b] = One;
        let mut expected = Space::new(&bn);
        assert_eq!(expected, stg.percolate_space(&unstable, false));
        expected[b] = One;
        expected[a] = One;
        expected[c] = One;
        assert_eq!(expected, stg.percolate_space(&unstable, true));

        assert!(stg.space_has_var_false(b, &a_true));
        assert!(stg.space_has_var_true(b, &a_true));
        assert!(stg.space_has_var_false(c, &a_true));
        assert!(stg.space_has_var_true(c, &a_true));

        assert!(stg.space_has_var_false(b, &a_false));
        assert!(!stg.space_has_var_true(b, &a_false));
        assert!(stg.space_has_var_false(c, &a_false));
        assert!(!stg.space_has_var_true(c, &a_false));
    }
}
