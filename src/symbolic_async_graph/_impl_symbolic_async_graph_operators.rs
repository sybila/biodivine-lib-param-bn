use crate::biodivine_std::traits::Set;
use crate::symbolic_async_graph::{GraphColoredVertices, SymbolicAsyncGraph};
use crate::VariableId;
use biodivine_lib_bdd::Bdd;

/// Basic symbolic graph operators.
impl SymbolicAsyncGraph {
    /// Compute the colored vertex set which is a result of applying the update function
    /// of the given `variable` to the `initial` set.
    ///
    /// Uses a single symbolic operation.
    pub fn var_post(
        &self,
        variable: VariableId,
        initial: &GraphColoredVertices,
    ) -> GraphColoredVertices {
        // flip(initial & can_apply_function)
        let output = Bdd::fused_binary_flip_op(
            (&initial.bdd, None),
            (&self.update_functions[variable.0], None),
            Some(self.symbolic_context.state_variables[variable.0]),
            biodivine_lib_bdd::op_function::and,
        );
        GraphColoredVertices::new(output, &self.symbolic_context)
    }

    /// Compute the subset of `set` that can perform `post` using given `variable`.
    ///
    /// Uses a single symbolic operation.
    pub fn var_can_post(
        &self,
        variable: VariableId,
        set: &GraphColoredVertices,
    ) -> GraphColoredVertices {
        // set & can_apply_function
        GraphColoredVertices::new(
            set.bdd.and(&self.update_functions[variable.0]),
            &self.symbolic_context,
        )
    }

    /// Compute the colored vertex set which can create some valuation in `initial` by
    /// applying the update function of the given `variable`.
    ///
    /// Uses a single symbolic operation.
    pub fn var_pre(
        &self,
        variable: VariableId,
        initial: &GraphColoredVertices,
    ) -> GraphColoredVertices {
        // flip(set) & can_apply_function
        let symbolic_var = self.symbolic_context.state_variables[variable.0];
        let output = Bdd::fused_binary_flip_op(
            (&initial.bdd, Some(symbolic_var)),
            (&self.update_functions[variable.0], None),
            None,
            biodivine_lib_bdd::op_function::and,
        );
        GraphColoredVertices::new(output, &self.symbolic_context)
    }

    pub fn var_pre_out(
        &self,
        variable: VariableId,
        initial: &GraphColoredVertices,
    ) -> GraphColoredVertices {
        let symbolic_var = self.symbolic_context.state_variables[variable.0];
        let output = Bdd::fused_ternary_op(
            (&initial.bdd, Some(symbolic_var)),
            (&self.update_functions[variable.0], None),
            (&initial.bdd, None),
            None,
            |a, b, c| {
                // a & b & !c
                match (a, b, c) {
                    (Some(false), _, _) => Some(false),
                    (_, Some(false), _) => Some(false),
                    (_, _, Some(true)) => Some(false),
                    (Some(true), Some(true), Some(false)) => Some(true),
                    _ => None,
                }
            },
        );
        GraphColoredVertices::new(output, &self.symbolic_context)
    }

    /// Compute the subset of `set` that can perform `pre` using given `variable`.
    ///
    /// Uses a single symbolic operation.
    pub fn var_can_pre(
        &self,
        variable: VariableId,
        set: &GraphColoredVertices,
    ) -> GraphColoredVertices {
        // flip(flip(set) & can_apply_function)
        let symbolic_var = self.symbolic_context.state_variables[variable.0];
        let output = Bdd::fused_binary_flip_op(
            (&set.bdd, Some(symbolic_var)),
            (&self.update_functions[variable.0], None),
            Some(symbolic_var),
            biodivine_lib_bdd::op_function::and,
        );
        GraphColoredVertices::new(output, &self.symbolic_context)
    }

    /// Compute the subset of `set` that can perform `post` using the given `variable`,
    /// such that the successor is also within `set`.
    ///
    /// Uses two symbolic operations.
    pub fn var_can_post_within(
        &self,
        variable: VariableId,
        set: &GraphColoredVertices,
    ) -> GraphColoredVertices {
        let symbolic_var = self.symbolic_context.state_variables[variable.0];
        let has_dual_within_set = Bdd::fused_binary_flip_op(
            (&set.bdd, None),
            (&set.bdd, Some(symbolic_var)),
            None,
            biodivine_lib_bdd::op_function::and,
        );
        GraphColoredVertices::new(
            has_dual_within_set.and(&self.update_functions[variable.0]),
            &self.symbolic_context,
        )
    }

    /// Compute the subset of `set` that can perform `post` using the given `variable`,
    /// such that the successor is *not* within `set`.
    ///
    /// Uses two symbolic operations.
    pub fn var_can_post_out(
        &self,
        variable: VariableId,
        set: &GraphColoredVertices,
    ) -> GraphColoredVertices {
        let symbolic_var = self.symbolic_context.state_variables[variable.0];
        // s in output if s in set, but s not in set with var flipped
        let has_no_dual_within_set = Bdd::fused_binary_flip_op(
            (&set.bdd, None),
            (&set.bdd, Some(symbolic_var)),
            None,
            biodivine_lib_bdd::op_function::and_not,
        );
        GraphColoredVertices::new(
            has_no_dual_within_set.and(&self.update_functions[variable.0]),
            &self.symbolic_context,
        )
    }

    /// Compute the subset of `set` that can perform `pre` using the given `variable`,
    /// such that the predecessor is also within `set`.
    ///
    /// Uses two symbolic operations.
    pub fn var_can_pre_within(
        &self,
        variable: VariableId,
        set: &GraphColoredVertices,
    ) -> GraphColoredVertices {
        let symbolic_var = self.symbolic_context.state_variables[variable.0];
        let has_dual_within_set = Bdd::fused_binary_flip_op(
            (&set.bdd, None),
            (&set.bdd, Some(symbolic_var)),
            None,
            biodivine_lib_bdd::op_function::and,
        );
        let can_pre = Bdd::fused_binary_flip_op(
            (&has_dual_within_set, Some(symbolic_var)),
            (&self.update_functions[variable.0], None),
            Some(symbolic_var),
            biodivine_lib_bdd::op_function::and,
        );
        GraphColoredVertices::new(can_pre, &self.symbolic_context)
    }

    /// Compute the subset of `set` that can perform `pre` using the given `variable`,
    /// such that the successor is *not* within `set`.
    ///
    /// Uses two symbolic operations.
    pub fn var_can_pre_out(
        &self,
        variable: VariableId,
        set: &GraphColoredVertices,
    ) -> GraphColoredVertices {
        let symbolic_var = self.symbolic_context.state_variables[variable.0];
        // s in output if s in set, but s not in set with var flipped
        let has_no_dual_within_set = Bdd::fused_binary_flip_op(
            (&set.bdd, None),
            (&set.bdd, Some(symbolic_var)),
            None,
            biodivine_lib_bdd::op_function::and_not,
        );
        let can_pre = Bdd::fused_binary_flip_op(
            (&has_no_dual_within_set, Some(symbolic_var)),
            (&self.update_functions[variable.0], None),
            Some(symbolic_var),
            biodivine_lib_bdd::op_function::and,
        );
        GraphColoredVertices::new(can_pre, &self.symbolic_context)
    }
}

/// Derived operators.
impl SymbolicAsyncGraph {
    /// Compute the result of applying `post` with *all* update functions to the `initial` set.
    pub fn post(&self, initial: &GraphColoredVertices) -> GraphColoredVertices {
        self.network
            .variables()
            .fold(self.mk_empty_vertices(), |r, v| {
                r.union(&self.var_post(v, initial))
            })
    }

    /// Compute the result of applying `pre` with *all* update functions to the `initial` set.
    pub fn pre(&self, initial: &GraphColoredVertices) -> GraphColoredVertices {
        self.network
            .variables()
            .fold(self.mk_empty_vertices(), |r, v| {
                r.union(&self.var_pre(v, initial))
            })
    }

    /// Compute the subset of `set` that can perform *some* `post` operation.
    pub fn can_post(&self, set: &GraphColoredVertices) -> GraphColoredVertices {
        self.network
            .variables()
            .fold(self.mk_empty_vertices(), |r, v| {
                r.union(&self.var_can_post(v, set))
            })
    }

    /// Compute the subset of `set` that can perform *some* `pre` operation.
    pub fn can_pre(&self, set: &GraphColoredVertices) -> GraphColoredVertices {
        self.network
            .variables()
            .fold(self.mk_empty_vertices(), |r, v| {
                r.union(&self.var_can_pre(v, set))
            })
    }

    /// Compute the subset of `set` that can perform *some* `post` operation which leads
    /// to a state within `set`.
    pub fn can_post_within(&self, set: &GraphColoredVertices) -> GraphColoredVertices {
        self.network
            .variables()
            .fold(self.mk_empty_vertices(), |r, v| {
                r.union(&self.var_can_post_within(v, set))
            })
    }

    /// Compute the subset of `set` such that *every admissible* `post` operation leads to a state
    /// within the same `set`.
    ///
    /// Note that this also includes states which cannot perform any `post` operation.
    pub fn will_post_within(&self, set: &GraphColoredVertices) -> GraphColoredVertices {
        self.network
            .variables()
            .fold(set.clone(), |r, v| r.minus(&self.var_can_post_out(v, set)))
    }

    /// Compute the subset of `set` that can perform *some* `pre` operation which leads
    /// to a state within `set`.
    pub fn can_pre_within(&self, set: &GraphColoredVertices) -> GraphColoredVertices {
        self.network
            .variables()
            .fold(self.mk_empty_vertices(), |r, v| {
                r.union(&self.var_can_pre_within(v, set))
            })
    }

    /// Compute the subset of `set` such that *every admissible* `pre` operation leads to a state
    /// within the same `set`.
    ///
    /// Note that this also includes states which cannot perform any `pre` operation.
    pub fn will_pre_within(&self, set: &GraphColoredVertices) -> GraphColoredVertices {
        self.network
            .variables()
            .fold(set.clone(), |r, v| r.minus(&self.var_can_pre_out(v, set)))
    }

    /// Compute the subset of `set` that can perform *some* `post` operation which leads
    /// to a state outside of `set`.
    pub fn can_post_out(&self, set: &GraphColoredVertices) -> GraphColoredVertices {
        self.network
            .variables()
            .fold(self.mk_empty_vertices(), |r, v| {
                r.union(&self.var_can_post_out(v, set))
            })
    }

    /// Compute the subset of `set` such that *every admissible* `post` operation leads
    /// to a state outside the `set`.
    ///
    /// Note that this also includes states which cannot perform any `post` operation.
    pub fn will_post_out(&self, set: &GraphColoredVertices) -> GraphColoredVertices {
        self.network.variables().fold(set.clone(), |r, v| {
            r.minus(&self.var_can_post_within(v, set))
        })
    }

    /// Compute the subset of `set` that can perform *some* `pre` operation which leads
    /// to a state outside of `set`.
    pub fn can_pre_out(&self, set: &GraphColoredVertices) -> GraphColoredVertices {
        self.network
            .variables()
            .fold(self.mk_empty_vertices(), |r, v| {
                r.union(&self.var_can_pre_out(v, set))
            })
    }

    /// Compute the subset of `set` such that *every admissible* `pre` operation leads
    /// to a state outside of `set`.
    ///
    /// Note that this also includes states which cannot perform any `pre` operation.
    pub fn will_pre_out(&self, set: &GraphColoredVertices) -> GraphColoredVertices {
        self.network.variables().fold(set.clone(), |r, v| {
            r.minus(&self.var_can_pre_within(v, set))
        })
    }
}

#[cfg(test)]
mod tests {

    /* Basically a copy from of example from tutorial, but tutorials don't count towards coverage. */
    use crate::symbolic_async_graph::SymbolicAsyncGraph;
    use crate::BooleanNetwork;
    use std::convert::TryFrom;

    #[test]
    fn basic_graph_test() {
        let bn = BooleanNetwork::try_from(
            r"
            A -> B
            C -|? B
            $B: A
            C -> A
            B -> A
            A -| A
            $A: C | f(A, B)
        ",
        )
        .unwrap();
        let stg = SymbolicAsyncGraph::new(bn).unwrap();
        let id_b = stg.as_network().as_graph().find_variable("B").unwrap();
        let b_is_true = stg.fix_network_variable(id_b, true);
        let b_is_false = stg.fix_network_variable(id_b, false);

        assert_eq!(
            stg.var_can_pre(id_b, &b_is_true),
            stg.var_post(id_b, &b_is_false)
        );
        assert_eq!(
            stg.var_can_post(id_b, &b_is_false),
            stg.var_pre(id_b, &b_is_true)
        );
        assert_eq!(4.0, stg.can_pre(&b_is_true).vertices().approx_cardinality());
        assert_eq!(
            4.0,
            stg.can_post(&b_is_false).vertices().approx_cardinality()
        );

        let some_color = stg.unit_colors().pick_singleton();
        let b_is_true_with_color = b_is_true.intersect_colors(&some_color);
        let b_is_false_with_color = b_is_false.intersect_colors(&some_color);
        assert_eq!(
            3.0,
            stg.can_pre(&b_is_true_with_color)
                .vertices()
                .approx_cardinality()
        );
        assert_eq!(
            4.0,
            stg.can_post(&b_is_false_with_color)
                .vertices()
                .approx_cardinality()
        );

        assert_ne!(stg.can_pre(&b_is_true), stg.post(&b_is_false));
        assert_ne!(stg.can_post(&b_is_false), stg.pre(&b_is_true));
    }
}
