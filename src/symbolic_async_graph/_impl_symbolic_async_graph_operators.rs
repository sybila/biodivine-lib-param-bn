use crate::biodivine_std::traits::Set;
use crate::symbolic_async_graph::{GraphColoredVertices, SymbolicAsyncGraph};
use crate::VariableId;
use biodivine_lib_bdd::Bdd;

/// Basic symbolic graph operators. For convenience, there is a wide variety of different
/// operators fulfilling different needs. Here, all operators only analyse transitions with
/// respect to a single network variable and every operation implemented using one symbolic
/// operation.
///
/// The general recommendation is to use `var_post` / `var_pre` for most tasks
/// (implementing additional logic using extra symbolic operations), and once the algorithm is
/// tested and stable, replace these functions with the more efficient "fused" operations.
///
/// We provide the following variable-specific operations:
///  - `var_post` / `var_pre`: General successors or predecessors.
///  - `var_post_out` / `var_pre_out`: Successors or predecessors, but only *outside* of the
///     given initial set.
///  - `var_post_within` / `var_pre_within`: Successors or predecessors, but only *inside* the
///     given initial set.
///  - `var_can_post` / `var_can_pre`: Subset of the initial set that has some
///     successors / predecessors.
///  - `var_can_post_out` / `var_can_pre_out`: Subset of the initial set that can perform
///     a transition leading *outside* of the initial set.
///  - `var_can_post_within` / `var_can_pre_within`: Subset of the initial set that can perform
///     a transition leading *into* the initial set.
///
/// Note that the output of some of these functions is technically equivalent (e.g.
/// `var_post_within` and `var_can_pre_within`) but we nevertheless provided all for completeness.
///
impl SymbolicAsyncGraph {
    /// Compute the `GraphColoredVertices` representing the successors of the vertices in the
    /// given `initial` set that are reached by updating the given `variable`. Formally:
    ///
    /// $$
    ///    \texttt{VarPost}(v, X) = \\{~(y, c) \mid \exists x.~(x, c) \in X \land x \xrightarrow{v}_c y~\\}
    /// $$
    pub fn var_post(
        &self,
        variable: VariableId,
        initial: &GraphColoredVertices,
    ) -> GraphColoredVertices {
        // flip(initial & can_apply_function)
        let symbolic_var = self.symbolic_context.state_variables[variable.0];
        let output = Bdd::fused_binary_flip_op(
            (&initial.bdd, None),
            (&self.update_functions[variable.0], None),
            Some(symbolic_var),
            biodivine_lib_bdd::op_function::and,
        );
        GraphColoredVertices::new(output, &self.symbolic_context)
    }

    /// Compute the `GraphColoredVertices` representing the predecessors of the vertices in the
    /// given `initial` set that are reached by updating the given `variable`. Formally:
    ///
    /// $$
    ///    \texttt{VarPre}(v, X) = \\{~(x, c) \mid \exists y.~(y, c) \in X \land x \xrightarrow{v}_{c} y~\\}
    /// $$
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

    /// Compute the `GraphColoredVertices` representing the successors of the vertices in the
    /// given `initial` set that are reached by updating the given `variable`, but are *not* in
    /// the `initial` set. Formally:
    ///
    /// $$
    ///    \texttt{VarPostOut}(v, X) = \\{~(y, c) \mid (y, c) \notin X \land \exists x.~(x, c) \in X \land x \xrightarrow{v}_{c} y~\\}
    /// $$
    pub fn var_post_out(
        &self,
        variable: VariableId,
        initial: &GraphColoredVertices,
    ) -> GraphColoredVertices {
        // flip(set & !flip(set) & can_apply_function)
        let symbolic_var = self.symbolic_context.state_variables[variable.0];
        let output = Bdd::fused_ternary_flip_op(
            (&initial.bdd, None),
            (&initial.bdd, Some(symbolic_var)),
            (&self.update_functions[variable.0], None),
            Some(symbolic_var),
            |a, b, c| {
                // a & !b & c
                match (a, b, c) {
                    (Some(false), _, _) => Some(false),
                    (_, Some(true), _) => Some(false),
                    (_, _, Some(false)) => Some(false),
                    (Some(true), Some(false), Some(true)) => Some(true),
                    _ => None,
                }
            },
        );
        GraphColoredVertices::new(output, &self.symbolic_context)
    }

    /// Compute the `GraphColoredVertices` representing the predecessors of the vertices in the
    /// given `initial` set that are reached by updating the given `variable`, but are *not* in
    /// the initial set. Formally:
    ///
    /// $$
    ///    \texttt{VarPreOut}(v, X) = \\{~(x, c) \mid (x, c) \notin X \land \exists y.~(y, c) \in X \land x \xrightarrow{v}_{c} y~\\}
    /// $$
    pub fn var_pre_out(
        &self,
        variable: VariableId,
        initial: &GraphColoredVertices,
    ) -> GraphColoredVertices {
        // !set & flip(set) & can_apply_function
        let symbolic_var = self.symbolic_context.state_variables[variable.0];
        let output = Bdd::fused_ternary_flip_op(
            (&initial.bdd, None),
            (&initial.bdd, Some(symbolic_var)),
            (&self.update_functions[variable.0], None),
            None,
            |a, b, c| {
                // !a & b & c
                match (a, b, c) {
                    (Some(true), _, _) => Some(false),
                    (_, Some(false), _) => Some(false),
                    (_, _, Some(false)) => Some(false),
                    (Some(false), Some(true), Some(true)) => Some(true),
                    _ => None,
                }
            },
        );
        GraphColoredVertices::new(output, &self.symbolic_context)
    }

    /// Compute the `GraphColoredVertices` representing the successors of the vertices in the
    /// given `initial` set that are reached by updating the given `variable`, but are *within*
    /// the `initial` set. Formally:
    ///
    /// $$
    ///    \texttt{VarPostWithin}(v, X) = \\{~(y, c) \mid (y, c) \in X \land \exists x.~(x, c) \in X \land x \xrightarrow{v}_{c} y~\\}
    /// $$
    pub fn var_post_within(
        &self,
        variable: VariableId,
        initial: &GraphColoredVertices,
    ) -> GraphColoredVertices {
        // flip(set & flip(set) & can_apply_function)
        let symbolic_var = self.symbolic_context.state_variables[variable.0];
        let output = Bdd::fused_ternary_flip_op(
            (&initial.bdd, None),
            (&initial.bdd, Some(symbolic_var)),
            (&self.update_functions[variable.0], None),
            Some(symbolic_var),
            |a, b, c| {
                // a & b & c
                match (a, b, c) {
                    (Some(false), _, _) => Some(false),
                    (_, Some(false), _) => Some(false),
                    (_, _, Some(false)) => Some(false),
                    (Some(true), Some(true), Some(true)) => Some(true),
                    _ => None,
                }
            },
        );
        GraphColoredVertices::new(output, &self.symbolic_context)
    }

    /// Compute the `GraphColoredVertices` representing the predecessors of the vertices in the
    /// given `initial` set that are reached by updating the given `variable`, but are *within*
    /// the initial set. Formally:
    ///
    /// $$
    ///    \texttt{VarPreWithin}(v, X) = \\{~(x, c) \mid (x, c) \in X \land \exists y.~(y, c) \in X \land x \xrightarrow{v}_{c} y~\\}
    /// $$
    pub fn var_pre_within(
        &self,
        variable: VariableId,
        initial: &GraphColoredVertices,
    ) -> GraphColoredVertices {
        // set & flip(set) & can_apply_function
        let symbolic_var = self.symbolic_context.state_variables[variable.0];
        let output = Bdd::fused_ternary_flip_op(
            (&initial.bdd, None),
            (&initial.bdd, Some(symbolic_var)),
            (&self.update_functions[variable.0], None),
            None,
            |a, b, c| {
                // a & b & c
                match (a, b, c) {
                    (Some(false), _, _) => Some(false),
                    (_, Some(false), _) => Some(false),
                    (_, _, Some(false)) => Some(false),
                    (Some(true), Some(true), Some(true)) => Some(true),
                    _ => None,
                }
            },
        );
        GraphColoredVertices::new(output, &self.symbolic_context)
    }

    /// Compute the `GraphColoredVertices` representing the subset of the `initial` set for which
    /// there exists an outgoing transition using the given `variable`. Formally:
    ///
    /// $$
    ///     \texttt{VarCanPost}(v, X) = \\{~ (x, c) \in X \mid \exists y.~ x \xrightarrow{v}_{c} y ~\\}
    /// $$
    pub fn var_can_post(
        &self,
        variable: VariableId,
        initial: &GraphColoredVertices,
    ) -> GraphColoredVertices {
        // set & can_apply_function
        GraphColoredVertices::new(
            initial.bdd.and(&self.update_functions[variable.0]),
            &self.symbolic_context,
        )
    }

    /// Compute the `GraphColoredVertices` representing the subset of the `initial` set for which
    /// there exists an incoming transition using the given `variable`. Formally:
    ///
    /// $$
    ///     \texttt{VarCanPre}(v, X) = \\{~ (y, c) \in X \mid \exists x.~ x \xrightarrow{v}_{c} y ~\\}
    /// $$
    pub fn var_can_pre(
        &self,
        variable: VariableId,
        initial: &GraphColoredVertices,
    ) -> GraphColoredVertices {
        // flip(flip(set) & can_apply_function)
        let symbolic_var = self.symbolic_context.state_variables[variable.0];
        let output = Bdd::fused_binary_flip_op(
            (&initial.bdd, Some(symbolic_var)),
            (&self.update_functions[variable.0], None),
            Some(symbolic_var),
            biodivine_lib_bdd::op_function::and,
        );
        GraphColoredVertices::new(output, &self.symbolic_context)
    }

    /// Compute the `GraphColoredVertices` representing the subset of the `initial` set for which
    /// there exists an outgoing transition using the given `variable` that leads *outside* of the
    /// `initial` set. Formally:
    ///
    /// $$
    ///     \texttt{VarCanPostOut}(v, X) = \\{~ (x, c) \in X \mid \exists y.~(y, c) \notin X \land x \xrightarrow{v}_{c} y ~\\}
    /// $$
    pub fn var_can_post_out(
        &self,
        variable: VariableId,
        initial: &GraphColoredVertices,
    ) -> GraphColoredVertices {
        // set & !flip(set) & can_apply_function
        let symbolic_var = self.symbolic_context.state_variables[variable.0];
        let output = Bdd::fused_ternary_flip_op(
            (&initial.bdd, None),
            (&initial.bdd, Some(symbolic_var)),
            (&self.update_functions[variable.0], None),
            None,
            |a, b, c| {
                // a & !b & c
                match (a, b, c) {
                    (Some(false), _, _) => Some(false),
                    (_, Some(true), _) => Some(false),
                    (_, _, Some(false)) => Some(false),
                    (Some(true), Some(false), Some(true)) => Some(true),
                    _ => None,
                }
            },
        );
        GraphColoredVertices::new(output, &self.symbolic_context)
    }

    /// Compute the `GraphColoredVertices` representing the subset of the `initial` set for which
    /// there exists an incoming transition using the given `variable` that originates *outside* of the
    /// `initial` set. Formally:
    ///
    /// $$
    ///     \texttt{VarCanPreOut}(v, X) = \\{~ (y, c) \in X \mid \exists x.~(x, c) \notin X \land x \xrightarrow{v}_{c} y ~\\}
    /// $$
    pub fn var_can_pre_out(
        &self,
        variable: VariableId,
        initial: &GraphColoredVertices,
    ) -> GraphColoredVertices {
        // !set & flip(set) & can_apply_function
        let symbolic_var = self.symbolic_context.state_variables[variable.0];
        let output = Bdd::fused_ternary_flip_op(
            (&initial.bdd, None),
            (&initial.bdd, Some(symbolic_var)),
            (&self.update_functions[variable.0], None),
            None,
            |a, b, c| {
                // !a & b & c
                match (a, b, c) {
                    (Some(true), _, _) => Some(false),
                    (_, Some(false), _) => Some(false),
                    (_, _, Some(false)) => Some(false),
                    (Some(false), Some(true), Some(true)) => Some(true),
                    _ => None,
                }
            },
        );
        GraphColoredVertices::new(output, &self.symbolic_context)
    }

    /// Compute the `GraphColoredVertices` representing the subset of the `initial` set for which
    /// there exists an outgoing transition using the given `variable` that leads *into* the
    /// `initial` set. Formally:
    ///
    /// $$
    ///     \texttt{VarCanPostWithin}(v, X) = \\{~ (x, c) \in X \mid \exists y.~(y, c) \in X \land x \xrightarrow{v}_{c} y ~\\}
    /// $$
    pub fn var_can_post_within(
        &self,
        variable: VariableId,
        initial: &GraphColoredVertices,
    ) -> GraphColoredVertices {
        // set & flip(set) & can_apply_function
        let symbolic_var = self.symbolic_context.state_variables[variable.0];
        let output = Bdd::fused_ternary_flip_op(
            (&initial.bdd, None),
            (&initial.bdd, Some(symbolic_var)),
            (&self.update_functions[variable.0], None),
            None,
            |a, b, c| {
                // a & b & c
                match (a, b, c) {
                    (Some(false), _, _) => Some(false),
                    (_, Some(false), _) => Some(false),
                    (_, _, Some(false)) => Some(false),
                    (Some(true), Some(true), Some(true)) => Some(true),
                    _ => None,
                }
            },
        );
        GraphColoredVertices::new(output, &self.symbolic_context)
    }

    /// Compute the `GraphColoredVertices` representing the subset of the `initial` set for which
    /// there exists an incoming transition using the given `variable` that originates *inside* the
    /// `initial` set. Formally:
    ///
    /// $$
    ///     \texttt{VarCanPreWithin}(v, X) = \\{~ (y, c) \in X \mid \exists x.~(x, c) \in X \land x \xrightarrow{v}_{c} y ~\\}
    /// $$
    pub fn var_can_pre_within(
        &self,
        variable: VariableId,
        initial: &GraphColoredVertices,
    ) -> GraphColoredVertices {
        // flip(set & flip(set) & can_post_function)
        let symbolic_var = self.symbolic_context.state_variables[variable.0];
        let output = Bdd::fused_ternary_flip_op(
            (&initial.bdd, None),
            (&initial.bdd, Some(symbolic_var)),
            (&self.update_functions[variable.0], None),
            Some(symbolic_var),
            |a, b, c| {
                // a & b & c
                match (a, b, c) {
                    (Some(false), _, _) => Some(false),
                    (_, Some(false), _) => Some(false),
                    (_, _, Some(false)) => Some(false),
                    (Some(true), Some(true), Some(true)) => Some(true),
                    _ => None,
                }
            },
        );
        GraphColoredVertices::new(output, &self.symbolic_context)
    }
}

/// Here, we give several operators derived from the variable-specific operators. These have
/// complexity `O(|vars|)` since they are internally represented using the variable-specific
/// operators.
///
/// We provide the following functions:
///  - `post` / `pre`: General successors and predecessors functions.
///  - `can_post` / `can_pre`: Subsets of the initial states that have some successors
///     or predecessors.
///  - `can_post_within` / `can_pre_within`: Subsets of initial states that have some successors
///     / predecessors within the initial set.
///  - `will_post_within` / `will_pre_within`: Subsets of initial states that have all successors
///     / predecessors withing the initial set.
///  - `can_post_out` / `can_pre_out`: Subsets of initial states that have some successors
///     / predecessors outside of the initial set.
///  - `will_post_out` / `will_pre_out`: Subsets of initial states that have all successors
///     / predecessors outside of the initial set.
///
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
