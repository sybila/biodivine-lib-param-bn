use crate::symbolic_async_graph::{GraphColoredVertices, SymbolicAsyncGraph};
use crate::VariableId;
use biodivine_lib_bdd::Bdd;

/// Basic symbolic graph operators.
impl SymbolicAsyncGraph {
    /// Compute the colored vertex set which is a result of applying the update function
    /// of the given `variable` to the `initial` set.
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
    pub fn var_pre(
        &self,
        variable: VariableId,
        initial: &GraphColoredVertices,
    ) -> GraphColoredVertices {
        // flip(set) & can_apply_function
        let output = Bdd::fused_binary_flip_op(
            (
                &initial.bdd,
                Some(self.symbolic_context.state_variables[variable.0]),
            ),
            (&self.update_functions[variable.0], None),
            None,
            biodivine_lib_bdd::op_function::and,
        );
        GraphColoredVertices::new(output, &self.symbolic_context)
    }

    /// Compute the subset of `set` that can perform `pre` using given `variable`.
    pub fn var_can_pre(
        &self,
        variable: VariableId,
        set: &GraphColoredVertices,
    ) -> GraphColoredVertices {
        // flip(flip(set) & can_apply_function)
        let output = Bdd::fused_binary_flip_op(
            (
                &set.bdd,
                Some(self.symbolic_context.state_variables[variable.0]),
            ),
            (&self.update_functions[variable.0], None),
            Some(self.symbolic_context.state_variables[variable.0]),
            biodivine_lib_bdd::op_function::and,
        );
        GraphColoredVertices::new(output, &self.symbolic_context)
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

    /// Compute the subset of `set` that can perform *some `pre` operation.
    pub fn can_pre(&self, set: &GraphColoredVertices) -> GraphColoredVertices {
        self.network
            .variables()
            .fold(self.mk_empty_vertices(), |r, v| {
                r.union(&self.var_can_pre(v, set))
            })
    }
}
