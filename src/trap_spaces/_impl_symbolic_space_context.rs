use crate::symbolic_async_graph::{SymbolicAsyncGraph, SymbolicContext};
use crate::trap_spaces::{NetworkColoredSpaces, NetworkSpaces, SymbolicSpaceContext};
use crate::{
    global_log_level, log_essential, never_stop, BooleanNetwork, ExtendedBoolean, Space, VariableId,
};
use biodivine_lib_bdd::{bdd, Bdd, BddPartialValuation, BddVariable, BddVariableSet};
use std::collections::HashMap;

impl SymbolicSpaceContext {
    /// Create a new [SymbolicSpaceContext] valid for the given [BooleanNetwork].
    pub fn new(network: &BooleanNetwork) -> SymbolicSpaceContext {
        let map = network
            .variables()
            .map(|it| (it, 2))
            .collect::<HashMap<_, _>>();
        let inner_ctx = SymbolicContext::with_extra_state_variables(network, &map).unwrap();
        let positive_variables = inner_ctx.extra_state_variables_by_offset(0);
        let negative_variables = inner_ctx.extra_state_variables_by_offset(1);
        let dual_variables = positive_variables
            .into_iter()
            .zip(negative_variables)
            .map(|((_v1, var_t), (_v2, var_f))| (var_t, var_f))
            .collect::<Vec<_>>();

        let bdd_vars = inner_ctx.bdd_variable_set();

        let mut s_to_v_bdd = inner_ctx.mk_constant(true);
        let mut v_to_s_bdd = inner_ctx.mk_constant(true);
        for var in inner_ctx.network_variables() {
            let (p_var, n_var) = dual_variables[var.to_index()];
            let s_var = inner_ctx.get_state_variable(var);

            s_to_v_bdd = bdd!(bdd_vars, s_to_v_bdd & ((p_var & (!n_var)) => s_var));
            s_to_v_bdd = bdd!(bdd_vars, s_to_v_bdd & (((!p_var) & n_var) => (!s_var)));

            v_to_s_bdd = bdd!(bdd_vars, v_to_s_bdd & (s_var => (p_var & (!n_var))));
            v_to_s_bdd = bdd!(bdd_vars, v_to_s_bdd & ((!s_var) => ((!p_var) & n_var)));
            v_to_s_bdd = bdd!(bdd_vars, v_to_s_bdd & (p_var | n_var)); // Enforce correct encoding.
        }

        SymbolicSpaceContext {
            inner_ctx,
            dual_variables,
            space_to_vertex_bdd: s_to_v_bdd,
            vertex_to_space_bdd: v_to_s_bdd,
        }
    }

    /// Access the inner [SymbolicContext].
    pub fn inner_context(&self) -> &SymbolicContext {
        &self.inner_ctx
    }

    /// A reference to the [BddVariableSet] of the inner [SymbolicContext].
    pub fn bdd_variable_set(&self) -> &BddVariableSet {
        self.inner_context().bdd_variable_set()
    }

    /// Get the BDD state variable `x` representing the network variable `var`.
    pub fn get_state_variable(&self, var: VariableId) -> BddVariable {
        self.inner_context().get_state_variable(var)
    }

    /// Get the BDD space variable `x_T` for the network variable `var`.
    pub fn get_positive_variable(&self, var: VariableId) -> BddVariable {
        self.dual_variables[var.to_index()].0
    }

    /// Get the BDD space variable `x_F` for the network variable `var`.
    pub fn get_negative_variable(&self, var: VariableId) -> BddVariable {
        self.dual_variables[var.to_index()].1
    }

    /// Get the two BDD variables `(x_T, x_F)` which this [SymbolicSpaceContext] uses to
    /// encode a subspace.
    pub fn get_dual_variable_pair(&self, var: VariableId) -> (BddVariable, BddVariable) {
        self.dual_variables[var.to_index()]
    }

    /// Returns the list of all dual variable pairs `(x_T, x_F)` that are used in the
    /// subspace encoding. These are ordered the same way as "normal" state variables.
    pub fn get_dual_variables(&self) -> Vec<(BddVariable, BddVariable)> {
        self.dual_variables.clone()
    }

    /// Compute the [Bdd] which contains all correctly encoded spaces tracked by this
    /// [SymbolicSpaceContext].
    ///
    /// The [Bdd] only constraints the space variables and it has no impact on the space/parameter
    /// variables.
    pub fn mk_unit_bdd(&self) -> Bdd {
        let bdd_vars = self.bdd_variable_set();
        self.dual_variables
            .iter()
            .cloned()
            .fold(bdd_vars.mk_true(), |acc, (t_var, f_var)| {
                bdd!(bdd_vars, acc & (t_var | f_var))
            })
    }

    /// Compute the symbolic set of all [NetworkSpaces] valid in this [SymbolicSpaceContext].
    pub fn mk_unit_spaces(&self) -> NetworkSpaces {
        NetworkSpaces::new(self.mk_unit_bdd(), self)
    }

    /// Compute an empty symbolic set of network spaces.
    pub fn mk_empty_spaces(&self) -> NetworkSpaces {
        NetworkSpaces::new(self.bdd_variable_set().mk_false(), self)
    }

    /// Compute an empty symbolic set of colored network spaces.
    pub fn mk_empty_colored_spaces(&self) -> NetworkColoredSpaces {
        NetworkColoredSpaces::new(self.bdd_variable_set().mk_false(), self)
    }

    /// Compute a unit set of coloured trap spaces which is valid with respect to a specific
    /// [SymbolicAsyncGraph]. Note that such graph has to be created using
    /// [SymbolicAsyncGraph::with_space_context].
    pub fn mk_unit_colored_spaces(&self, graph: &SymbolicAsyncGraph) -> NetworkColoredSpaces {
        let colors = graph.mk_unit_colors().into_bdd();
        let spaces = self.mk_unit_spaces().into_bdd();
        NetworkColoredSpaces {
            bdd: colors.and(&spaces),
            dual_variables: self.dual_variables.clone(),
            parameter_variables: self.inner_ctx.parameter_variables().clone(),
        }
    }

    /// Compute a [Bdd] which encodes all spaces in which the value of `function` can be
    /// `true` for some state. We assume that `function` can depend on state variables and
    /// parameter variables, but not on the dual variables used for space encoding.
    ///
    /// In other words, a space `S` satisfies the result [Bdd] if and only if there exists
    /// a state `x \in S` such that `function(x) = true`.
    ///
    /// To compute this, we evaluate the following (informal) expression:
    ///     `exists s_1...s_n: [(s_i => s_i_T) & (!s_i => s_i_F)] & function(s_1, ..., s_n)`
    ///
    /// **WARNING:** The resulting BDD also allows invalid space encodings, mostly because
    /// these are to some extent still interesting in some applications.
    ///
    pub fn mk_can_go_to_true(&self, function: &Bdd) -> Bdd {
        self._mk_can_go_to_true(function, global_log_level(), &never_stop)
            .unwrap()
    }

    pub fn _mk_can_go_to_true<E, F: Fn() -> Result<(), E>>(
        &self,
        function: &Bdd,
        log_level: usize,
        interrupt: &F,
    ) -> Result<Bdd, E> {
        let bdd_vars = self.inner_ctx.bdd_variable_set();
        // Only constrain variables that are relevant to `functions`.
        let support_set = {
            let mut s = function.support_set().into_iter().collect::<Vec<_>>();
            s.sort();
            s
        };
        let mut result = function.clone();
        for var in support_set.into_iter().rev() {
            let index = self
                .inner_ctx
                .state_variables()
                .iter()
                .position(|it| *it == var);
            let Some(index) = index else {
                // Skip non-state variables.
                continue;
            };
            let state_var = var;
            let (t_var, f_var) = self.dual_variables[index];
            let is_in_space = bdd!(bdd_vars, (state_var => t_var) & ((!state_var) => f_var));
            result = result.and(&is_in_space).var_exists(state_var);
            interrupt()?;

            if log_essential(log_level, result.size()) {
                println!(
                    "Computing can-go-to-true: {}[nodes:{}].",
                    result.cardinality(),
                    result.size(),
                );
            }
        }
        Ok(result)
    }

    /// Compute a [Bdd] of all spaces that are a super-space of the elements in `spaces`.
    ///
    /// The process should also preserve any "extra" variables, such as colors/parameters.
    /// Also note that this is a simple iterative algorithm that may need `O(n)` iterations
    /// and `O(n)` BDD ops to converge (`n` being the number of network variables).
    ///
    pub fn mk_super_spaces(&self, spaces: &Bdd) -> Bdd {
        self._mk_super_spaces(spaces, global_log_level(), &never_stop)
            .unwrap()
    }

    pub fn _mk_super_spaces<E, F: Fn() -> Result<(), E>>(
        &self,
        spaces: &Bdd,
        log_level: usize,
        interrupt: &F,
    ) -> Result<Bdd, E> {
        let vars = self.bdd_variable_set();
        let mut result = spaces.clone();
        for (t_var, f_var) in self.dual_variables.iter().rev() {
            // Select every space in which we have `t_var=false`, but there is
            // no equivalent space with `t_var=true`. Flips `t_var` on output,
            // meaning we actually get the set of super spaces where `true` is added.
            let t_var_bdd = vars.mk_literal(*t_var, false);
            let adds_true = Bdd::fused_ternary_flip_op(
                (&result, None),
                (&t_var_bdd, None),
                (&result, Some(*t_var)),
                Some(*t_var),
                and_and_not,
            );
            interrupt()?;

            // Symmetrically for `t_false`.
            let f_var_bdd = vars.mk_literal(*f_var, false);
            let adds_false = Bdd::fused_ternary_flip_op(
                (&result, None),
                (&f_var_bdd, None),
                (&result, Some(*f_var)),
                Some(*f_var),
                and_and_not,
            );
            interrupt()?;

            if !adds_true.is_false() || !adds_false.is_false() {
                result = bdd!(vars, result | (adds_true | adds_false));
                interrupt()?;
                if log_essential(log_level, result.size()) {
                    println!(
                        "Computing super-spaces: {}[nodes:{}].",
                        result.cardinality(),
                        result.size(),
                    );
                }
            }
        }
        Ok(result)
    }

    /// Compute a [Bdd] of all spaces that are a subspace of the elements in `spaces`.
    ///
    /// The same notes as for [SymbolicSpaceContext::mk_super_spaces] apply.
    pub fn mk_sub_spaces(&self, spaces: &Bdd) -> Bdd {
        self._mk_sub_spaces(spaces, global_log_level(), &never_stop)
            .unwrap()
    }

    pub fn _mk_sub_spaces<E, F: Fn() -> Result<(), E>>(
        &self,
        spaces: &Bdd,
        log_level: usize,
        interrupt: &F,
    ) -> Result<Bdd, E> {
        let vars = self.bdd_variable_set();
        let mut result = spaces.clone();
        for (t_var, f_var) in self.dual_variables.clone().into_iter().rev() {
            // A value can go down only in subspaces where both variables are set.
            // If only one variable is set, going down will just break the encoding.
            let can_go_down = bdd!(vars, t_var & f_var);
            // Has `t_var=true`, but the flipped valuation is not present. We return
            // the flipped valuation.
            let removes_true = Bdd::fused_ternary_flip_op(
                (&result, None),
                (&can_go_down, None),
                (&result, Some(t_var)),
                Some(t_var),
                and_and_not,
            );
            interrupt()?;

            // Symmetrically for `t_false`.
            let removes_false = Bdd::fused_ternary_flip_op(
                (&result, None),
                (&can_go_down, None),
                (&result, Some(f_var)),
                Some(f_var),
                and_and_not,
            );
            interrupt()?;

            if !removes_true.is_false() || !removes_false.is_false() {
                result = bdd!(vars, result | (removes_true | removes_false));
                interrupt()?;

                if log_essential(log_level, result.size()) {
                    println!(
                        "Computing sub-spaces: {}[nodes:{}].",
                        result.cardinality(),
                        result.size(),
                    );
                }
            }
        }
        Ok(result)
    }

    /// Construct a symbolic singleton for a [Space].
    pub fn mk_space(&self, space: &Space) -> Bdd {
        let mut valuation = BddPartialValuation::empty();
        for (i, (t_var, f_var)) in self.dual_variables.iter().enumerate() {
            match space.0[i] {
                ExtendedBoolean::Zero => {
                    valuation.set_value(*t_var, false);
                    valuation.set_value(*f_var, true);
                }
                ExtendedBoolean::One => {
                    valuation.set_value(*t_var, true);
                    valuation.set_value(*f_var, false);
                }
                ExtendedBoolean::Any => {
                    valuation.set_value(*t_var, true);
                    valuation.set_value(*f_var, true);
                }
            }
        }
        self.bdd_variable_set().mk_conjunctive_clause(&valuation)
    }

    /// A utility method which "materializes" the network spaces in the dual encoding into
    /// a set of vertices that reside in these places.
    ///
    /// See also [SymbolicSpaceContext::vertices_to_spaces], but note that these operations
    /// are not invertible, that is `vertices_to_spaces(spaces_to_vertices(x))` does not
    /// produce the set `x`.
    pub fn spaces_to_vertices(&self, bdd: &Bdd) -> Bdd {
        let mut space_vars = Vec::new();
        for (p, n) in &self.dual_variables {
            space_vars.push(*p);
            space_vars.push(*n);
        }
        Bdd::binary_op_with_exists(
            &self.space_to_vertex_bdd,
            bdd,
            biodivine_lib_bdd::op_function::and,
            &space_vars,
        )
    }

    /// Convert a set of vertices into a set of singleton spaces. That is, for each vertex,
    /// the corresponding space is created.
    ///
    /// In other words, this does not try to decompose the set into maximal spaces or anything
    /// like that, it converts each vertex 1:1 into a space.
    pub fn vertices_to_spaces(&self, bdd: &Bdd) -> Bdd {
        Bdd::binary_op_with_exists(
            &self.vertex_to_space_bdd,
            bdd,
            biodivine_lib_bdd::op_function::and,
            self.inner_ctx.state_variables(),
        )
    }

    /// The same as [SymbolicContext::eliminate_network_variable], but extended to the
    /// domain of a subspaces.
    pub fn eliminate_network_variable(&self, variable_id: VariableId) -> SymbolicSpaceContext {
        let mut result = self.clone();
        let (p_var, n_var) = self.dual_variables[variable_id.to_index()];
        let s_var = self.inner_ctx.get_state_variable(variable_id);
        result.inner_ctx = result.inner_ctx.eliminate_network_variable(variable_id);
        result.dual_variables.remove(variable_id.to_index());
        result.vertex_to_space_bdd = result.vertex_to_space_bdd.exists(&[p_var, n_var, s_var]);
        result.space_to_vertex_bdd = result.space_to_vertex_bdd.exists(&[p_var, n_var, s_var]);
        result
    }
}

fn and_and_not(a: Option<bool>, b: Option<bool>, c: Option<bool>) -> Option<bool> {
    // Just `a & b & !c`:
    match (a, b, c) {
        (Some(true), Some(true), Some(false)) => Some(true),
        (Some(false), _, _) => Some(false),
        (_, Some(false), _) => Some(false),
        (_, _, Some(true)) => Some(false),
        (_, _, _) => None,
    }
}

#[cfg(test)]
mod tests {
    use crate::biodivine_std::traits::Set;
    use crate::symbolic_async_graph::SymbolicAsyncGraph;
    use crate::trap_spaces::{NetworkSpaces, SymbolicSpaceContext};
    use crate::ExtendedBoolean::{One, Zero};
    use crate::{BooleanNetwork, FnUpdate, Space, VariableId};
    use biodivine_lib_bdd::bdd;

    #[test]
    fn test_basic_getter_functionality() {
        let network = BooleanNetwork::try_from_file("./aeon_models/005.aeon").unwrap();
        let ctx = SymbolicSpaceContext::new(&network);

        assert_eq!(ctx.get_dual_variables().len(), network.num_vars());
        let var = VariableId::from_index(1);
        let expected = (
            ctx.get_positive_variable(var),
            ctx.get_negative_variable(var),
        );
        assert_eq!(ctx.get_dual_variable_pair(var), expected);
    }

    #[test]
    fn test_super_and_sub_spaces() {
        let network = BooleanNetwork::try_from_file("./aeon_models/005.aeon").unwrap();
        let ctx = SymbolicSpaceContext::new(&network);
        let mut all_zero = Space::new(&network);
        for var in network.variables() {
            all_zero[var] = Zero;
        }
        let all_zero = ctx.mk_space(&all_zero);
        let super_spaces = ctx.mk_super_spaces(&all_zero);
        let sub_spaces = ctx.mk_sub_spaces(&all_zero);

        // all_zero should have only one subspace: itself.
        println!("{} {}", all_zero.cardinality(), sub_spaces.cardinality());
        assert!(sub_spaces.iff(&all_zero).is_true());

        let all_zero = NetworkSpaces::new(all_zero, &ctx);
        let super_spaces = NetworkSpaces::new(super_spaces, &ctx);

        assert!(all_zero.is_singleton());
        assert!(all_zero.is_subset(&super_spaces));
        assert_eq!(1.0, all_zero.approx_cardinality());

        // A state has exactly 2^n super-spaces, which in this case means 2^28.
        // The rationale is that every super-space has a unique subset of variables set to
        // `Any` instead of `Zero`. And the number of such subsets is 2^n.
        assert_eq!(268435456.0, super_spaces.approx_cardinality());

        let mut first_10 = Space::new(&network);
        for var in network.variables().take(10) {
            first_10[var] = One;
        }
        let first_10 = ctx.mk_space(&first_10);
        let super_spaces = ctx.mk_super_spaces(&first_10);
        let sub_spaces = ctx.mk_sub_spaces(&first_10);

        //let first_10 = NetworkSpaces::new(first_10, &ctx);
        let super_spaces = NetworkSpaces::new(super_spaces, &ctx);
        let sub_spaces = NetworkSpaces::new(sub_spaces, &ctx);

        // There are 18 free variables and 10 fixed variables, hence the number of super-spaces
        // should be 2^10, and the number of sub-spaces should be 3^18.
        assert_eq!(1024.0, super_spaces.approx_cardinality());
        assert_eq!(387420489.0, sub_spaces.approx_cardinality());
    }

    #[test]
    fn test_can_go_to_true() {
        let network = BooleanNetwork::try_from_file("./aeon_models/005.aeon").unwrap();
        let ctx = SymbolicSpaceContext::new(&network);
        let vars = ctx.bdd_variable_set();
        let and_function = bdd!(vars, "v_ADD" & "v_ATM");
        let or_function = bdd!(vars, "v_ADD" | "v_ATM");
        let and_up = ctx.mk_can_go_to_true(&and_function);
        let or_up = ctx.mk_can_go_to_true(&or_function);

        let unit = ctx.mk_unit_spaces();
        let and_up = NetworkSpaces::new(and_up, &ctx).intersect(&unit);
        let or_up = NetworkSpaces::new(or_up, &ctx).intersect(&unit);

        // In every space where (x & y) goes to true, (x | y) also goes to true.
        assert!(and_up.is_subset(&or_up));
        assert!(!or_up.is_subset(&and_up));
        // In this case, the number of such spaces is k*3^26 (remaining variables are unconstrained)
        // where `k=4` for AND ([*,*], [1,*], [*,1], [1,1]) and `k=8` for OR ([*,*], [*,0], [0,*]
        // [*,1], [1,*], [0,1], [1,0], [1,1]; everything except [0,0]).
        assert_eq!(4.0 * 2541865828329.0, and_up.approx_cardinality());
        assert_eq!(8.0 * 2541865828329.0, or_up.approx_cardinality());
    }

    #[test]
    fn conversions() {
        let network = BooleanNetwork::try_from_file("./aeon_models/005.aeon").unwrap();
        let ctx = SymbolicSpaceContext::new(&network);
        let stg = SymbolicAsyncGraph::with_space_context(&network, &ctx).unwrap();

        assert_eq!(
            stg.empty_vertices().to_singleton_spaces(&ctx),
            ctx.mk_empty_spaces(),
        );

        assert_eq!(
            stg.empty_colored_vertices().to_singleton_spaces(&ctx),
            ctx.mk_empty_colored_spaces(),
        );

        assert_eq!(
            stg.unit_vertices().exact_cardinality(),
            stg.unit_vertices()
                .to_singleton_spaces(&ctx)
                .exact_cardinality(),
        );

        assert_eq!(
            stg.unit_colored_vertices().exact_cardinality(),
            stg.unit_colored_vertices()
                .to_singleton_spaces(&ctx)
                .exact_cardinality(),
        );

        assert_eq!(
            ctx.mk_unit_spaces().to_vertices(&ctx),
            stg.mk_unit_vertices(),
        );

        assert_eq!(
            ctx.mk_unit_colored_spaces(&stg).to_colored_vertices(&ctx),
            stg.mk_unit_colored_vertices(),
        );

        let mut space = Space::new(&network);
        space[VariableId(0)] = One;
        space[VariableId(2)] = Zero;
        space[VariableId(6)] = One;

        let space = NetworkSpaces::new(ctx.mk_space(&space), &ctx);
        assert!(space.is_singleton());
        let vertices = space.to_vertices(&ctx);
        assert_eq!(
            vertices,
            stg.mk_subspace(&[
                (VariableId(0), true),
                (VariableId(2), false),
                (VariableId(6), true)
            ])
            .vertices()
        );
    }

    #[test]
    fn elimination() {
        let mut network = BooleanNetwork::try_from_file("./aeon_models/005.aeon").unwrap();
        let foo = network.add_parameter("foo", 3).unwrap();
        network.set_update_function(VariableId(0), None).unwrap();
        let v1 = network.as_graph().find_variable("v_ATM").unwrap();
        let v2 = network.as_graph().find_variable("v_CHKREC").unwrap();
        let v3 = network.as_graph().find_variable("v_ATR").unwrap();
        network
            .set_update_function(
                VariableId(4),
                Some(FnUpdate::mk_basic_param(foo, &[v1, v2, v3])),
            )
            .unwrap();
        let ctx = SymbolicSpaceContext::new(&network);
        let ctx2 = ctx.eliminate_network_variable(VariableId(1));

        assert_eq!(
            ctx.inner_ctx.num_state_variables(),
            ctx2.inner_ctx.num_state_variables() + 1
        );
        assert_eq!(
            ctx.inner_ctx.num_parameter_variables(),
            ctx2.inner_ctx.num_parameter_variables()
        );
        assert_eq!(ctx.dual_variables.len(), ctx2.dual_variables.len() + 1);

        assert!(ctx
            .vertex_to_space_bdd
            .imp(&ctx2.vertex_to_space_bdd)
            .is_true());
        assert!(ctx
            .space_to_vertex_bdd
            .imp(&ctx2.space_to_vertex_bdd)
            .is_true());
    }
}
