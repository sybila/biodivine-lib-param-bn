use crate::biodivine_std::bitvector::{ArrayBitVector, BitVector};
use crate::biodivine_std::traits::Set;
use crate::symbolic_async_graph::_impl_regulation_constraint::apply_regulation_constraints;
use crate::symbolic_async_graph::{
    GraphColoredVertices, GraphColors, GraphVertices, SymbolicAsyncGraph, SymbolicContext,
};
use crate::{BooleanNetwork, FnUpdate, VariableId};
use crate::{ExtendedBoolean, Space};
use biodivine_lib_bdd::{bdd, Bdd, BddVariable};
use std::collections::HashMap;

impl SymbolicAsyncGraph {
    pub fn new(network: BooleanNetwork) -> Result<SymbolicAsyncGraph, String> {
        let context = SymbolicContext::new(&network)?;
        let unit_bdd = apply_regulation_constraints(context.bdd.mk_true(), &network, &context)?;

        // For each variable, pre-compute contexts where the update function can be applied, i.e.
        // (F = 1 & var = 0) | (F = 0 & var = 1)
        let update_functions = network
            .graph
            .variables()
            .map(|variable| {
                let regulators = network.regulators(variable);
                let function_is_one = network
                    .get_update_function(variable)
                    .as_ref()
                    .map(|fun| context.mk_fn_update_true(fun))
                    .unwrap_or_else(|| context.mk_implicit_function_is_true(variable, &regulators));
                let variable_is_zero = context.mk_state_variable_is_true(variable).not();
                bdd!(variable_is_zero <=> function_is_one)
            })
            .collect();

        Ok(SymbolicAsyncGraph {
            vertex_space: (
                GraphColoredVertices::new(context.bdd.mk_false(), &context),
                GraphColoredVertices::new(unit_bdd.clone(), &context),
            ),
            color_space: (
                GraphColors::new(context.bdd.mk_false(), &context),
                GraphColors::new(unit_bdd.clone(), &context),
            ),
            symbolic_context: context,
            unit_bdd,
            network,
            update_functions,
        })
    }
}

/// Examine the general properties of the graph.
impl SymbolicAsyncGraph {
    /// Return a reference to the original Boolean network.
    pub fn as_network(&self) -> &BooleanNetwork {
        &self.network
    }

    /// Return a reference to the symbolic context of this graph.
    pub fn symbolic_context(&self) -> &SymbolicContext {
        &self.symbolic_context
    }

    /// Create a colored vertex set with a fixed value of the given variable.
    pub fn fix_network_variable(&self, variable: VariableId, value: bool) -> GraphColoredVertices {
        let bdd_variable = self.symbolic_context.state_variables[variable.0];
        GraphColoredVertices::new(
            self.unit_bdd.var_select(bdd_variable, value),
            &self.symbolic_context,
        )
    }

    /// Create a vertex set with a fixed value of the given network variable.
    ///
    /// Note that if you only need the vertices, this can be faster than `fix_network_variable`,
    /// since it does not involve the BDD of color constraints.
    pub fn fix_vertices_with_network_variable(
        &self,
        variable: VariableId,
        value: bool,
    ) -> GraphVertices {
        let bdd_variable = self.symbolic_context.state_variables[variable.0];
        GraphVertices::new(
            self.symbolic_context.bdd.mk_literal(bdd_variable, value),
            &self.symbolic_context,
        )
    }

    /// Make a witness network for one color in the given set.
    pub fn pick_witness(&self, colors: &GraphColors) -> BooleanNetwork {
        if colors.is_empty() {
            panic!("Cannot create witness for empty color set.");
        }
        let witness_valuation = colors.bdd.sat_witness().unwrap();
        let mut witness = self.network.clone();
        for variable in witness.graph.variables() {
            if let Some(function) = &mut witness.update_functions[variable.0] {
                let instantiated_expression = self
                    .symbolic_context
                    .instantiate_fn_update(&witness_valuation, function)
                    .to_boolean_expression(&self.symbolic_context.bdd);
                *function =
                    FnUpdate::try_from_expression(instantiated_expression, self.network.as_graph())
                        .unwrap();
            } else {
                let regulators = self.network.regulators(variable);
                let instantiated_expression = self
                    .symbolic_context
                    .instantiate_implicit_function(&witness_valuation, variable, &regulators)
                    .to_boolean_expression(&self.symbolic_context.bdd);
                let instantiated_fn_update =
                    FnUpdate::try_from_expression(instantiated_expression, self.network.as_graph());
                witness.update_functions[variable.0] = instantiated_fn_update;
            }
        }
        // Remove all explicit parameters since they have been eliminated.
        witness.parameters.clear();
        witness.parameter_to_index.clear();
        witness
    }

    /// Reference to an empty color set.
    pub fn empty_colors(&self) -> &GraphColors {
        &self.color_space.0
    }

    /// Make a new copy of empty color set.
    pub fn mk_empty_colors(&self) -> GraphColors {
        self.color_space.0.clone()
    }

    /// Reference to a unit color set.
    pub fn unit_colors(&self) -> &GraphColors {
        &self.color_space.1
    }

    /// Make a new copy of unit color set.
    pub fn mk_unit_colors(&self) -> GraphColors {
        self.color_space.1.clone()
    }

    /// Reference to an empty colored vertex set.
    pub fn empty_vertices(&self) -> &GraphColoredVertices {
        &self.vertex_space.0
    }

    /// Make a new copy of empty vertex set.
    pub fn mk_empty_vertices(&self) -> GraphColoredVertices {
        self.vertex_space.0.clone()
    }

    /// Reference to a unit colored vertex set.
    pub fn unit_colored_vertices(&self) -> &GraphColoredVertices {
        &self.vertex_space.1
    }

    /// Make a new copy of unit vertex set.
    pub fn mk_unit_colored_vertices(&self) -> GraphColoredVertices {
        self.vertex_space.1.clone()
    }

    /// Compute a subset of the unit vertex set that is specified using the given list
    /// of `(variable, value)` pairs. That is, the resulting set contains only those
    /// vertices that have all the given variables set to their respective values.
    ///
    /// *Note:* The reason this method takes a slice and not, e.g., a `HashMap` is that:
    ///  - (a) If constant, slices are much easier to write in code (i.e. we can write
    /// `graph.mk_subspace(&[(a, true), (b, false)])` -- there is no such syntax for a map).
    ///  - (b) This is already used by the internal BDD API, so the conversion is less involved.
    pub fn mk_subspace(&self, values: &[(VariableId, bool)]) -> GraphColoredVertices {
        let partial_valuation: Vec<(BddVariable, bool)> = values
            .iter()
            .map(|(id, value)| (self.symbolic_context.state_variables[id.0], *value))
            .collect();
        self.select_partial_valuation(&partial_valuation)
    }

    /// Return true of the given set is a trap set (also invariant set; set with no outgoing
    /// transitions).
    pub fn is_trap_set(&self, set: &GraphColoredVertices) -> bool {
        self.can_post_out(set).is_empty()
    }

    /// This is the same as `mk_subspace`, but it allows you to specify the partial valuation
    /// using a slice of optional Booleans instead of mapping `VariableId` objects.
    ///
    /// Such slice may be easier obtain for example when one is starting with a network state
    /// (vertex) that is already represented as a `Vec<bool>`. In this case, it may be easier
    /// to convert `Vec<bool>` to `Vec<Option<bool>>` and then simply erase the undesired values.
    pub fn mk_partial_vertex(&self, state: &[Option<bool>]) -> GraphColoredVertices {
        let partial_valuation: Vec<(BddVariable, bool)> = state
            .iter()
            .enumerate()
            .filter_map(|(index, value)| {
                value
                    .as_ref()
                    .map(|value| (self.symbolic_context.state_variables[index], *value))
            })
            .collect();
        self.select_partial_valuation(&partial_valuation)
    }

    /// Construct a vertex set that only contains one vertex, but all colors
    ///
    pub fn vertex(&self, state: &ArrayBitVector) -> GraphColoredVertices {
        assert_eq!(state.len(), self.network.num_vars());
        // TODO: When breaking changes will be possible, this should add a `mk_` prefix.
        let partial_valuation: Vec<(BddVariable, bool)> = state
            .values()
            .into_iter()
            .enumerate()
            .map(|(i, v)| (self.symbolic_context.state_variables[i], v))
            .collect();
        self.select_partial_valuation(&partial_valuation)
    }

    /// **(internal)** Construct a subset of the `unit_bdd` with respect to the given partial
    /// valuation of BDD variables.
    fn select_partial_valuation(
        &self,
        partial_valuation: &[(BddVariable, bool)],
    ) -> GraphColoredVertices {
        GraphColoredVertices::new(
            self.unit_bdd.select(partial_valuation),
            &self.symbolic_context,
        )
    }

    /// Create a copy of this `SymbolicAsyncGraph` where the vertex space is restricted to
    /// the given `set` (including possible transitions). The resulting graph is symbolically
    /// compatible with this graph, so the sets of vertices and colors are interchangeable.
    ///
    /// However, note that in a restricted graph, it may not hold that the unit vertex set is
    /// a product of some subset of vertices and some subset of colours (i.e. there may be
    /// vertices that are present for some colors and not for others, and vice-versa).
    pub fn restrict(&self, set: &GraphColoredVertices) -> SymbolicAsyncGraph {
        SymbolicAsyncGraph {
            network: self.network.clone(),
            symbolic_context: self.symbolic_context.clone(),
            vertex_space: (self.mk_empty_vertices(), set.clone()),
            color_space: (self.mk_empty_colors(), set.colors()),
            unit_bdd: set.bdd.clone(),
            update_functions: self
                .update_functions
                .iter()
                .enumerate()
                .map(|(i, function)| {
                    let symbolic_var = self.symbolic_context().state_variables()[i];
                    // Ensure that both source *and* target state of the transition are in the
                    // new, restricted state space:
                    Bdd::fused_ternary_flip_op(
                        (function, None),
                        (&set.bdd, None),
                        (&set.bdd, Some(symbolic_var)),
                        None,
                        |a, b, c| {
                            // a & b & c
                            match (a, b, c) {
                                (Some(true), Some(true), Some(true)) => Some(true),
                                (Some(false), _, _) => Some(false),
                                (_, Some(false), _) => Some(false),
                                (_, _, Some(false)) => Some(false),
                                _ => None,
                            }
                        },
                    )
                })
                .collect(),
        }
    }

    /// Fined the smallest subspace (hypercube) that encapsulates all the vertices
    /// within this set (colors are not affected).
    ///
    /// Keep in mind that since the colors are not affected, the result might not pass
    /// through `GraphColoredVertices::is_subspace`, but the `vertices()` set should pass
    /// this check.
    pub fn wrap_in_symbolic_subspace(&self, set: &GraphColoredVertices) -> GraphColoredVertices {
        // I'm not quite ready to make this method public...
        fn make_variable_free(
            stg: &SymbolicAsyncGraph,
            var: VariableId,
            cube: &GraphColoredVertices,
        ) -> GraphColoredVertices {
            let bdd_var = stg.symbolic_context().get_state_variable(var);
            let relaxed_bdd = cube.as_bdd().var_project(bdd_var);
            stg.empty_vertices().copy(relaxed_bdd)
        }

        let mut result = set.clone();
        for var in self.as_network().variables() {
            let var_true = self.fix_network_variable(var, true);
            let var_false = self.fix_network_variable(var, false);
            if !(result.is_subset(&var_true) || result.is_subset(&var_false)) {
                result = make_variable_free(self, var, &result);
            }
        }
        result
    }

    /// Find the smallest subspace (hypercube) that contains the given set of vertices.
    pub fn wrap_in_subspace(&self, set: &GraphVertices) -> Space {
        let clause = set.bdd.necessary_clause().unwrap();
        let mut result = Space::new(self.as_network());
        for var in self.as_network().variables() {
            let bdd_var = self.symbolic_context.state_variables[var.to_index()];
            if let Some(value) = clause.get_value(bdd_var) {
                if value {
                    result[var] = ExtendedBoolean::One;
                } else {
                    result[var] = ExtendedBoolean::Zero;
                }
            }
        }
        result
    }

    /// Fix a variable in the underlying symbolic representation and then erase it completely
    /// from the result. The resulting representation still "contains" the variable, but the
    /// update functions no longer depend on it.
    pub fn restrict_variable_in_graph(&self, var: VariableId, value: bool) -> SymbolicAsyncGraph {
        let bdd_var = self.symbolic_context.state_variables[var.0];
        SymbolicAsyncGraph {
            network: self.network.clone(),
            symbolic_context: self.symbolic_context.clone(),
            vertex_space: (
                self.mk_empty_vertices(),
                self.unit_colored_vertices()
                    .restrict_network_variable(var, value),
            ),
            color_space: (self.mk_empty_colors(), self.mk_unit_colors()),
            unit_bdd: self.unit_bdd.var_restrict(bdd_var, value),
            update_functions: self
                .update_functions
                .iter()
                .map(|f| f.var_restrict(bdd_var, value))
                .collect(),
        }
    }
}

impl SymbolicAsyncGraph {
    /// Compute the set of all possible colours (instantiations) of this (*main*) network that are
    /// represented by the supplied more specific *sub-network*.
    ///
    /// Note that this is a rather non-trivial theoretical problem. Consequently,
    /// the implementation is currently limited such that it only supports the following special
    /// case. In the future, these restrictions may be lifted as we add better equivalence
    /// checking algorithms:
    ///  - The two networks have the same variables.
    ///  - All parameters used in the sub-network must also be declared in the
    ///  main network (with the same arity).
    ///  - The regulations are identical in both networks (including monotonicity/observability).
    ///  - If the main network has an update function, the sub-network must have the same
    ///  update function (tested using the abstract syntax tree, not semantics).
    ///  - If the main network has an erased update function, the sub-network can have
    ///  a fully specified function (no parameters) instead.
    ///  - The sub-network and main network are consistent with the shared regulatory graph.
    ///
    /// If all of these conditions are met, the function returns a `ColorSet` representing all
    /// instantiations of the sub-network represented using the main network encoding. Otherwise,
    /// an error indicates which conditions were not met.
    ///
    pub fn mk_subnetwork_colors(&self, network: &BooleanNetwork) -> Result<GraphColors, String> {
        let main_network = self.as_network();
        let sub_network = network;
        {
            // 1.1 Verify that the networks have the same variables.
            for var in main_network.variables() {
                let name = main_network.get_variable_name(var);
                if sub_network.as_graph().find_variable(name).is_none() {
                    return Err(format!("Variable `{}` not found in the sub-network.", name));
                }
            }
            for var in sub_network.variables() {
                let name = sub_network.get_variable_name(var);
                if main_network.as_graph().find_variable(name).is_none() {
                    return Err(format!(
                        "Variable `{}` not found in the main network.",
                        name
                    ));
                }
            }
        }

        // 1.2 Make mapping vectors for variable IDs. For most networks, this is just identity,
        // but better safe than sorry.
        let main_to_sub = main_network
            .variables()
            .map(|id| {
                let name = main_network.get_variable_name(id);
                sub_network.as_graph().find_variable(name).unwrap()
            })
            .collect::<Vec<_>>();

        let sub_to_main = sub_network
            .variables()
            .map(|id| {
                let name = sub_network.get_variable_name(id);
                main_network.as_graph().find_variable(name).unwrap()
            })
            .collect::<Vec<_>>();

        {
            // 2.1 Verify that the sub-network has the same parameters as the main network.
            for param in sub_network.parameters() {
                let name = sub_network.get_parameter(param).get_name();
                if let Some(main_id) = main_network.find_parameter(name) {
                    let main_arity = main_network.get_parameter(main_id).get_arity();
                    if sub_network.get_parameter(param).get_arity() != main_arity {
                        return Err(format!("Arity mismatch for parameter `{}`.", name));
                    }
                } else {
                    return Err(format!("Parameter `{}` missing in the main network.", name));
                }
            }
        }

        // 2.2 Construct a mapping vector from the sub-network parameters to the main network.
        let param_sub_to_main = sub_network
            .parameters()
            .map(|id| {
                let name = sub_network.get_parameter(id).get_name();
                main_network.find_parameter(name).unwrap()
            })
            .collect::<Vec<_>>();

        {
            // 3.1 Verify that every regulation from main is in sub.
            for main_reg in main_network.as_graph().regulations() {
                let sub_reg = sub_network.as_graph().find_regulation(
                    main_to_sub[main_reg.regulator.0],
                    main_to_sub[main_reg.target.0],
                );
                if let Some(sub_reg) = sub_reg {
                    if sub_reg.observable != main_reg.observable
                        || sub_reg.monotonicity != main_reg.monotonicity
                    {
                        return Err(format!(
                            "Regulation `{:?}` is different in the sub-network (`{:?}`).",
                            main_reg, sub_reg
                        ));
                    }
                } else {
                    return Err(format!(
                        "Regulation `{:?}` not found in the sub-network.",
                        main_reg
                    ));
                }
            }
        }

        {
            // 3.2 Verify that every regulation from sub is in main.
            for sub_reg in sub_network.as_graph().regulations() {
                let main_reg = main_network.as_graph().find_regulation(
                    sub_to_main[sub_reg.regulator.0],
                    sub_to_main[sub_reg.target.0],
                );
                if main_reg.is_none() {
                    return Err(format!(
                        "Regulation `{:?} not found in the main network.`",
                        main_reg
                    ));
                }
                // We already tested that if the regulation exists, it is the same.
            }
        }

        // 4. Verify that every function in the sub-network is either identical to the main
        // network, or replaces an unknown function.
        for sub_var in sub_network.variables() {
            let main_var = sub_to_main[sub_var.0];
            let name = main_network.get_variable_name(main_var);
            if let Some(sub_fun) = sub_network.get_update_function(sub_var) {
                if let Some(main_fun) = main_network.get_update_function(main_var) {
                    let sub_fun_in_main = sub_fun.substitute(&sub_to_main, &param_sub_to_main);
                    if &sub_fun_in_main != main_fun {
                        return Err(format!("Functions of `{}` are different.", name));
                    }
                } else {
                    // Main has a missing function and sub specialises it.
                    if !sub_fun.collect_parameters().is_empty() {
                        return Err(format!(
                            "A specialised function of `{}` in the sub-network has parameters.",
                            name
                        ));
                    }
                }
            } else {
                let main_fun = main_network.get_update_function(main_var);
                if main_fun.is_some() {
                    return Err(format!(
                        "Sub-network erases existing function of `{}`.",
                        name
                    ));
                }
            }
        }

        // 5. Check that the sub-network is valid.
        let sub_network_graph = SymbolicAsyncGraph::new(sub_network.clone());
        if sub_network_graph.is_err() {
            return Err("Sub-network is not consistent with the regulatory graph.".to_string());
        }

        // 6. Now we can actually start computing the thing...
        let mut colors = self.unit_bdd.clone();

        for main_var in main_network.variables() {
            let sub_var = main_to_sub[main_var.0];
            let name = main_network.get_variable_name(main_var);

            if main_network.get_update_function(main_var).is_some() {
                // We already checked that the functions are the same in this case.
                continue;
            }

            if let Some(specialised_function) = sub_network.get_update_function(sub_var) {
                let function_table = self
                    .symbolic_context()
                    .get_implicit_function_table(main_var);
                let function_args = main_network.regulators(main_var);
                let specialised_function =
                    specialised_function.substitute(&sub_to_main, &param_sub_to_main);

                let mut valuation = main_network
                    .variables()
                    .map(|it| (it, false))
                    .collect::<HashMap<_, _>>();
                for (input, bdd_var) in function_table {
                    function_args
                        .iter()
                        .zip(input.iter())
                        .for_each(|(id, value)| {
                            valuation.insert(*id, *value);
                        });

                    if let Some(output) = specialised_function.evaluate(&valuation) {
                        let literal = self
                            .symbolic_context
                            .bdd_variable_set()
                            .mk_literal(bdd_var, output);
                        colors = colors.and(&literal);
                    } else {
                        return Err(format!("Unexpected error when evaluating `{}`.", name));
                    }
                }
            }
            // Else: The function is not specialised in the sub-network. It is safe to skip.
        }

        Ok(self.unit_colors().copy(colors))
    }
}

#[cfg(test)]
mod tests {
    use crate::biodivine_std::bitvector::BitVector;
    use crate::biodivine_std::traits::Set;
    use crate::symbolic_async_graph::SymbolicAsyncGraph;
    use crate::BooleanNetwork;
    use std::convert::TryFrom;

    #[test]
    fn test_subnetworks() {
        let network_1 = BooleanNetwork::try_from(
            r"
            b -> a
            c -> a
            a -> a
            a -> b
            b -> b
            c -> c
            a -> c
        ",
        )
        .unwrap();
        let sg = SymbolicAsyncGraph::new(network_1).unwrap();

        assert_eq!(
            sg.mk_unit_colors(),
            sg.mk_subnetwork_colors(sg.as_network()).unwrap()
        );

        // Fixes only the function of `a`, not the remaining variables:
        let network_2 = BooleanNetwork::try_from(
            r"
            b -> a
            c -> a
            a -> a
            a -> b
            b -> b
            c -> c
            a -> c
            $a: a | (b & c)
        ",
        )
        .unwrap();

        let sub_colors = sg.mk_subnetwork_colors(&network_2).unwrap();
        assert_eq!(4.0, sub_colors.approx_cardinality());
        assert_eq!(36.0, sg.unit_colors().approx_cardinality());

        let network_3 = BooleanNetwork::try_from(
            r"
            b -> a
            c -> a
            a -> a
            a -> b
            b -> b
            c -> c
            a -> c
            $a: a | (b & c)
            $b: a & b
        ",
        )
        .unwrap();

        let sub_colors = sg.mk_subnetwork_colors(&network_3).unwrap();
        assert_eq!(2.0, sub_colors.approx_cardinality());

        let sg_2 = SymbolicAsyncGraph::new(network_2).unwrap();
        let sub_colors = sg_2.mk_subnetwork_colors(&network_3).unwrap();
        assert_eq!(2.0, sub_colors.approx_cardinality());

        // Test some of the error conditions:

        // Different variables:
        let result = sg.mk_subnetwork_colors(
            &BooleanNetwork::try_from(
                r"
            a -> b
            b -> a
        ",
            )
            .unwrap(),
        );
        assert!(result.is_err());

        let result = sg.mk_subnetwork_colors(
            &BooleanNetwork::try_from(
                r"
            a -> b
            b -> a
            a -> c
            c -> d
        ",
            )
            .unwrap(),
        );
        assert!(result.is_err());

        // Different regulations:
        let result = sg.mk_subnetwork_colors(
            &BooleanNetwork::try_from(
                r"
            b -> a
            c -> a
            a -> a
            a -> b
            b -> b
            a -> c
        ",
            )
            .unwrap(),
        );
        assert!(result.is_err());

        let result = sg.mk_subnetwork_colors(
            &BooleanNetwork::try_from(
                r"
            b -> a
            c -> a
            a -> a
            a -> b
            b -> b
            c -> c
            a -> c
            b -> c
        ",
            )
            .unwrap(),
        );
        assert!(result.is_err());

        let result = sg.mk_subnetwork_colors(
            &BooleanNetwork::try_from(
                r"
            b -> a
            c -> a
            a -> a
            a -> b
            b -> b
            c -| c
            a -> c
        ",
            )
            .unwrap(),
        );
        assert!(result.is_err());

        // Inconsistent sub-network:
        let result = sg.mk_subnetwork_colors(
            &BooleanNetwork::try_from(
                r"
            b -> a
            c -> a
            a -> a
            a -> b
            b -> b
            c -> c
            a -> c
            $a: c | b
        ",
            )
            .unwrap(),
        );
        assert!(result.is_err());

        // Mismatched update function:
        let result = sg_2.mk_subnetwork_colors(
            &BooleanNetwork::try_from(
                r"
            b -> a
            c -> a
            a -> a
            a -> b
            b -> b
            c -> c
            a -> c
            $a: a | (b | c)
        ",
            )
            .unwrap(),
        );
        assert!(result.is_err());

        // Use of new parameters in the specialised function:
        let result = sg.mk_subnetwork_colors(
            &BooleanNetwork::try_from(
                r"
            b -> a
            c -> a
            a -> a
            a -> b
            b -> b
            c -> c
            a -> c
            $a: a | f(b, c)
        ",
            )
            .unwrap(),
        );
        assert!(result.is_err());

        // Function erasure:
        let result = sg_2.mk_subnetwork_colors(
            &BooleanNetwork::try_from(
                r"
            b -> a
            c -> a
            a -> a
            a -> b
            b -> b
            c -> c
            a -> c
        ",
            )
            .unwrap(),
        );
        assert!(result.is_err());
    }

    #[test]
    fn test_constraints_1() {
        let network = BooleanNetwork::try_from("a -> t \n $a: true").unwrap();
        let graph = SymbolicAsyncGraph::new(network).unwrap();
        assert_eq!(1.0, graph.unit_colors().approx_cardinality());
        let network = BooleanNetwork::try_from("a -| t \n $a: true").unwrap();
        let graph = SymbolicAsyncGraph::new(network).unwrap();
        assert_eq!(1.0, graph.unit_colors().approx_cardinality());
        let network = BooleanNetwork::try_from("a ->? t \n $a: true").unwrap();
        let graph = SymbolicAsyncGraph::new(network).unwrap();
        assert_eq!(3.0, graph.unit_colors().approx_cardinality());
        let network = BooleanNetwork::try_from("a -|? t \n $a: true").unwrap();
        let graph = SymbolicAsyncGraph::new(network).unwrap();
        assert_eq!(3.0, graph.unit_colors().approx_cardinality());
        let network = BooleanNetwork::try_from("a -? t \n $a: true").unwrap();
        let graph = SymbolicAsyncGraph::new(network).unwrap();
        assert_eq!(2.0, graph.unit_colors().approx_cardinality());
        let network = BooleanNetwork::try_from("a -?? t \n $a: true").unwrap();
        let graph = SymbolicAsyncGraph::new(network).unwrap();
        assert_eq!(4.0, graph.unit_colors().approx_cardinality());
    }

    #[test]
    fn test_constraints_2() {
        /*        a&!b a  a|!b
           a b | f_1 f_2 f_3
           0 0 |  0   0   1
           0 1 |  0   0   0
           1 0 |  1   1   1
           1 1 |  0   1   1
        */
        let network = "
            a -> t \n b -|? t
            $a: true \n $b: true
        ";
        let network = BooleanNetwork::try_from(network).unwrap();
        let graph = SymbolicAsyncGraph::new(network).unwrap();
        assert_eq!(3.0, graph.unit_colors().approx_cardinality());
    }

    /* For a monotonous function, the cardinality should follow dedekind numbers... */

    #[test]
    fn test_monotonicity_2() {
        let network = "
            a ->? t \n b -|? t
            $a: true \n $b: true
        ";
        let network = BooleanNetwork::try_from(network).unwrap();
        let graph = SymbolicAsyncGraph::new(network).unwrap();
        assert_eq!(6.0, graph.unit_colors().approx_cardinality());
    }

    #[test]
    fn test_monotonicity_3() {
        let network = "
            a ->? t \n b -|? t \n c ->? t
            $a: true \n $b: true \n $c: true
        ";
        let network = BooleanNetwork::try_from(network).unwrap();
        let graph = SymbolicAsyncGraph::new(network).unwrap();
        assert_eq!(20.0, graph.unit_colors().approx_cardinality());
    }

    #[test]
    fn test_monotonicity_4() {
        let network = "
            a ->? t \n b -|? t \n c ->? t \n d -|? t
            $a: true \n $b: true \n $c: true \n $d: true
        ";
        let network = BooleanNetwork::try_from(network).unwrap();
        let graph = SymbolicAsyncGraph::new(network).unwrap();
        assert_eq!(168.0, graph.unit_colors().approx_cardinality());
    }

    #[test]
    fn test_invalid_function() {
        let network = "
            a -> t \n b -| t \n
            $a: true \n $b: true \n $t: b
        ";
        let network = BooleanNetwork::try_from(network).unwrap();
        let graph = SymbolicAsyncGraph::new(network);
        assert!(graph.is_err());
    }

    #[test]
    fn test_subspace_creation() {
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
        let graph = SymbolicAsyncGraph::new(bn).unwrap();
        let a = graph.as_network().as_graph().find_variable("A").unwrap();
        let c = graph.as_network().as_graph().find_variable("C").unwrap();
        let sub_space_a = graph.fix_network_variable(a, true);
        let sub_space_c = graph.fix_network_variable(c, false);
        let sub_space = sub_space_a.intersect(&sub_space_c);

        let sub_space_1 = graph.mk_subspace(&[(a, true), (c, false)]);
        let sub_space_2 = graph.mk_partial_vertex(&[Some(true), None, Some(false)]);

        assert_eq!(sub_space_1, sub_space);
        assert_eq!(sub_space_2, sub_space);
    }

    #[test]
    fn test_restriction() {
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
        let graph = SymbolicAsyncGraph::new(bn).unwrap();
        let a = graph.as_network().as_graph().find_variable("A").unwrap();
        let b = graph.as_network().as_graph().find_variable("B").unwrap();
        let c = graph.as_network().as_graph().find_variable("C").unwrap();

        let original_a = graph
            .var_can_post(a, graph.unit_colored_vertices())
            .approx_cardinality();
        let original_b = graph
            .var_can_post(b, graph.unit_colored_vertices())
            .approx_cardinality();
        let original_c = graph
            .var_can_post(c, graph.unit_colored_vertices())
            .approx_cardinality();

        // Subspace 1*0
        let subspace = graph.mk_subspace(&[(a, true), (c, false)]);

        let restricted = graph.restrict(&subspace);

        let restricted_a = restricted
            .var_can_post(a, restricted.unit_colored_vertices())
            .approx_cardinality();
        let restricted_b = restricted
            .var_can_post(b, restricted.unit_colored_vertices())
            .approx_cardinality();
        let restricted_c = restricted
            .var_can_post(c, restricted.unit_colored_vertices())
            .approx_cardinality();

        assert_eq!(restricted.mk_unit_colored_vertices(), subspace);

        assert!(restricted_a < original_a && restricted_a == 0.0);
        assert!(restricted_b < original_b && restricted_b > 0.0);
        assert!(restricted_c < original_c && restricted_c == 0.0);
    }

    /*
        This is essentially a copy paste from the tutorial, but for some reason code coverage
        does not count documentation tests, so let's make a copy here!
    */
    #[test]
    fn basic_test() {
        // Boolean network from the previous tutorial:
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
        assert_eq!(32.0, stg.unit_colored_vertices().approx_cardinality());
        assert_eq!(
            8.0,
            stg.unit_colored_vertices().vertices().approx_cardinality()
        );
        assert_eq!(
            4.0,
            stg.unit_colored_vertices().colors().approx_cardinality()
        );
        assert!(stg.empty_vertices().is_empty());
        assert!(stg.mk_empty_colors().is_empty());
        assert_eq!(stg.mk_unit_colors(), stg.unit_colored_vertices().colors());
        assert_eq!(3, stg.as_network().num_vars());

        let id_a = stg.as_network().as_graph().find_variable("A").unwrap();
        stg.fix_network_variable(id_a, true);
        let witness = stg.pick_witness(stg.unit_colors());
        assert_eq!(0, witness.parameters().count());

        for vertex in stg.unit_colored_vertices().vertices().materialize().iter() {
            println!(
                "Value of A in state {:?} is {}",
                vertex,
                vertex.get(id_a.into())
            );
            let singleton = stg.vertex(&vertex);
            assert_eq!(4.0, singleton.approx_cardinality());
            assert_eq!(1.0, singleton.vertices().approx_cardinality());
        }

        let one_color = stg.unit_colors().pick_singleton();
        assert_eq!(1.0, one_color.approx_cardinality());
        assert_eq!(
            4.0,
            stg.unit_colored_vertices()
                .pick_vertex()
                .approx_cardinality()
        );
        assert_eq!(
            8.0,
            stg.unit_colored_vertices()
                .pick_color()
                .approx_cardinality()
        );
    }
}
