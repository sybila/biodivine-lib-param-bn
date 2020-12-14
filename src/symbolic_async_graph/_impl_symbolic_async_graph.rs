use crate::symbolic_async_graph::{
    GraphColoredVertices, GraphColors, SymbolicAsyncGraph, SymbolicContext,
};
use crate::{BinaryOp, BooleanNetwork, FnUpdate, Monotonicity, RegulatoryGraph, VariableId};
use biodivine_lib_bdd::boolean_expression::BooleanExpression;
use biodivine_lib_bdd::{bdd, Bdd, BddVariableSet};
use biodivine_lib_std::collections::bitvectors::{ArrayBitVector, BitVector};
use biodivine_lib_std::param_graph::Params;

impl SymbolicAsyncGraph {
    pub fn new(network: BooleanNetwork) -> Result<SymbolicAsyncGraph, String> {
        let context = SymbolicContext::new(&network)?;

        // For each variable, compute Bdd that is true exactly when its update function is true.
        let update_function_one: Vec<Bdd> = network
            .graph
            .variables()
            .map(|id| {
                let function = network.get_update_function(id);
                if let Some(function) = function {
                    context.mk_fn_update_true(function)
                } else {
                    context.mk_implicit_function_is_true(id, &network.regulators(id))
                }
            })
            .collect();

        let mut error_message = String::new();
        let mut unit_bdd = context.mk_constant(true);
        for reg in &network.graph.regulations {
            let reg_is_one = context.mk_state_variable_is_true(reg.regulator);
            let reg_is_zero = reg_is_one.not();
            let reg_var = context.state_variables[reg.regulator.0];
            let fn_is_one = &update_function_one[reg.target.0];
            let fn_is_zero = fn_is_one.not();
            /*
               Observability: { p | f_p is observable } =
                = projection({ (s, p) | f_p(s[x=0]) != f_p(s[x=1]) })
                ("exists an input where value of f changes")
               Activation: { p | f_p is activation } =
                = ! projection({ (s, p) | f_p(s[x=0]) = 1 & f_p(s[x=1]) = 0 })
               Inhibition: { p | f_p is inhibition } =
                = ! projection({ (s, p) | f_p(s[x=0]) = 0 & f_p(s[x=1]) = 1 })
                ("does not exist an input that validates monotonicity")

                                       !!!!!!
               Note that (f_p(s[x=1]) = 0) is NOT !(f_p(s[x=1]) = 1), because these
               translate to (f_p(s) = 0 & x=1)|x and !(f_p(s) = 1 & x=1) = f_p(s)=0 | x=0.
                                       !!!!!!
            */
            let observability = if reg.observable {
                let fn_x1_to_1 = bdd!(fn_is_one & reg_is_one).var_projection(reg_var);
                let fn_x0_to_1 = bdd!(fn_is_one & reg_is_zero).var_projection(reg_var);
                let observable = bdd!(!(fn_x1_to_1 <=> fn_x0_to_1));
                context
                    .state_variables
                    .iter()
                    .fold(observable, |a, b| a.var_projection(*b))
            } else {
                context.mk_constant(true)
            };
            if observability.is_false() {
                let problem = format!(
                    " - {} has no effect in {}.\n",
                    network.graph.get_variable(reg.regulator).name,
                    network.graph.get_variable(reg.target).name,
                );
                error_message = format!("{}{}", error_message, problem);
                print!("{}", problem);
            }
            let non_monotonous_pairs = match reg.monotonicity {
                Some(Monotonicity::Activation) => {
                    let fn_x0_to_1 = bdd!(fn_is_one & reg_is_zero).var_projection(reg_var);
                    let fn_x1_to_0 = bdd!(fn_is_zero & reg_is_one).var_projection(reg_var);
                    bdd!(fn_x0_to_1 & fn_x1_to_0)
                }
                Some(Monotonicity::Inhibition) => {
                    let fn_x0_to_0 = bdd!(fn_is_zero & reg_is_zero).var_projection(reg_var);
                    let fn_x1_to_1 = bdd!(fn_is_one & reg_is_one).var_projection(reg_var);
                    bdd!(fn_x0_to_0 & fn_x1_to_1)
                }
                None => context.mk_constant(false),
            };

            let monotonicity = context
                .state_variables
                .iter()
                .fold(non_monotonous_pairs, |a, b| a.var_projection(*b))
                .not();
            if monotonicity.is_false() {
                let monotonicity_str = match reg.monotonicity {
                    Some(Monotonicity::Activation) => "activating",
                    Some(Monotonicity::Inhibition) => "inhibiting",
                    None => "monotonous",
                };
                let problem = format!(
                    " - {} not {} in {}.\n",
                    network.graph.get_variable(reg.regulator).name,
                    monotonicity_str,
                    network.graph.get_variable(reg.target).name,
                );
                error_message = format!("{}{}", error_message, problem);
                print!("{}", problem);
            }

            // At this point, monotonicity and observability should be only
            // constrained on parameters, not state variables.

            let function_constraint = bdd!(monotonicity & observability);

            if function_constraint.is_false() {
                println!(
                    "Regulation {} -> {} has invalid constraints.",
                    network.graph.get_variable(reg.regulator).name,
                    network.graph.get_variable(reg.target).name,
                );
            }

            unit_bdd = bdd!(unit_bdd & function_constraint);
        }

        if unit_bdd.is_false() {
            return Err(format!(
                "No update functions satisfy given constraints: \n{}",
                error_message
            ));
        }

        // Compute pre-evaluated functions
        let update_functions = network
            .graph
            .variables()
            .map(|v| {
                let function_is_one = &update_function_one[v.0];
                let variable_is_zero = context.mk_state_variable_is_true(v).not();
                bdd!(variable_is_zero <=> function_is_one)
            })
            .collect();

        let p_var_count = context.bdd.num_vars() - network.graph.num_vars() as u16;
        return Ok(SymbolicAsyncGraph {
            empty_color_set: GraphColors::new(context.mk_constant(false), p_var_count),
            unit_color_set: GraphColors::new(unit_bdd.clone(), p_var_count),
            empty_set: GraphColoredVertices::new(context.mk_constant(false), p_var_count),
            unit_set: GraphColoredVertices::new(unit_bdd, p_var_count),
            symbolic_context: context,
            network,
            update_functions,
        });
    }
}

/// Examine the general properties of the graph.
impl SymbolicAsyncGraph {
    /// Return a reference to the original Boolean network.
    pub fn network(&self) -> &BooleanNetwork {
        return &self.network;
    }

    pub fn state_variable_true(&self, variable: VariableId) -> GraphColoredVertices {
        let bdd_var = self.symbolic_context.state_variables[variable.0];
        return GraphColoredVertices::new(
            self.symbolic_context.bdd.mk_var(bdd_var),
            self.symbolic_context.p_var_count,
        )
        .intersect(self.unit_vertices());
    }

    pub fn state_variable_false(&self, variable: VariableId) -> GraphColoredVertices {
        let bdd_var = self.symbolic_context.state_variables[variable.0];
        return GraphColoredVertices::new(
            self.symbolic_context.bdd.mk_not_var(bdd_var),
            self.symbolic_context.p_var_count,
        )
        .intersect(self.unit_vertices());
    }

    /// Return the total number of states/vertices in this graph.
    pub fn num_states(&self) -> usize {
        return 1 << self.network().graph.num_vars();
    }

    /// Make a witness network for one color in the given set.
    pub fn make_witness(&self, colors: &GraphColors) -> BooleanNetwork {
        if colors.is_empty() {
            panic!("Cannot create witness for empty color set.");
        }
        let witness_valuation = colors.bdd.sat_witness().unwrap();
        let mut witness = self.network.clone();
        for variable in witness.graph.variables() {
            if let Some(function) = &mut witness.update_functions[variable.0] {
                *function = to_fn_update(
                    self.symbolic_context
                        .instantiate_fn_update(&witness_valuation, function)
                        .to_boolean_expression(&self.symbolic_context.bdd),
                    self.network.as_graph(),
                );
            } else {
                witness.update_functions[variable.0] = Some(to_fn_update(
                    self.symbolic_context
                        .instantiate_implicit_function(
                            &witness_valuation,
                            variable,
                            &self.network.graph.regulators(variable),
                        )
                        .to_boolean_expression(&self.symbolic_context.bdd),
                    self.network.as_graph(),
                ));
            }
        }
        return witness;
    }

    /// Return an empty set of colors.
    pub fn empty_colors(&self) -> &GraphColors {
        return &self.empty_color_set;
    }

    /// Return a full set of colors.
    pub fn unit_colors(&self) -> &GraphColors {
        return &self.unit_color_set;
    }

    /// Return empty vertex set.
    pub fn empty_vertices(&self) -> &GraphColoredVertices {
        return &self.empty_set;
    }

    /// Return complete vertex set.
    pub fn unit_vertices(&self) -> &GraphColoredVertices {
        return &self.unit_set;
    }

    /// Construct a vertex set that only contains one vertex.
    pub fn vertex(&self, state: &ArrayBitVector) -> GraphColoredVertices {
        let mut state_bdd = self.unit_set.bdd.clone();
        for i_variable in 0..self.network.graph.num_vars() {
            let bdd_var = self.symbolic_context.state_variables[i_variable];
            let bdd = if state.get(i_variable) {
                self.symbolic_context.bdd.mk_var(bdd_var)
            } else {
                self.symbolic_context.bdd.mk_not_var(bdd_var)
            };
            state_bdd = state_bdd.and(&bdd);
        }
        return GraphColoredVertices::new(state_bdd, self.symbolic_context.p_var_count);
    }

    pub fn bdd_variables(&self) -> &BddVariableSet {
        return &self.symbolic_context.bdd;
    }
}

pub fn to_fn_update(e: BooleanExpression, graph: &RegulatoryGraph) -> FnUpdate {
    match e {
        BooleanExpression::Const(value) => FnUpdate::Const(value),
        BooleanExpression::Variable(name) => FnUpdate::Var(graph.find_variable(&name).unwrap()),
        BooleanExpression::Not(inner) => FnUpdate::Not(Box::new(to_fn_update(*inner, graph))),
        BooleanExpression::Or(l, r) => FnUpdate::Binary(
            BinaryOp::Or,
            Box::new(to_fn_update(*l, graph)),
            Box::new(to_fn_update(*r, graph)),
        ),
        BooleanExpression::And(l, r) => FnUpdate::Binary(
            BinaryOp::And,
            Box::new(to_fn_update(*l, graph)),
            Box::new(to_fn_update(*r, graph)),
        ),
        BooleanExpression::Iff(l, r) => FnUpdate::Binary(
            BinaryOp::Iff,
            Box::new(to_fn_update(*l, graph)),
            Box::new(to_fn_update(*r, graph)),
        ),
        BooleanExpression::Imp(l, r) => FnUpdate::Binary(
            BinaryOp::Imp,
            Box::new(to_fn_update(*l, graph)),
            Box::new(to_fn_update(*r, graph)),
        ),
        BooleanExpression::Xor(l, r) => FnUpdate::Binary(
            BinaryOp::Xor,
            Box::new(to_fn_update(*l, graph)),
            Box::new(to_fn_update(*r, graph)),
        ),
    }
}
/*
/// Symbolic graph exploration operations.
impl SymbolicAsyncGraph {
    /// Compute direct successors of `frontier` within the `universe` set under the given `VariableId`.
    pub fn post(
        &self,
        variable: VariableId,
        frontier: &GraphColoredVertices,
        universe: &GraphColoredVertices,
    ) -> GraphColoredVertices {
        let frontier = &frontier.bdd;
        let universe = &universe.bdd;
        let v = self.symbolic_context.state_variables[variable.0];
        let apply_function = &self.update_functions[variable.0];
        // This is equivalent to [frontier & ((v_is_one & function_is_zero) | (v_is_zero & function_is_one))]
        let can_perform_step: Bdd = bdd!(frontier & apply_function);
        let after_step_performed = can_perform_step.invert_input(v).and(universe);
        return GraphColoredVertices::new(after_step_performed, self.symbolic_context.p_var_count);
    }

    pub fn any_post(
        &self,
        variable: VariableId,
        frontier: &GraphColoredVertices,
    ) -> GraphColoredVertices {
        let frontier = &frontier.bdd;
        let v = self.symbolic_context.state_variables[variable.0];
        let apply_function = &self.update_functions[variable.0];
        // This is equivalent to [frontier & ((v_is_one & function_is_zero) | (v_is_zero & function_is_one))]
        let can_perform_step: Bdd = bdd!(frontier & apply_function);
        let after_step_performed = can_perform_step.invert_input(v);
        return GraphColoredVertices::new(after_step_performed, self.symbolic_context.p_var_count);
    }

    /// Compute vertices in `universe` that have a direct successor under `variable` in that `universe`.
    /// Can be used to compute sinks when trimming.
    pub fn has_post(
        &self,
        variable: VariableId,
        universe: &GraphColoredVertices,
    ) -> GraphColoredVertices {
        let universe = &universe.bdd;
        let v = self.symbolic_context.state_variables[variable.0];
        let apply_function = &self.update_functions[variable.0];
        let can_do_transition = bdd!(universe & apply_function);
        // This has to be universe and not sink_candidate because that's where we look for successors.
        let after_transition = universe.and(&can_do_transition.invert_input(v));
        return GraphColoredVertices::new(
            after_transition.invert_input(v),
            self.symbolic_context.p_var_count,
        );
    }

    pub fn has_any_post(
        &self,
        variable: VariableId,
        universe: &GraphColoredVertices,
    ) -> GraphColoredVertices {
        let universe = &universe.bdd;
        let apply_function = &self.update_functions[variable.0];
        let can_do_transition = bdd!(universe & apply_function);
        return GraphColoredVertices::new(can_do_transition, self.symbolic_context.p_var_count);
    }

    /// Compute direct predecessors of `frontier` within `universe` set under the given `VariableId`.
    pub fn pre(
        &self,
        variable: VariableId,
        frontier: &GraphColoredVertices,
        universe: &GraphColoredVertices,
    ) -> GraphColoredVertices {
        let frontier = &frontier.bdd;
        let universe = &universe.bdd;
        let v = self.symbolic_context.state_variables[variable.0];
        let apply_function = &self.update_functions[variable.0];
        let possible_predecessors = frontier.invert_input(v).and(universe);
        let can_perform_step = bdd!(possible_predecessors & apply_function);
        return GraphColoredVertices::new(can_perform_step, self.symbolic_context.p_var_count);
    }

    pub fn any_pre(
        &self,
        variable: VariableId,
        frontier: &GraphColoredVertices,
    ) -> GraphColoredVertices {
        let frontier = &frontier.bdd;
        let v = self.symbolic_context.state_variables[variable.0];
        let apply_function = &self.update_functions[variable.0];
        let possible_predecessors = frontier.invert_input(v);
        let can_perform_step = bdd!(possible_predecessors & apply_function);
        return GraphColoredVertices::new(can_perform_step, self.symbolic_context.p_var_count);
    }

    /// Compute vertices in `universe` that have a direct predecessor under `variable` in that `universe`.
    /// Can be used to compute sources when trimming.
    pub fn has_pre(
        &self,
        variable: VariableId,
        universe: &GraphColoredVertices,
    ) -> GraphColoredVertices {
        let universe = &universe.bdd;
        let v = self.symbolic_context.state_variables[variable.0];
        let apply_function = &self.update_functions[variable.0];
        let possible_predecessors = universe.invert_input(v).and(&universe);
        let can_do_transition = bdd!(possible_predecessors & apply_function);
        return GraphColoredVertices::new(
            can_do_transition.invert_input(v),
            self.symbolic_context.p_var_count,
        );
    }

    pub fn has_any_pre(
        &self,
        variable: VariableId,
        universe: &GraphColoredVertices,
    ) -> GraphColoredVertices {
        let universe = &universe.bdd;
        let v = self.symbolic_context.state_variables[variable.0];
        let apply_function = &self.update_functions[variable.0];
        let possible_predecessors = universe.invert_input(v);
        let can_do_transition = bdd!(possible_predecessors & apply_function);
        return GraphColoredVertices::new(
            can_do_transition.invert_input(v),
            self.symbolic_context.p_var_count,
        );
    }
}*/

#[cfg(test)]
mod tests {
    use crate::symbolic_async_graph::SymbolicAsyncGraph;
    use crate::BooleanNetwork;
    use std::convert::TryFrom;

    #[test]
    fn test_constraints_1() {
        let network = BooleanNetwork::try_from("a -> t \n $a: true").unwrap();
        let graph = SymbolicAsyncGraph::new(network).unwrap();
        assert_eq!(1.0, graph.unit_colors().cardinality());
        let network = BooleanNetwork::try_from("a -| t \n $a: true").unwrap();
        let graph = SymbolicAsyncGraph::new(network).unwrap();
        assert_eq!(1.0, graph.unit_colors().cardinality());
        let network = BooleanNetwork::try_from("a ->? t \n $a: true").unwrap();
        let graph = SymbolicAsyncGraph::new(network).unwrap();
        assert_eq!(3.0, graph.unit_colors().cardinality());
        let network = BooleanNetwork::try_from("a -|? t \n $a: true").unwrap();
        let graph = SymbolicAsyncGraph::new(network).unwrap();
        assert_eq!(3.0, graph.unit_colors().cardinality());
        let network = BooleanNetwork::try_from("a -? t \n $a: true").unwrap();
        let graph = SymbolicAsyncGraph::new(network).unwrap();
        assert_eq!(2.0, graph.unit_colors().cardinality());
        let network = BooleanNetwork::try_from("a -?? t \n $a: true").unwrap();
        let graph = SymbolicAsyncGraph::new(network).unwrap();
        assert_eq!(4.0, graph.unit_colors().cardinality());
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
        assert_eq!(3.0, graph.unit_colors().cardinality());
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
        assert_eq!(6.0, graph.unit_colors().cardinality());
    }

    #[test]
    fn test_monotonicity_3() {
        let network = "
            a ->? t \n b -|? t \n c ->? t
            $a: true \n $b: true \n $c: true
        ";
        let network = BooleanNetwork::try_from(network).unwrap();
        let graph = SymbolicAsyncGraph::new(network).unwrap();
        assert_eq!(20.0, graph.unit_colors().cardinality());
    }

    #[test]
    fn test_monotonicity_4() {
        let network = "
            a ->? t \n b -|? t \n c ->? t \n d -|? t
            $a: true \n $b: true \n $c: true \n $d: true
        ";
        let network = BooleanNetwork::try_from(network).unwrap();
        let graph = SymbolicAsyncGraph::new(network).unwrap();
        assert_eq!(168.0, graph.unit_colors().cardinality());
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
}
