use crate::bdd_params::{build_static_constraints, BddParameterEncoder};
use crate::symbolic_async_graph::{GraphColoredVertices, GraphColors, SymbolicAsyncGraph};
use crate::{BooleanNetwork, FnUpdate, VariableId};
use biodivine_lib_bdd::{
    bdd, Bdd, BddValuationIterator, BddVariable, BddVariableSet, BddVariableSetBuilder,
};
use biodivine_lib_std::param_graph::Params;
use biodivine_lib_std::IdState;
use std::ops::Shl;

impl SymbolicAsyncGraph {
    pub fn new(network: BooleanNetwork) -> SymbolicAsyncGraph {
        let mut bdd_variable_set = BddVariableSetBuilder::new();

        // First, handle BDD variables for parameters as in normal BddParameterEncoder.
        let explicit_function_tables: Vec<Vec<BddVariable>> =
            BddParameterEncoder::build_explicit_function_table(&network, &mut bdd_variable_set);
        let implicit_function_tables: Vec<Vec<BddVariable>> =
            BddParameterEncoder::build_implicit_function_table(&network, &mut bdd_variable_set);
        let regulators: Vec<Vec<VariableId>> =
            BddParameterEncoder::build_regulators_table(&network);

        // Now create values for state variables.
        let mut state_variables = Vec::new();
        for v in &network.graph.variables {
            let bdd_v = bdd_variable_set.make_variable(&format!("{}", v.name));
            state_variables.push(bdd_v);
        }

        let bdd_variable_set = bdd_variable_set.build();

        // Create a custom parameter encode which we use to evaluate functions and
        // compute static constraints. Admittedly, this is cheating a bit,
        // but for now this is reasonable...
        let function_context = BddParameterEncoder::build_custom_encoder(
            bdd_variable_set.clone(),
            explicit_function_tables,
            implicit_function_tables.clone(),
            regulators,
        );

        // Compute pre-evaluated functions
        let mut function_cache = Vec::new();
        for v in network.graph.variable_ids() {
            let regulators = network.graph.regulators(v);
            let function_is_one = if let Some(function) = network.get_update_function(v) {
                // When there is an explicit update function, we have to eval it one valuation at a time:
                Self::pre_compute_explicit_update_function(
                    &state_variables,
                    &function_context,
                    &regulators,
                    function,
                )
            } else {
                // When the update function is implicit, we just combine all (valuation => parameter):
                Self::pre_compute_implicit_update_function(
                    &state_variables,
                    &function_context,
                    &regulators,
                    &implicit_function_tables[v.0],
                )
            };
            let v_bdd_var = state_variables[v.0];
            let v_is_zero = bdd_variable_set.mk_not_var(v_bdd_var);
            function_cache.push(bdd!(v_is_zero <=> function_is_one));
        }

        let p_var_count = bdd_variable_set.num_vars() - network.graph.num_vars() as u16;
        let unit_bdd = build_static_constraints(&network, &function_context);
        return SymbolicAsyncGraph {
            empty_color_set: GraphColors::new(bdd_variable_set.mk_false(), p_var_count),
            unit_color_set: GraphColors::new(unit_bdd.clone(), p_var_count),
            empty_set: GraphColoredVertices::new(bdd_variable_set.mk_false(), p_var_count),
            unit_set: GraphColoredVertices::new(unit_bdd, p_var_count),
            update_functions: function_cache,
            p_var_count,
            network,
            bdd_variable_set,
            state_variables,
            function_context,
        };
    }

    fn pre_compute_implicit_update_function(
        state_variables: &Vec<BddVariable>,
        function_context: &BddParameterEncoder,
        regulators: &Vec<VariableId>,
        table: &Vec<BddVariable>,
    ) -> Bdd {
        return BddValuationIterator::new(regulators.len() as u16)
            .enumerate()
            .fold(
                function_context.bdd_variables.mk_true(),
                |function_is_one, (i, valuation)| {
                    let valuation_bdd = Self::extend_valuation_to_bdd(
                        &function_context.bdd_variables,
                        &state_variables,
                        &valuation.vector(),
                        &regulators,
                    );
                    let parameter = table[i];
                    let parameter_bdd = function_context.bdd_variables.mk_var(parameter);
                    bdd!(function_is_one & (valuation_bdd => parameter_bdd))
                },
            );
    }

    fn pre_compute_explicit_update_function(
        state_variables: &Vec<BddVariable>,
        function_context: &BddParameterEncoder,
        regulators: &Vec<VariableId>,
        function: &FnUpdate,
    ) -> Bdd {
        return BddValuationIterator::new(regulators.len() as u16).fold(
            function_context.bdd_variables.mk_true(),
            |function_is_one, valuation| {
                let valuation_vector = valuation.vector();
                let valuation_bdd = Self::extend_valuation_to_bdd(
                    &function_context.bdd_variables,
                    &state_variables,
                    &valuation_vector,
                    &regulators,
                );
                let valuation_state =
                    Self::extend_valuation_to_id_state(&valuation_vector, &regulators);
                let function_is_one_in_valuation: Bdd =
                    function._symbolic_eval(valuation_state, function_context);
                bdd!(function_is_one & (valuation_bdd => function_is_one_in_valuation))
            },
        );
    }

    /// Create a state variable BDD corresponding to the given valuation of state variables.
    /// Something like this should be a native lib-bdd operation (TODO).
    fn extend_valuation_to_bdd(
        vars: &BddVariableSet,
        state_variables: &Vec<BddVariable>,
        valuation: &Vec<bool>,
        regulators: &Vec<VariableId>,
    ) -> Bdd {
        // valuation.len == regulators.len
        // variable_id \in state_variables.indices
        let mut bdd = vars.mk_true();
        for r_i in 0..regulators.len() {
            let r = regulators[r_i];
            let bdd_var_of_r = state_variables[r.0];
            let r_is_true = valuation[r_i];
            let r_bdd = if r_is_true {
                vars.mk_var(bdd_var_of_r)
            } else {
                vars.mk_not_var(bdd_var_of_r)
            };
            bdd = bdd.and(&r_bdd);
        }
        return bdd;
    }

    /// Create an IdState corresponding to the given valuation of state variables.
    fn extend_valuation_to_id_state(
        valuation: &Vec<bool>,
        regulators: &Vec<VariableId>,
    ) -> IdState {
        let mut state = 0;
        for r_i in 0..regulators.len() {
            if valuation[r_i] {
                let r = regulators[r_i];
                state += (1 as usize).shl(r.0);
            }
        }
        return IdState::from(state);
    }
}

/// Examine the general properties of the graph.
impl SymbolicAsyncGraph {
    /// Return a reference to the original Boolean network.
    pub fn network(&self) -> &BooleanNetwork {
        return &self.network;
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
        return self
            .network
            .make_witness_for_valuation(colors.bdd.sat_witness().unwrap(), &self.function_context);
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
}

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
        let v = self.state_variables[variable.0];
        let apply_function = &self.update_functions[variable.0];
        // This is equivalent to [frontier & ((v_is_one & function_is_zero) | (v_is_zero & function_is_one))]
        let can_perform_step: Bdd = bdd!(frontier & apply_function);
        let after_step_performed = can_perform_step.invert_input(v).and(universe);
        return GraphColoredVertices::new(after_step_performed, self.p_var_count);
    }

    /// Compute vertices in `universe` that have a direct successor under `variable` in that `universe`.
    /// Can be used to compute sinks.
    pub fn has_post(
        &self,
        variable: VariableId,
        universe: &GraphColoredVertices,
    ) -> GraphColoredVertices {
        let universe = &universe.bdd;
        let v = self.state_variables[variable.0];
        let apply_function = &self.update_functions[variable.0];
        let can_do_transition = bdd!(universe & apply_function);
        // This has to be universe and not sink_candidate because that's where we look for successors.
        let after_transition = universe.and(&can_do_transition.invert_input(v));
        return GraphColoredVertices::new(after_transition.invert_input(v), self.p_var_count);
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
        let v = self.state_variables[variable.0];
        let apply_function = &self.update_functions[variable.0];
        let possible_predecessors = frontier.invert_input(v).and(universe);
        let can_perform_step = bdd!(possible_predecessors & apply_function);
        return GraphColoredVertices::new(can_perform_step, self.p_var_count);
    }

    /// Compute vertices in `universe` that have a direct predecessor under `variable` in that `universe`.
    /// Can be used to compute sources.
    pub fn has_pre(
        &self,
        variable: VariableId,
        universe: &GraphColoredVertices,
    ) -> GraphColoredVertices {
        let universe = &universe.bdd;
        let v = self.state_variables[variable.0];
        let apply_function = &self.update_functions[variable.0];
        let possible_predecessors = universe.invert_input(v).and(&universe);
        let can_do_transition = bdd!(possible_predecessors & apply_function);
        return GraphColoredVertices::new(can_do_transition.invert_input(v), self.p_var_count);
    }
}
