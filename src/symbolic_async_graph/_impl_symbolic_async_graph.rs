use crate::bdd_params::{build_static_constraints, BddParameterEncoder};
use crate::symbolic_async_graph::SymbolicAsyncGraph;
use crate::{BooleanNetwork, FnUpdate, VariableId};
use biodivine_lib_bdd::{
    bdd, Bdd, BddValuationIterator, BddVariable, BddVariableSet, BddVariableSetBuilder,
};
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

        return SymbolicAsyncGraph {
            p_var_count: bdd_variable_set.num_vars() - network.graph.num_vars() as u16,
            empty_set: bdd_variable_set.mk_false(),
            unit_set: build_static_constraints(&network, &function_context),
            update_functions: function_cache,
            network,
            bdd_variable_set,
            state_variables,
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
