use crate::async_graph::{AsyncGraphEdgeParams, DefaultEdgeParams};
use crate::bdd_params::{build_static_constraints, BddParameterEncoder, BddParams};
use crate::biodivine_std::structs::IdState;
use crate::biodivine_std::traits::Params;
use crate::{BooleanNetwork, VariableId};

impl DefaultEdgeParams {
    /// New default edge parametrisation for the given network. Warning: computes the unit set, which can be expensive.
    pub fn new(network: BooleanNetwork) -> Result<DefaultEdgeParams, String> {
        let encoder = BddParameterEncoder::new(&network);
        Self::new_with_custom_encoder(network, encoder)
    }

    pub fn new_with_custom_encoder(
        network: BooleanNetwork,
        encoder: BddParameterEncoder,
    ) -> Result<DefaultEdgeParams, String> {
        let unit_set = BddParams::from(build_static_constraints(&network, &encoder));
        if unit_set.is_empty() {
            Err("No update functions satisfy given constraints".to_string())
        } else {
            Ok(DefaultEdgeParams {
                empty_set: BddParams::from(encoder.bdd_variables.mk_false()),
                network,
                encoder,
                unit_set,
            })
        }
    }
}

impl AsyncGraphEdgeParams for DefaultEdgeParams {
    type ParamSet = BddParams;

    fn network(&self) -> &BooleanNetwork {
        &self.network
    }

    fn empty_params(&self) -> &Self::ParamSet {
        &self.empty_set
    }

    fn unit_params(&self) -> &Self::ParamSet {
        &self.unit_set
    }

    /// Compute the parameter set which enables the value of `variable` to be flipped
    /// in the given `state`.
    ///
    /// Note that this set is not a subset of the `unit_set`! It is really just the flip condition.
    fn edge_params(&self, state: IdState, variable: VariableId) -> BddParams {
        // First, compute the parameter set that sends value of variable to true in this state
        let update_function = &self.network.update_functions[variable.0];
        let edge_params = if let Some(update_function) = update_function {
            update_function.symbolic_eval_true(state, &self.encoder)
        } else {
            let var = self.encoder.get_implicit(state, variable);
            BddParams::from(self.encoder.bdd_variables.mk_var(var))
        };

        // Now if we actually want to go to false, invert the set:
        if state.get_bit(variable.0) {
            BddParams::from(edge_params.into_bdd().not())
        } else {
            edge_params
        }
    }

    fn make_witness(&self, params: &Self::ParamSet) -> BooleanNetwork {
        self.network.make_witness(params, &self.encoder)
    }
}
