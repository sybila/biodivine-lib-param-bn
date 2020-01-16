use crate::async_graph::AsyncGraph;
use crate::bdd_params::{build_static_constraints, BddParameterEncoder, BddParams};
use crate::biodivine_std::param::Params;
use crate::biodivine_std::IdState;
use crate::{BooleanNetwork, VariableId};

impl AsyncGraph {
    /// Create a new `AsyncGraph` from the given `BooleanNetwork`.
    pub fn new(network: BooleanNetwork) -> Result<AsyncGraph, String> {
        return if network.graph.num_vars() > 32 {
            Err("Can't create the graph. At most 32 variables supported".to_string())
        } else {
            let encoder = BddParameterEncoder::new(&network);
            let unit_set = BddParams::from(build_static_constraints(&network, &encoder));
            if unit_set.is_empty() {
                Err("No update functions satisfy given constraints".to_string())
            } else {
                Ok(AsyncGraph {
                    network,
                    encoder,
                    unit_set,
                })
            }
        };
    }

    /// Return the total number of states in this graph.
    pub fn num_states(&self) -> usize {
        return 1 << self.network.graph.num_vars();
    }

    /// Return an empty parameter set.
    pub fn empty_params(&self) -> BddParams {
        return BddParams::from(self.encoder.bdd_variables.mk_false());
    }

    /// Return a unit parameter set, i.e. all parameters that satisfy all static conditions.
    pub fn unit_params(&self) -> &BddParams {
        return &self.unit_set;
    }

    /// Compute the parameter set which enables the value of `variable` to be flipped
    /// in the given `state`.
    ///
    /// Note that this set is not a subset of the `unit_set`! It is really just the flip condition.
    pub fn edge_params(&self, state: IdState, variable: VariableId) -> BddParams {
        // First, compute the parameter set that sends value of variable to true in this state
        let update_function = &self.network.update_functions[variable.0];
        let edge_params = if let Some(update_function) = update_function {
            update_function.symbolic_eval_true(state, &self.encoder)
        } else {
            let var = self.encoder.get_implicit(state, variable);
            BddParams::from(self.encoder.bdd_variables.mk_var(var))
        };

        // Now if we actually want to go to false, invert the set:
        return if state.get_bit(variable.0) {
            BddParams::from(edge_params.into_bdd().not())
        } else {
            edge_params
        };
    }
}

#[cfg(test)]
mod tests {
    use crate::async_graph::AsyncGraph;
    use crate::BooleanNetwork;
    use std::convert::TryFrom;

    #[test]
    fn test_graph_unit_set_anonymous_params() {
        let network = BooleanNetwork::try_from(
            "
            a ->? b
            a -> a
            b -| b
            b -|? a
        ",
        )
        .unwrap();
        let graph = AsyncGraph::new(network).unwrap();
        // both functions can have 3 different valuations, so 9 in total
        assert_eq!(9.0, graph.unit_set.cardinality());
    }

    #[test]
    fn test_graph_unit_set_names_params() {
        let network = BooleanNetwork::try_from(
            "
            a ->? b
            a -> a
            b -| b
            b -|? a
            $a: a | p(b)
            $b: q(a, b) & a
        ",
        )
        .unwrap();
        let graph = AsyncGraph::new(network).unwrap();
        // p can have 2 valuations, q can have 4, 8 in total
        // actually, for b, there is only one possible function but it is achieved
        // regardless of two values of q.
        assert_eq!(8.0, graph.unit_set.cardinality());
    }
}
