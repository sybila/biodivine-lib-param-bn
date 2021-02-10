use crate::async_graph::{AsyncGraph, AsyncGraphEdgeParams, DefaultEdgeParams};
use crate::BooleanNetwork;

impl AsyncGraph<DefaultEdgeParams> {
    /// Create a new `AsyncGraph` from the given `BooleanNetwork` using default edge parameter implementation.
    pub fn new(network: BooleanNetwork) -> Result<AsyncGraph<DefaultEdgeParams>, String> {
        if network.graph.num_vars() > 32 {
            Err("Can't create the graph. At most 32 variables supported".to_string())
        } else {
            let edge_params = DefaultEdgeParams::new(network)?;
            Ok(AsyncGraph { edges: edge_params })
        }
    }
}

impl<Params: AsyncGraphEdgeParams> AsyncGraph<Params> {
    /// Create a new `AsyncGraph` using given edge parametrisation.
    pub fn new_with_edges(edge_params: Params) -> Result<AsyncGraph<Params>, String> {
        return if edge_params.network().graph.num_vars() > 32 {
            Err("Can't create the graph. At most 32 variables supported".to_string())
        } else {
            Ok(AsyncGraph { edges: edge_params })
        };
    }

    /// Return the total number of states in this graph.
    pub fn num_states(&self) -> usize {
        1 << self.network().graph.num_vars()
    }

    /// Return a reference to the original Boolean network.
    pub fn network(&self) -> &BooleanNetwork {
        self.edges.network()
    }

    /// Expose the inner edge implementation.
    pub fn edges(&self) -> &Params {
        return &self.edges;
    }

    /// Make a witness network for one parametrisation in the given set.
    pub fn make_witness(&self, params: &Params::ParamSet) -> BooleanNetwork {
        self.edges.make_witness(params)
    }

    /// Return an empty set of parameters.
    pub fn empty_params(&self) -> &Params::ParamSet {
        self.edges.empty_params()
    }

    /// Return a full set of parameters.
    pub fn unit_params(&self) -> &Params::ParamSet {
        self.edges.unit_params()
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
        assert_eq!(9.0, graph.unit_params().cardinality());
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
        assert_eq!(8.0, graph.unit_params().cardinality());
    }
}
