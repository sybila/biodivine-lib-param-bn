use crate::async_graph::{AsyncGraphEdgeParams, Bwd, BwdIterator, Fwd, FwdIterator};
use crate::biodivine_std::structs::IdState;
use crate::biodivine_std::traits::{EvolutionOperator, InvertibleEvolutionOperator};

impl<'a, Params: AsyncGraphEdgeParams> EvolutionOperator for Fwd<'a, Params> {
    type State = IdState;
    type Params = Params::ParamSet;
    type Iterator = FwdIterator<'a, Params>;

    fn step(&self, current: IdState) -> Self::Iterator {
        return FwdIterator {
            graph: self.graph,
            variables: self.graph.network().graph.variable_ids(),
            state: current,
        };
    }
}

impl<'a, Params: AsyncGraphEdgeParams> InvertibleEvolutionOperator for Fwd<'a, Params> {
    type InvertedOperator = Bwd<'a, Params>;

    fn invert(&self) -> Self::InvertedOperator {
        return Bwd { graph: self.graph };
    }
}

impl<Params: AsyncGraphEdgeParams> Iterator for FwdIterator<'_, Params> {
    type Item = (IdState, Params::ParamSet);

    fn next(&mut self) -> Option<Self::Item> {
        return if let Some(var) = self.variables.next() {
            let target = self.state.flip_bit(var.0);
            let edge_params = self.graph.edges.edge_params(self.state, var);
            Some((target, edge_params))
        } else {
            None
        };
    }
}

impl<'a, Params: AsyncGraphEdgeParams> EvolutionOperator for Bwd<'a, Params> {
    type State = IdState;
    type Params = Params::ParamSet;
    type Iterator = BwdIterator<'a, Params>;

    fn step(&self, current: IdState) -> Self::Iterator {
        return BwdIterator {
            graph: self.graph,
            variables: self.graph.network().graph.variable_ids(),
            state: current,
        };
    }
}

impl<'a, Params: AsyncGraphEdgeParams> InvertibleEvolutionOperator for Bwd<'a, Params> {
    type InvertedOperator = Fwd<'a, Params>;

    fn invert(&self) -> Self::InvertedOperator {
        return Fwd { graph: self.graph };
    }
}

impl<Params: AsyncGraphEdgeParams> Iterator for BwdIterator<'_, Params> {
    type Item = (IdState, Params::ParamSet);

    fn next(&mut self) -> Option<Self::Item> {
        return if let Some(var) = self.variables.next() {
            let source = self.state.flip_bit(var.0);
            let edge_params = self.graph.edges.edge_params(source, var);
            Some((source, edge_params))
        } else {
            None
        };
    }
}

#[cfg(test)]
mod tests {
    use crate::async_graph::AsyncGraph;
    use crate::bdd_params::BddParams;
    use crate::biodivine_std::structs::IdState;
    use crate::biodivine_std::traits::{EvolutionOperator, Graph, Params};
    use crate::BooleanNetwork;
    use std::collections::HashSet;
    use std::convert::TryFrom;

    #[test]
    fn test_no_param_network() {
        let network = BooleanNetwork::try_from(
            "
            a -> b
            a -> a
            b -| a
            b -| b
            $a: a & !b
            $b: a | !b
        ",
        )
        .unwrap();
        let graph = &AsyncGraph::new(network).unwrap();

        let edges: HashSet<(IdState, IdState)> = vec![
            (IdState::from(0b00), IdState::from(0b10)),
            (IdState::from(0b10), IdState::from(0b00)),
            (IdState::from(0b00), IdState::from(0b10)),
            (IdState::from(0b01), IdState::from(0b11)),
            (IdState::from(0b11), IdState::from(0b10)),
        ]
        .into_iter()
        .collect();

        let fwd = graph.fwd();
        let bwd = graph.bwd();

        for s in graph.states() {
            for (t, p) in fwd.step(s) {
                assert_eq!(
                    !p.is_empty(),
                    edges.contains(&(s, t)),
                    "Edge ({:?},{:?})",
                    s,
                    t
                );
            }
            for (t, p) in bwd.step(s) {
                assert_eq!(
                    !p.is_empty(),
                    edges.contains(&(t, s)),
                    "Edge ({:?},{:?})",
                    t,
                    s
                );
            }
        }
    }

    #[test]
    fn test_anonymous_param_network() {
        let network = BooleanNetwork::try_from(
            "
            a ->? b
            a -> a
            b -|? a
            b -| b
        ",
        )
        .unwrap();
        let graph = &AsyncGraph::new(network).unwrap();
        let fwd = graph.fwd();
        let bwd = graph.bwd();

        let edges: HashSet<(IdState, IdState, i32)> = vec![
            (IdState::from(0b00), IdState::from(0b10), 2 * 3),
            (IdState::from(0b10), IdState::from(0b00), 3 * 3),
            (IdState::from(0b00), IdState::from(0b01), 1 * 3),
            (IdState::from(0b11), IdState::from(0b10), 1 * 3),
            (IdState::from(0b01), IdState::from(0b11), 3 * 3),
            (IdState::from(0b11), IdState::from(0b01), 2 * 3),
        ]
        .into_iter()
        .collect();

        assert_eq!(9.0, graph.unit_params().cardinality());

        let mut fwd_edges: HashSet<(IdState, IdState, BddParams)> = HashSet::new();
        let mut bwd_edges: HashSet<(IdState, IdState, BddParams)> = HashSet::new();

        for s in graph.states() {
            let successors = fwd.step(s);
            for (t, p) in successors {
                let p = p.intersect(graph.unit_params());
                if p.cardinality() > 0.0 {
                    assert!(edges.contains(&(s, t, p.cardinality() as i32)));
                }
                fwd_edges.insert((s, t, p));
            }
            for (t, p) in bwd.step(s) {
                let p = p.intersect(graph.unit_params());
                if p.cardinality() > 0.0 {
                    assert!(edges.contains(&(t, s, p.cardinality() as i32)));
                }
                bwd_edges.insert((t, s, p));
            }
        }

        assert_eq!(fwd_edges, bwd_edges)
    }
}
