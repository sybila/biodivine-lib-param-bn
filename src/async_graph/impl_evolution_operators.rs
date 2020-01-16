use crate::async_graph::BwdIterator;
use crate::biodivine_std::IdState;
use crate::bdd_params::BddParams;

impl Iterator for BwdIterator<'_> {
    type Item = (IdState, BddParams);

    fn next(&mut self) -> Option<Self::Item> {
        return if let Some(var) = self.variables.next() {
            let source = self.target.flip_bit(var);
            let edge_params = self.graph.edge_params(source, var);
            Some((source, edge_params.intersect(&self.graph.unit_set)))
        } else {
            None
        };
    }
}