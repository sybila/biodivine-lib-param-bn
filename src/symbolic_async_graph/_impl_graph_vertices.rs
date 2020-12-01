use crate::symbolic_async_graph::{GraphVertexIterator, GraphVertices, SymbolicAsyncGraph};
use biodivine_lib_bdd::Bdd;
use biodivine_lib_std::collections::bitvectors::{ArrayBitVector, BitVector};

impl GraphVertices {
    pub fn new(bdd: Bdd, p_var_count: u16) -> GraphVertices {
        return GraphVertices { bdd, p_var_count };
    }

    pub fn into_bdd(self) -> Bdd {
        return self.bdd;
    }

    pub fn as_bdd(&self) -> &Bdd {
        return &self.bdd;
    }

    pub fn cardinality(&self) -> f64 {
        let parameters = (2.0f64).powi(self.p_var_count as i32);
        return self.bdd.cardinality() / parameters;
    }

    pub fn states<'a, 'b>(&'b self, graph: &'a SymbolicAsyncGraph) -> GraphVertexIterator<'a, 'b> {
        return GraphVertexIterator {
            state_variables: &graph.symbolic_context.state_variables,
            iterator: self.bdd.sat_valuations(),
        };
    }
}

impl Iterator for GraphVertexIterator<'_, '_> {
    type Item = ArrayBitVector;

    fn next(&mut self) -> Option<Self::Item> {
        return if let Some(valuation) = self.iterator.next() {
            let mut state = ArrayBitVector::empty(self.state_variables.len());
            for (i, v) in self.state_variables.iter().enumerate() {
                if valuation.value(*v) {
                    state.flip(i);
                }
            }
            Some(state)
        } else {
            None
        };
    }
}

/* Set operations */
impl GraphVertices {
    pub fn union(&self, other: &Self) -> Self {
        return Self::new(self.bdd.or(&other.bdd), self.p_var_count);
    }

    pub fn intersect(&self, other: &Self) -> Self {
        return Self::new(self.bdd.and(&other.bdd), self.p_var_count);
    }

    pub fn minus(&self, other: &Self) -> Self {
        return Self::new(self.bdd.and_not(&other.bdd), self.p_var_count);
    }

    pub fn is_empty(&self) -> bool {
        return self.bdd.is_false();
    }

    pub fn is_subset(&self, other: &Self) -> bool {
        return self.bdd.and_not(&other.bdd).is_false();
    }
}
