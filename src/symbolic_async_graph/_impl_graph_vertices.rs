use crate::biodivine_std::bitvector::{ArrayBitVector, BitVector};
use crate::symbolic_async_graph::{
    GraphVertexIterator, GraphVertices, IterableVertices, SymbolicContext,
};
use biodivine_lib_bdd::{Bdd, BddValuation};
use std::convert::TryFrom;

impl GraphVertices {
    /// Create a new set of vertices using the given `Bdd` and a symbolic `context`.
    pub fn new(bdd: Bdd, context: &SymbolicContext) -> Self {
        GraphVertices {
            bdd,
            state_variables: context.state_variables.clone(),
        }
    }

    /// Copy the context of this vertex set, but using a new `bdd`.
    pub fn copy(&self, bdd: Bdd) -> Self {
        GraphVertices {
            bdd,
            state_variables: self.state_variables.clone(),
        }
    }

    /// Convert this vertex set into a raw `Bdd`.
    pub fn into_bdd(self) -> Bdd {
        self.bdd
    }

    /// View this vertex set as a raw `Bdd`.
    pub fn as_bdd(&self) -> &Bdd {
        &self.bdd
    }

    /// Approximate size of this set (error grows for large sets).
    pub fn approx_cardinality(&self) -> f64 {
        let parameter_variable_count =
            self.bdd.num_vars() - u16::try_from(self.state_variables.len()).unwrap();
        let parameter_count = 2.0f64.powi(parameter_variable_count.into());
        self.bdd.cardinality() / parameter_count
    }

    /// Create an iterable view of this vertex set.
    ///
    /// Note that sadly you have to use `set.materialize().iter()` to actually iterate over
    /// the vertices, since we are not moving our the value of this set.
    pub fn materialize(&self) -> IterableVertices {
        // This is a colossal hack, but it is easier than trying to drag parameter variables into this.
        let all_false: Bdd = BddValuation::all_false(self.bdd.num_vars()).into();
        let parameters_false = all_false.project(&self.state_variables);
        IterableVertices {
            materialized_bdd: self.bdd.and(&parameters_false),
            state_variables: self.state_variables.clone(),
        }
    }
}

impl IterableVertices {
    /// Turn this materialized vertex set into an actual iterator.
    pub fn iter(&self) -> GraphVertexIterator {
        return GraphVertexIterator {
            iterator: self.materialized_bdd.sat_valuations(),
            state_variables: self.state_variables.clone(),
        };
    }
}

/// Iterate over vertices using `GraphVertexIterator`.
impl Iterator for GraphVertexIterator<'_> {
    type Item = ArrayBitVector;

    fn next(&mut self) -> Option<Self::Item> {
        return if let Some(valuation) = self.iterator.next() {
            let mut state = ArrayBitVector::empty(self.state_variables.len());
            for (i, v) in self.state_variables.iter().enumerate() {
                if valuation[*v] {
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
        self.copy(self.bdd.or(&other.bdd))
    }

    pub fn intersect(&self, other: &Self) -> Self {
        self.copy(self.bdd.and(&other.bdd))
    }

    pub fn minus(&self, other: &Self) -> Self {
        self.copy(self.bdd.and_not(&other.bdd))
    }

    pub fn is_empty(&self) -> bool {
        self.bdd.is_false()
    }

    pub fn is_subset(&self, other: &Self) -> bool {
        self.bdd.and_not(&other.bdd).is_false()
    }
}
