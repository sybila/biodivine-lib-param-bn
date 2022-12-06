use crate::biodivine_std::bitvector::{ArrayBitVector, BitVector};
use crate::biodivine_std::traits::Set;
use crate::symbolic_async_graph::{
    GraphVertexIterator, GraphVertices, IterableVertices, SymbolicContext,
};
use crate::VariableId;
use biodivine_lib_bdd::{Bdd, BddValuation, BddVariable};
use num_bigint::BigInt;
use num_traits::ToPrimitive;
use std::convert::TryFrom;
use std::ops::Shr;

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
        let cardinality = self.bdd.cardinality();
        if cardinality.is_infinite() || cardinality.is_nan() {
            self.exact_cardinality().to_f64().unwrap_or(f64::INFINITY)
        } else {
            let parameter_variable_count =
                self.bdd.num_vars() - u16::try_from(self.state_variables.len()).unwrap();
            let parameter_count = 2.0f64.powi(parameter_variable_count.into());
            cardinality / parameter_count
        }
    }

    /// Compute exact `BigInt` cardinality of this set.
    pub fn exact_cardinality(&self) -> BigInt {
        let parameter_variable_count =
            self.bdd.num_vars() - u16::try_from(self.state_variables.len()).unwrap();
        self.bdd.exact_cardinality().shr(parameter_variable_count)
    }

    /// Pick one vertex from this set and return it as a singleton.
    ///
    /// If the set is empty, return empty set.
    pub fn pick_singleton(&self) -> GraphVertices {
        if self.is_empty() {
            self.clone()
        } else {
            /* This is faster than `bdd.pick` and still correct since state variables are unconstrained. */
            let witness = self.bdd.sat_witness().unwrap();
            let partial_valuation: Vec<(BddVariable, bool)> = self
                .state_variables
                .iter()
                .map(|v| (*v, witness[*v]))
                .collect();
            self.copy(self.bdd.select(&partial_valuation))
        }
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

    /// Amount of storage used for this symbolic set.
    pub fn symbolic_size(&self) -> usize {
        self.bdd.size()
    }

    /// Convert this set to a `.dot` graph.
    pub fn to_dot_string(&self, context: &SymbolicContext) -> String {
        self.bdd.to_dot_string(&context.bdd, true)
    }

    /// Return `true` if the set can be described by a single conjunction of literals. That is,
    /// the set is a hypercube in the $\mathbb{B}^n$ space.
    pub fn is_subspace(&self) -> bool {
        self.bdd.is_clause()
    }

    /// Return `true` if the set represents a single vertex.
    pub fn is_singleton(&self) -> bool {
        if self.bdd.is_clause() {
            let clause = self.bdd.first_clause().unwrap();
            for var in &self.state_variables {
                if clause.get_value(*var).is_none() {
                    return false;
                }
            }
            true
        } else {
            false
        }
    }

    /// Compute a set where the value of the given variable is restricted.
    ///
    /// Restriction operation takes only the elements where `variable=value`, but then makes
    /// the result independent on this variable by erasing it. This is useful when you
    /// are computing various operations on subspaces.
    pub fn restrict_network_variable(&self, variable: VariableId, value: bool) -> Self {
        let var = self.state_variables[variable.0];
        self.copy(self.bdd.var_restrict(var, value))
    }

    /// Compute a subset of this set where the given network variable is always fixed to the
    /// given value.
    pub fn fix_network_variable(&self, variable: VariableId, value: bool) -> Self {
        let var = self.state_variables[variable.0];
        self.copy(self.bdd.var_select(var, value))
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
        if let Some(valuation) = self.iterator.next() {
            let mut state = ArrayBitVector::empty(self.state_variables.len());
            for (i, v) in self.state_variables.iter().enumerate() {
                if valuation[*v] {
                    state.flip(i);
                }
            }
            Some(state)
        } else {
            None
        }
    }
}

/* Set operations */
impl Set for GraphVertices {
    fn union(&self, other: &Self) -> Self {
        self.copy(self.bdd.or(&other.bdd))
    }

    fn intersect(&self, other: &Self) -> Self {
        self.copy(self.bdd.and(&other.bdd))
    }

    fn minus(&self, other: &Self) -> Self {
        self.copy(self.bdd.and_not(&other.bdd))
    }

    fn is_empty(&self) -> bool {
        self.bdd.is_false()
    }

    fn is_subset(&self, other: &Self) -> bool {
        self.bdd.and_not(&other.bdd).is_false()
    }
}
