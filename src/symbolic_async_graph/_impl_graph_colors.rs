use crate::biodivine_std::traits::Set;
use crate::symbolic_async_graph::{GraphColors, SymbolicContext};
use biodivine_lib_bdd::{Bdd, BddVariable};
use std::convert::TryFrom;

impl GraphColors {
    /// Make a new color set from a `bdd` and a symbolic `context`.
    pub fn new(bdd: Bdd, context: &SymbolicContext) -> Self {
        GraphColors {
            bdd,
            parameter_variables: context.parameter_variables.clone(),
        }
    }

    /// Make a copy of graph colors with a new `bdd` inheriting the original context.
    pub fn copy(&self, bdd: Bdd) -> Self {
        GraphColors {
            bdd,
            parameter_variables: self.parameter_variables.clone(),
        }
    }

    /// Convert this set to a raw `Bdd`.
    pub fn into_bdd(self) -> Bdd {
        self.bdd
    }

    /// View this set as a raw `Bdd`.
    pub fn as_bdd(&self) -> &Bdd {
        &self.bdd
    }

    /// Pick one color from this set and return it as a singleton.
    ///
    /// If the set is empty, return empty set.
    pub fn pick_singleton(&self) -> GraphColors {
        if self.is_empty() {
            self.clone()
        } else {
            /* This is faster than `bdd.pick` and still correct since state variables are unconstrained. */
            let witness = self.bdd.sat_witness().unwrap();
            let partial_valuation: Vec<(BddVariable, bool)> = self
                .parameter_variables
                .iter()
                .map(|v| (*v, witness[*v]))
                .collect();
            self.copy(self.bdd.select(&partial_valuation))
        }
    }

    /// Approximate size of this set (error grows for large sets).
    pub fn approx_cardinality(&self) -> f64 {
        let state_variable_count =
            self.bdd.num_vars() - u16::try_from(self.parameter_variables.len()).unwrap();
        let state_count = (2.0f64).powi(state_variable_count.into());
        self.bdd.cardinality() / state_count
    }

    /// Amount of storage used for this symbolic set.
    pub fn symbolic_size(&self) -> usize {
        self.bdd.size()
    }

    /// Convert this set to a `.dot` graph.
    pub fn to_dot_string(&self, context: &SymbolicContext) -> String {
        self.bdd.to_dot_string(&context.bdd, true)
    }
}

/// Set operations.
impl Set for GraphColors {
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
