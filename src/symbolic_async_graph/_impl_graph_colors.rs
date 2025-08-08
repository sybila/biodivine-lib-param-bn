use crate::VariableId;
use crate::biodivine_std::traits::Set;
use crate::symbolic_async_graph::bdd_set::BddSet;
use crate::symbolic_async_graph::projected_iteration::{FnUpdateProjection, RawProjection};
use crate::symbolic_async_graph::{GraphColors, SymbolicAsyncGraph, SymbolicContext};
use biodivine_lib_bdd::{Bdd, BddVariable};
use num_bigint::BigInt;
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
        BddSet::approx_cardinality(self)
    }

    /// Compute exact `BigInt` cardinality of this set.
    pub fn exact_cardinality(&self) -> BigInt {
        BddSet::exact_cardinality(self)
    }

    /// Amount of storage used for this symbolic set.
    pub fn symbolic_size(&self) -> usize {
        BddSet::symbolic_size(self)
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

    /// Return `true` if the set represents a single color.
    pub fn is_singleton(&self) -> bool {
        if self.bdd.is_clause() {
            let clause = self.bdd.first_clause().unwrap();
            for var in &self.parameter_variables {
                if clause.get_value(*var).is_none() {
                    return false;
                }
            }
            true
        } else {
            false
        }
    }

    /// Perform a "raw projection" which eliminates the given symbolic variables from this set.
    ///
    /// Technically, you can supply any `BddVariable`, but the underlying `Bdd` of this set
    /// should only depend on *parameter variables*.
    pub fn raw_projection(&self, eliminate: &[BddVariable]) -> RawProjection {
        let mut retained = Vec::new();
        for v in &self.parameter_variables {
            if !eliminate.contains(v) {
                retained.push(*v);
            }
        }
        RawProjection::new(retained, &self.bdd)
    }

    /// Create an iterable symbolic projection which only retains the update functions of the
    /// specified network variables.
    pub fn fn_update_projection<'a>(
        &self,
        functions: &[VariableId],
        context: &'a SymbolicAsyncGraph,
    ) -> FnUpdateProjection<'a> {
        FnUpdateProjection::new(functions.to_vec(), context, &self.bdd)
    }
}

impl BddSet for GraphColors {
    fn as_bdd(&self) -> &Bdd {
        GraphColors::as_bdd(self)
    }

    fn copy(&self, bdd: Bdd) -> Self {
        GraphColors::copy(self, bdd)
    }

    fn active_variables(&self) -> u16 {
        u16::try_from(self.parameter_variables.len()).unwrap()
    }
}
