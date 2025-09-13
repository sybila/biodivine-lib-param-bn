use crate::biodivine_std::traits::Set;
use biodivine_lib_bdd::Bdd;
use num_bigint::BigUint;
use num_traits::ToPrimitive;
use std::ops::Shr;

/// A simple trait that is implemented by symbolic sets represented using `Bdd` objects.
///
/// Historically, many of these methods were implemented directly by the actual objects
/// (and are still implemented for compatibility reasons). However, they can also be implemented
/// by this "blanket" implementation which might be easier to use, as we don't need to
/// reimplement each method for every type.
pub trait BddSet {
    /// A reference to the underlying `Bdd`.
    fn as_bdd(&self) -> &Bdd;
    /// Make a copy of this set but use a completely new BDD instead. This is very much
    /// unsafe, so make sure to only use it with the "right" BDDs.
    fn copy(&self, bdd: Bdd) -> Self;

    /// The number of BDD variables that are actually used by this encoding (they don't have
    /// to appear in the actual BDD, they just theoretically appear in the encoding).
    fn active_variables(&self) -> u16;

    /// Compute the number of BDD nodes required to represent this set.
    fn symbolic_size(&self) -> usize {
        self.as_bdd().size()
    }

    /// Compute the exact cardinality of this symbolic set.
    fn exact_cardinality(&self) -> BigUint {
        let unused_variables = self.as_bdd().num_vars() - self.active_variables();
        self.as_bdd().exact_cardinality().shr(unused_variables)
    }

    /// Compute an "approximate" cardinality of this symbolic set.
    ///
    /// The value is approximate because the limitations of `f64` can apply during computation.
    fn approx_cardinality(&self) -> f64 {
        let cardinality = self.as_bdd().cardinality();
        let unused_variables = self.as_bdd().num_vars() - self.active_variables();
        let cardinality = cardinality / 2.0f64.powi(i32::from(unused_variables));
        if cardinality.is_nan() || cardinality.is_infinite() {
            // If the result is invalid, try to recompute it with
            // better precision.
            self.exact_cardinality().to_f64().unwrap_or(f64::INFINITY)
        } else {
            cardinality
        }
    }
}

impl<T: BddSet + Clone> Set for T {
    fn union(&self, other: &Self) -> Self {
        self.copy(self.as_bdd().or(other.as_bdd()))
    }

    fn intersect(&self, other: &Self) -> Self {
        self.copy(self.as_bdd().and(other.as_bdd()))
    }

    fn minus(&self, other: &Self) -> Self {
        self.copy(self.as_bdd().and_not(other.as_bdd()))
    }

    fn is_empty(&self) -> bool {
        self.as_bdd().is_false()
    }

    fn is_subset(&self, other: &Self) -> bool {
        /*
           If A is a subset of B, then (A and not B) is `false` (everything that is in A is in B).
           The following operation can only return a `false` BDD (due to the limit argument).
           Any other result will terminate early and be returned as `None`.
        */
        Bdd::binary_op_with_limit(
            1,
            self.as_bdd(),
            other.as_bdd(),
            biodivine_lib_bdd::op_function::and_not,
        )
        .is_some()
    }
}
