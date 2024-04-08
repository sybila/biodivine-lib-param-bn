use crate::biodivine_std::traits::Set;
use crate::symbolic_async_graph::bdd_set::BddSet;
use crate::symbolic_async_graph::projected_iteration::RawProjection;
use crate::symbolic_async_graph::GraphVertices;
use crate::trap_spaces::{NetworkSpaces, SpaceIterator, SymbolicSpaceContext};
use crate::{ExtendedBoolean, Space};
use biodivine_lib_bdd::{Bdd, BddVariable};
use num_bigint::BigInt;

impl NetworkSpaces {
    /// Create a new set of network spaces using a "raw" [Bdd] object w.r.t. the given `context`.
    pub fn new(bdd: Bdd, context: &SymbolicSpaceContext) -> NetworkSpaces {
        NetworkSpaces {
            bdd,
            dual_variables: context.dual_variables.clone(),
        }
    }

    /// Create a new set of network spaces using a "raw" [Bdd] while transferring the context
    /// from this existing set.
    fn copy(&self, bdd: Bdd) -> Self {
        NetworkSpaces {
            bdd,
            dual_variables: self.dual_variables.clone(),
        }
    }

    /// Consume this object and return the underlying raw [Bdd].
    pub fn into_bdd(self) -> Bdd {
        self.bdd
    }

    /// Obtain the reference to the underlying raw [Bdd] of this set.
    pub fn as_bdd(&self) -> &Bdd {
        &self.bdd
    }

    /// Approximate the size of this set using `f64`.
    pub fn approx_cardinality(&self) -> f64 {
        BddSet::approx_cardinality(self)
    }

    /// The exact size of this set (i.e. number of elements).
    pub fn exact_cardinality(&self) -> BigInt {
        BddSet::exact_cardinality(self)
    }

    /// Deterministically pick a single space from this set, and return it as a symbolic
    /// singleton set.
    ///
    /// If this set is empty, returns an empty set.
    pub fn pick_singleton(&self) -> NetworkSpaces {
        if self.is_empty() {
            self.clone()
        } else {
            // Pick one witness valuation from the BDD.
            let witness = self.bdd.sat_witness().unwrap();
            // Retain only the relevant variables.
            let mut partial_valuation = Vec::with_capacity(self.dual_variables.len() * 2);
            for (t_var, f_var) in &self.dual_variables {
                partial_valuation.push((*t_var, witness[*t_var]));
                partial_valuation.push((*f_var, witness[*f_var]));
            }
            self.copy(self.bdd.select(&partial_valuation))
        }
    }

    /// Amount of storage used for this symbolic set.
    pub fn symbolic_size(&self) -> usize {
        BddSet::symbolic_size(self)
    }

    /// Returns true if this set represents a single space.
    pub fn is_singleton(&self) -> bool {
        if !self.bdd.is_clause() {
            return false;
        }
        let clause = self.bdd.first_clause().unwrap();
        for (t_var, f_var) in &self.dual_variables {
            if clause[*t_var].is_none() || clause[*f_var].is_none() {
                return false;
            }
        }
        true
    }

    pub fn raw_projection(&self, eliminate: &[BddVariable]) -> RawProjection {
        let mut retained = Vec::new();
        for (t_var, f_var) in &self.dual_variables {
            if !eliminate.contains(t_var) {
                retained.push(*t_var);
            }
            if !eliminate.contains(f_var) {
                retained.push(*f_var);
            }
        }
        RawProjection::new(retained, &self.bdd)
    }

    /// Returns an iterator over all elements stored in this set.
    ///
    /// In the case of symbolic sets, `iter` and `into_iter` have the same result because
    /// we have to recreate the the items anyway, so there is no true "iterate by reference"
    /// option.
    pub fn iter(&self) -> SpaceIterator {
        let mut variables = Vec::with_capacity(2 * self.dual_variables.len());
        for (t_var, f_var) in &self.dual_variables {
            variables.push(*t_var);
            variables.push(*f_var);
        }
        let projection = RawProjection::new(variables, self.as_bdd());
        SpaceIterator {
            inner_iterator: projection.into_iter(),
            dual_variables: self.dual_variables.clone(),
        }
    }

    /// Produce a set of vertices that are contained within the subspaces represented in this set.
    pub fn to_vertices(&self, ctx: &SymbolicSpaceContext) -> GraphVertices {
        GraphVertices::new(ctx.spaces_to_vertices(self.as_bdd()), ctx.inner_context())
    }
}

impl BddSet for NetworkSpaces {
    fn as_bdd(&self) -> &Bdd {
        &self.bdd
    }

    fn copy(&self, bdd: Bdd) -> Self {
        NetworkSpaces {
            bdd,
            dual_variables: self.dual_variables.clone(),
        }
    }

    fn active_variables(&self) -> u16 {
        u16::try_from(self.dual_variables.len() * 2).unwrap()
    }
}

impl IntoIterator for NetworkSpaces {
    type Item = Space;
    type IntoIter = SpaceIterator;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl Iterator for SpaceIterator {
    type Item = Space;

    fn next(&mut self) -> Option<Self::Item> {
        let valuation = self.inner_iterator.next()?;
        let mut space = Space(vec![ExtendedBoolean::Any; self.dual_variables.len()]);
        for (i, (t_var, f_var)) in self.dual_variables.iter().enumerate() {
            match (valuation[*t_var], valuation[*f_var]) {
                (Some(true), Some(false)) => space.0[i] = ExtendedBoolean::One,
                (Some(false), Some(true)) => space.0[i] = ExtendedBoolean::Zero,
                (Some(true), Some(true)) => space.0[i] = ExtendedBoolean::Any,
                _ => unreachable!(),
            }
        }
        Some(space)
    }
}

#[cfg(test)]
mod tests {
    use crate::trap_spaces::SymbolicSpaceContext;
    use crate::BooleanNetwork;
    use num_bigint::BigInt;
    use num_traits::One;

    #[test]
    fn basic_spaces_set_test() {
        let bn = BooleanNetwork::try_from_file("aeon_models/005.aeon").unwrap();
        let ctx = SymbolicSpaceContext::new(&bn);

        let unit = ctx.mk_unit_spaces();
        assert!(!unit.is_singleton());
        assert_eq!(unit, unit.copy(unit.clone().into_bdd()));

        let singleton = unit.pick_singleton();
        assert_eq!(1.0, singleton.approx_cardinality());
        assert_eq!(BigInt::one(), singleton.exact_cardinality());
        assert_eq!(1, singleton.iter().count());

        // There are 28 network variables and we are eliminating 22 of them, so 6 should be left.
        let dual_vars = ctx.inner_context().all_extra_state_variables();
        let project = unit.raw_projection(&dual_vars[0..44]);
        assert_eq!(project.iter().count(), 3_usize.pow(6));
    }
}
