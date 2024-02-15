use crate::biodivine_std::traits::Set;
use crate::symbolic_async_graph::bdd_set::BddSet;
use crate::symbolic_async_graph::projected_iteration::{FnUpdateProjection, RawProjection};
use crate::symbolic_async_graph::{GraphColoredVertices, GraphColors, SymbolicAsyncGraph};
use crate::trap_spaces::{NetworkColoredSpaces, NetworkSpaces, SymbolicSpaceContext};
use crate::VariableId;
use biodivine_lib_bdd::{Bdd, BddVariable};
use num_bigint::BigInt;

impl NetworkColoredSpaces {
    /// Construct a new [NetworkColoredSpaces] from a raw [Bdd] and a [SymbolicSpaceContext].
    pub fn new(bdd: Bdd, context: &SymbolicSpaceContext) -> NetworkColoredSpaces {
        NetworkColoredSpaces {
            bdd,
            parameter_variables: context.inner_context().parameter_variables().clone(),
            dual_variables: context.dual_variables.clone(),
        }
    }

    /// Construct a new [NetworkColoredSpaces] by copying the context of the current set.
    ///
    /// The contents of the set are completely replaced using the provided [Bdd], but the
    /// underlying [SymbolicSpaceContext] remains the same.
    pub fn copy(&self, bdd: Bdd) -> NetworkColoredSpaces {
        BddSet::copy(self, bdd)
    }

    /// Convert this set to a raw [Bdd].
    pub fn into_bdd(self) -> Bdd {
        self.bdd
    }

    /// View this set as a raw [Bdd].
    pub fn as_bdd(&self) -> &Bdd {
        BddSet::as_bdd(self)
    }

    /// Amount of storage used for this symbolic set.
    pub fn symbolic_size(&self) -> usize {
        BddSet::symbolic_size(self)
    }

    /// Approximate size of this set (error grows for large sets).
    pub fn approx_cardinality(&self) -> f64 {
        BddSet::approx_cardinality(self)
    }

    /// Compute exact `BigInt` cardinality of this set.
    pub fn exact_cardinality(&self) -> BigInt {
        BddSet::exact_cardinality(self)
    }

    /// Return `true` if the set represents a single space-color pair.
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
        for p_var in &self.parameter_variables {
            if clause[*p_var].is_none() {
                return false;
            }
        }
        true
    }

    /// Perform a "raw projection" which eliminates the given symbolic variables from this set.
    ///
    /// Technically, you can supply any `BddVariable`, but the underlying `Bdd` of this set
    /// should only depend on the *state and parameter variables* (i.e. not on any extra state
    /// variables).
    pub fn raw_projection(&self, eliminate: &[BddVariable]) -> RawProjection {
        let mut retained = Vec::new();
        for p_var in &self.parameter_variables {
            if !eliminate.contains(p_var) {
                retained.push(*p_var);
            }
        }
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

    /// Create an iterable symbolic projection which only retains the update functions
    /// of the specified network variables.
    pub fn fn_update_projection<'a>(
        &self,
        functions: &[VariableId],
        context: &'a SymbolicAsyncGraph,
    ) -> FnUpdateProjection<'a> {
        FnUpdateProjection::new(functions.to_vec(), context, &self.bdd)
    }

    fn space_variables(&self) -> Vec<BddVariable> {
        let mut variables = Vec::new();
        for (t_var, f_var) in &self.dual_variables {
            variables.push(*t_var);
            variables.push(*f_var);
        }
        variables
    }

    /// Produce a set of colored vertices that are contained within the subspaces
    /// represented in this set.
    pub fn to_colored_vertices(&self, ctx: &SymbolicSpaceContext) -> GraphColoredVertices {
        GraphColoredVertices::new(ctx.spaces_to_vertices(self.as_bdd()), ctx.inner_context())
    }
}

/// Relation operations.
impl NetworkColoredSpaces {
    /// Remove every occurrence of a color form `colors` set.
    pub fn minus_colors(&self, colors: &GraphColors) -> Self {
        self.copy(self.bdd.and_not(colors.as_bdd()))
    }

    /// Only retain colours in the supplied `colors` set.
    pub fn intersect_colors(&self, colors: &GraphColors) -> Self {
        self.copy(self.bdd.and(colors.as_bdd()))
    }

    /// Remove every occurrence of a space from the `spaces` set, regardless of color.
    pub fn minus_spaces(&self, spaces: &NetworkSpaces) -> Self {
        self.copy(self.bdd.and_not(&spaces.bdd))
    }

    /// Retain only occurrences of vertices from the `spaces` set, regardless of color.
    pub fn intersect_spaces(&self, spaces: &NetworkSpaces) -> Self {
        self.copy(self.bdd.and(&spaces.bdd))
    }

    /// For every color, pick exactly one space.
    pub fn pick_space(&self) -> Self {
        let variables = self.space_variables();
        self.copy(self.bdd.pick(&variables))
    }

    /// For every vertex, pick exactly one color.
    pub fn pick_color(&self) -> Self {
        self.copy(self.bdd.pick(&self.parameter_variables))
    }

    /// Pick one (space, color) pair from this set and return it as a singleton.
    ///
    /// If the set is empty, return empty set.
    pub fn pick_singleton(&self) -> NetworkColoredSpaces {
        if self.is_empty() {
            self.clone()
        } else {
            let witness = self.bdd.sat_witness().unwrap();
            // Retain only the relevant variables.
            let mut partial_valuation = Vec::new();
            for (t_var, f_var) in &self.dual_variables {
                partial_valuation.push((*t_var, witness[*t_var]));
                partial_valuation.push((*f_var, witness[*f_var]));
            }
            for p_var in &self.parameter_variables {
                partial_valuation.push((*p_var, witness[*p_var]));
            }
            self.copy(self.bdd.select(&partial_valuation))
        }
    }

    /// Set of all colors which are in this set for at least one vertex.
    pub fn colors(&self) -> GraphColors {
        let variables = self.space_variables();
        GraphColors {
            bdd: self.bdd.exists(&variables),
            parameter_variables: self.parameter_variables.clone(),
        }
    }

    /// Set of all spaces which are in this set for at least one colour.
    pub fn spaces(&self) -> NetworkSpaces {
        NetworkSpaces {
            bdd: self.bdd.exists(&self.parameter_variables),
            dual_variables: self.dual_variables.clone(),
        }
    }
}

impl BddSet for NetworkColoredSpaces {
    fn as_bdd(&self) -> &Bdd {
        &self.bdd
    }

    fn copy(&self, bdd: Bdd) -> Self {
        NetworkColoredSpaces {
            bdd,
            dual_variables: self.dual_variables.clone(),
            parameter_variables: self.parameter_variables.clone(),
        }
    }

    fn active_variables(&self) -> u16 {
        let x = self.dual_variables.len() * 2 + self.parameter_variables.len();
        u16::try_from(x).unwrap()
    }
}

#[cfg(test)]
mod tests {
    use crate::biodivine_std::traits::Set;
    use crate::symbolic_async_graph::SymbolicAsyncGraph;
    use crate::trap_spaces::SymbolicSpaceContext;
    use crate::BooleanNetwork;
    use num_bigint::BigInt;
    use num_traits::One;

    #[test]
    fn basic_colored_spaces_set_test() {
        let bn = BooleanNetwork::try_from_file("aeon_models/005.aeon").unwrap();
        let ctx = SymbolicSpaceContext::new(&bn);
        let stg = SymbolicAsyncGraph::with_space_context(&bn, &ctx).unwrap();

        let unit = ctx.mk_unit_colored_spaces(&stg);
        assert!(!unit.is_singleton());
        assert_eq!(unit, unit.copy(unit.clone().into_bdd()));

        let singleton = unit.pick_singleton();
        assert_eq!(1.0, singleton.approx_cardinality());
        assert_eq!(BigInt::one(), singleton.exact_cardinality());
        let singleton_color = singleton.colors();
        let singleton_space = singleton.spaces();
        assert!(singleton_color.is_singleton());
        assert!(singleton_space.is_singleton());
        assert!(!unit.intersect_colors(&singleton_color).is_singleton());
        // There is only one color, hence this holds. Otherwise this should not hold.
        assert!(unit.intersect_spaces(&singleton_space).is_singleton());
        assert!(unit.minus_colors(&singleton_color).is_empty());
        assert!(unit.minus_spaces(&singleton_space).is_subset(&unit));

        // There are 28 network variables and we are eliminating 22 of them, so 6 should be left.
        let dual_vars = ctx.inner_context().all_extra_state_variables();
        let project = unit.raw_projection(&dual_vars[0..44]);
        assert_eq!(project.iter().count(), 3_usize.pow(6));
    }
}
