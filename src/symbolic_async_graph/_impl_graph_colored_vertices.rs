use crate::biodivine_std::traits::Set;
use crate::symbolic_async_graph::bdd_set::BddSet;
use crate::symbolic_async_graph::projected_iteration::{
    FnUpdateProjection, MixedProjection, RawProjection, StateProjection,
};
use crate::symbolic_async_graph::{
    GraphColoredVertices, GraphColors, GraphVertices, SymbolicAsyncGraph, SymbolicContext,
};
use crate::VariableId;
use biodivine_lib_bdd::{Bdd, BddVariable};
use num_bigint::BigInt;

/// Basic utility operations.
impl GraphColoredVertices {
    /// Construct a new colored vertex set from a given `bdd` and symbolic `context`.
    pub fn new(bdd: Bdd, context: &SymbolicContext) -> GraphColoredVertices {
        GraphColoredVertices {
            bdd,
            state_variables: context.state_variables.clone(),
            parameter_variables: context.parameter_variables.clone(),
        }
    }

    /// Construct a new colored vertex set by copying the context of the current set.
    ///
    /// The contents of the set are completely replaced using the provided `bdd`, but the
    /// underlying `SymbolicAsyncGraph` remains the same.
    pub fn copy(&self, bdd: Bdd) -> GraphColoredVertices {
        GraphColoredVertices {
            bdd,
            state_variables: self.state_variables.clone(),
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

    /// Convert this set to a `.dot` graph.
    pub fn to_dot_string(&self, context: &SymbolicContext) -> String {
        self.bdd.to_dot_string(&context.bdd, true)
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

    /// Return `true` if the set can be described by a single conjunction of literals. That is,
    /// the set is a hypercube in the $\mathbb{B}^n$ space.
    pub fn is_subspace(&self) -> bool {
        self.bdd.is_clause()
    }

    /// Return `true` if the set represents a single vertex-color pair.
    pub fn is_singleton(&self) -> bool {
        if self.bdd.is_clause() {
            let clause = self.bdd.first_clause().unwrap();
            for var in &self.state_variables {
                if clause[*var].is_none() {
                    return false;
                }
            }
            for var in &self.parameter_variables {
                if clause[*var].is_none() {
                    return false;
                }
            }
            true
        } else {
            false
        }
    }

    /// Compute a subset of this set where the given network variable is always fixed to the
    /// given value.
    pub fn fix_network_variable(&self, variable: VariableId, value: bool) -> Self {
        let var = self.state_variables[variable.0];
        self.copy(self.bdd.var_select(var, value))
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

    /// Perform a "raw projection" which eliminates the given symbolic variables from this set.
    ///
    /// Technically, you can supply any `BddVariable`, but the underlying `Bdd` of this set
    /// should only depend on *state and parameter variables* (i.e. not on extra state variables).
    pub fn raw_projection(&self, variables: &[BddVariable]) -> RawProjection {
        let mut retained = Vec::new();
        for v in &self.state_variables {
            if !variables.contains(v) {
                retained.push(*v);
            }
        }
        for v in &self.parameter_variables {
            if !variables.contains(v) {
                retained.push(*v);
            }
        }
        RawProjection::new(retained, &self.bdd)
    }

    /// Create an iterable symbolic projection which only retains the specified network variables.
    pub fn state_projection(&self, variables: &[VariableId]) -> StateProjection {
        StateProjection::new(variables.to_vec(), &self.state_variables, &self.bdd)
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

    /// Create an iterable symbolic projection which only retains the specified network variables
    /// and the update functions of the specified variables.
    pub fn mixed_projection<'a>(
        &self,
        variables: &[VariableId],
        functions: &[VariableId],
        context: &'a SymbolicAsyncGraph,
    ) -> MixedProjection<'a> {
        MixedProjection::new(variables.to_vec(), functions.to_vec(), context, &self.bdd)
    }
}

/// Relation operations.
impl GraphColoredVertices {
    /// Remove every occurrence of a color form `colors` set.
    pub fn minus_colors(&self, colors: &GraphColors) -> Self {
        self.copy(self.bdd.and_not(&colors.bdd))
    }

    /// Only retain colours in the supplied `colors` set.
    pub fn intersect_colors(&self, colors: &GraphColors) -> Self {
        self.copy(self.bdd.and(&colors.bdd))
    }

    /// Remove every occurrence of a vertex from `vertices`, regardless of color.
    pub fn minus_vertices(&self, vertices: &GraphVertices) -> Self {
        self.copy(self.bdd.and_not(&vertices.bdd))
    }

    /// Retain only occurrences of vertices from `vertices`, regardless of color.
    pub fn intersect_vertices(&self, vertices: &GraphVertices) -> Self {
        self.copy(self.bdd.and(&vertices.bdd))
    }

    /// For every color, pick exactly one vertex.
    pub fn pick_vertex(&self) -> Self {
        self.copy(self.bdd.pick(&self.state_variables))
    }

    /// For every vertex, pick exactly one color.
    pub fn pick_color(&self) -> Self {
        self.copy(self.bdd.pick(&self.parameter_variables))
    }

    /// Pick one (vertex, color) pair from this set and return it as a singleton.
    ///
    /// If the set is empty, return empty set.
    pub fn pick_singleton(&self) -> GraphColoredVertices {
        if self.is_empty() {
            self.clone()
        } else {
            let witness = self.bdd.sat_witness().unwrap();
            // Retain only the relevant variables.
            let mut partial_valuation = Vec::new();
            for s_var in &self.state_variables {
                partial_valuation.push((*s_var, witness[*s_var]));
            }
            for p_var in &self.parameter_variables {
                partial_valuation.push((*p_var, witness[*p_var]));
            }
            self.copy(self.bdd.select(&partial_valuation))
        }
    }

    /// Set of all colors which are in this set for at least one vertex.
    pub fn colors(&self) -> GraphColors {
        GraphColors {
            bdd: self.bdd.exists(&self.state_variables),
            parameter_variables: self.parameter_variables.clone(),
        }
    }

    /// Set of all vertices which are in this set for at least one colour.
    pub fn vertices(&self) -> GraphVertices {
        GraphVertices {
            bdd: self.bdd.exists(&self.parameter_variables),
            state_variables: self.state_variables.clone(),
        }
    }
}

impl BddSet for GraphColoredVertices {
    fn as_bdd(&self) -> &Bdd {
        GraphColoredVertices::as_bdd(self)
    }

    fn copy(&self, bdd: Bdd) -> Self {
        GraphColoredVertices::copy(self, bdd)
    }

    fn active_variables(&self) -> u16 {
        u16::try_from(self.state_variables.len() + self.parameter_variables.len()).unwrap()
    }
}

#[cfg(test)]
mod tests {
    use crate::biodivine_std::traits::Set;
    use crate::symbolic_async_graph::SymbolicAsyncGraph;
    use crate::BooleanNetwork;
    use num_bigint::BigInt;
    use num_traits::One;

    #[test]
    fn basic_colored_spaces_set_test() {
        let bn = BooleanNetwork::try_from_file("aeon_models/005.aeon").unwrap();
        let stg = SymbolicAsyncGraph::new(bn.clone()).unwrap();

        let unit = stg.mk_unit_colored_vertices();
        assert!(!unit.is_singleton());
        assert_eq!(unit, unit.copy(unit.clone().into_bdd()));

        let singleton = unit.pick_singleton();
        assert_eq!(1.0, singleton.approx_cardinality());
        assert_eq!(BigInt::one(), singleton.exact_cardinality());
        let singleton_color = singleton.colors();
        let singleton_vertices = singleton.vertices();
        assert!(singleton_color.is_singleton());
        assert!(singleton_vertices.is_singleton());
        assert!(!unit.intersect_colors(&singleton_color).is_singleton());
        // There is only one color, hence this holds. Otherwise this should not hold.
        assert!(unit.intersect_vertices(&singleton_vertices).is_singleton());
        assert!(unit.minus_colors(&singleton_color).is_empty());
        assert!(unit.minus_vertices(&singleton_vertices).is_subset(&unit));

        let var = bn.as_graph().find_variable("v_XPF").unwrap();
        let selected = unit.fix_network_variable(var, true);
        assert_eq!(
            unit.approx_cardinality() / 2.0,
            selected.approx_cardinality()
        );
        let restricted = unit.restrict_network_variable(var, true);
        assert_eq!(unit.approx_cardinality(), restricted.approx_cardinality());
        let restricted = singleton.restrict_network_variable(var, false);
        assert_eq!(
            singleton.approx_cardinality() * 2.0,
            restricted.approx_cardinality()
        );
        assert!(singleton.restrict_network_variable(var, true).is_empty());

        // There are 28 variables and we are eliminating 22 of them, so 6 should be left.
        let project = unit.raw_projection(&stg.symbolic_context().state_variables()[0..22]);
        assert_eq!(project.iter().count(), 2_usize.pow(6));
    }
}
