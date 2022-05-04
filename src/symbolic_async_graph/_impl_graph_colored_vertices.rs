use crate::biodivine_std::traits::Set;
use crate::symbolic_async_graph::{
    GraphColoredVertices, GraphColors, GraphVertices, SymbolicContext,
};
use biodivine_lib_bdd::Bdd;
use num_bigint::BigInt;
use num_traits::ToPrimitive;

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
        self.bdd.size()
    }

    /// Approximate size of this set (error grows for large sets).
    pub fn approx_cardinality(&self) -> f64 {
        let cardinality = self.bdd.cardinality();
        if cardinality.is_infinite() || cardinality.is_nan() {
            self.bdd
                .exact_cardinality()
                .to_f64()
                .unwrap_or(f64::INFINITY)
        } else {
            cardinality
        }
    }

    /// Compute exact `BigInt` cardinality of this set.
    pub fn exact_cardinality(&self) -> BigInt {
        self.bdd.exact_cardinality()
    }
}

/// Set operations.
impl Set for GraphColoredVertices {
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
            self.copy(self.bdd.sat_witness().unwrap().into())
        }
    }

    /// Set of all colors which are in this set for at least one vertex.
    pub fn colors(&self) -> GraphColors {
        GraphColors {
            bdd: self.bdd.project(&self.state_variables),
            parameter_variables: self.parameter_variables.clone(),
        }
    }

    /// Set of all vertices which are in this set for at least one colour.
    pub fn vertices(&self) -> GraphVertices {
        GraphVertices {
            bdd: self.bdd.project(&self.parameter_variables),
            state_variables: self.state_variables.clone(),
        }
    }
}
