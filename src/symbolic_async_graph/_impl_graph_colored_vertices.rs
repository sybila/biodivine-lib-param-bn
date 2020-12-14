use crate::symbolic_async_graph::{
    GraphColoredVertices, GraphColors, GraphVertices, SymbolicContext,
};
use biodivine_lib_bdd::Bdd;

/// Basic utility operations.
impl GraphColoredVertices {
    /// Construct a new colored vertex set from a given `bdd` and symbolic `context`.
    pub fn new(bdd: Bdd, context: &SymbolicContext) -> GraphColoredVertices {
        return GraphColoredVertices {
            bdd,
            state_variables: context.state_variables.clone(),
            parameter_variables: context.parameter_variables.clone(),
        };
    }

    /// Construct a new colored vertex set by copying the context of the current set.
    pub fn copy(&self, bdd: Bdd) -> GraphColoredVertices {
        return GraphColoredVertices {
            bdd,
            state_variables: self.state_variables.clone(),
            parameter_variables: self.parameter_variables.clone(),
        };
    }

    /// Convert this set to a raw `Bdd`.
    pub fn into_bdd(self) -> Bdd {
        return self.bdd;
    }

    /// View this set as a raw `Bdd`.
    pub fn as_bdd(&self) -> &Bdd {
        return &self.bdd;
    }

    /// Convert this set to a `.dot` graph.
    pub fn to_dot_string(&self, context: &SymbolicContext) -> String {
        self.bdd.to_dot_string(&context.bdd, true)
    }

    /// Amount of storage used for this symbolic set.
    pub fn symbolic_size(&self) -> usize {
        return self.bdd.size();
    }

    /// Approximate size of this set (error grows for large sets).
    pub fn approx_cardinality(&self) -> f64 {
        return self.bdd.cardinality();
    }
}

/// Set operations.
impl GraphColoredVertices {
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

/// Relation operations.
impl GraphColoredVertices {
    pub fn minus_colors(&self, colors: &GraphColors) -> Self {
        self.copy(self.bdd.and_not(&colors.bdd))
    }

    pub fn intersect_colors(&self, colors: &GraphColors) -> Self {
        self.copy(self.bdd.and(&colors.bdd))
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
        return GraphColors {
            bdd: self.bdd.projection(&self.state_variables),
            parameter_variables: self.parameter_variables.clone(),
        };
    }

    /// Set of all vertices which are in this set for at least one colour.
    pub fn states(&self) -> GraphVertices {
        return GraphVertices {
            bdd: self.bdd.projection(&self.parameter_variables),
            state_variables: self.state_variables.clone(),
        };
    }
}
