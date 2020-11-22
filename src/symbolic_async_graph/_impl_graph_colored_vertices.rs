use crate::symbolic_async_graph::{GraphColoredVertices, GraphColors};
use biodivine_lib_bdd::Bdd;

/* Basic utility operations */
impl GraphColoredVertices {
    pub fn new(bdd: Bdd, p_var_count: u16) -> GraphColoredVertices {
        return GraphColoredVertices { bdd, p_var_count };
    }

    pub fn into_bdd(self) -> Bdd {
        return self.bdd;
    }

    pub fn as_bdd(&self) -> &Bdd {
        return &self.bdd;
    }

    pub fn cardinality(&self) -> f64 {
        return self.bdd.cardinality();
    }
}

/* Set operations */
impl GraphColoredVertices {
    /* TODO: If "shields_up", check that p_var_count is the same. */

    pub fn union(&self, other: &Self) -> Self {
        return Self::new(self.bdd.or(&other.bdd), self.p_var_count);
    }

    pub fn intersect(&self, other: &Self) -> Self {
        return Self::new(self.bdd.and(&other.bdd), self.p_var_count);
    }

    pub fn minus(&self, other: &Self) -> Self {
        return Self::new(self.bdd.and_not(&other.bdd), self.p_var_count);
    }

    pub fn is_empty(&self) -> bool {
        return self.bdd.is_false();
    }

    pub fn is_subset(&self, other: &Self) -> bool {
        return self.bdd.and_not(&other.bdd).is_false();
    }
}

/* Relation operations */
impl GraphColoredVertices {
    pub fn minus_colors(&self, colors: &GraphColors) -> Self {
        return Self::new(self.bdd.and_not(&colors.bdd), self.p_var_count);
    }

    pub fn intersect_colors(&self, colors: &GraphColors) -> Self {
        return Self::new(self.bdd.and(&colors.bdd), self.p_var_count);
    }

    pub fn pivots(&self) -> Self {
        return Self::new(
            self.bdd.extended_witness(self.p_var_count),
            self.p_var_count,
        );
    }

    pub fn color_projection(&self) -> GraphColors {
        return GraphColors::new(self.bdd.projection(self.p_var_count), self.p_var_count);
    }
}
