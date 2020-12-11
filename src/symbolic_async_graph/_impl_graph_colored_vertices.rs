use crate::symbolic_async_graph::{
    GraphColoredVertices, GraphColors, GraphVertices, SymbolicAsyncGraph,
};
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

    pub fn pivots(&self, graph: &SymbolicAsyncGraph) -> Self {
        let mut pivots = graph.symbolic_context.bdd.mk_false();
        let mut remaining = self.bdd.clone();
        while !remaining.is_false() {
            // Pick (state, colour)
            let pick: Bdd = remaining.sat_witness().unwrap().into();
            println!("Pick: {}", pick.cardinality());
            // Compute (state, ANY_COLOUR)
            let mut state = pick.clone();
            for v in &graph.symbolic_context.parameter_variables {
                state = state.var_projection(*v);
            }
            println!("State: {}", state.cardinality());
            // Pick colours with that state from remaining:
            let pick = remaining.and(&state);
            println!("Picked: {}", pick.cardinality());
            remaining = remaining.and_not(&pick);
            pivots = pivots.or(&pick);
            println!("Remaining: {}", remaining.cardinality());
        }
        return GraphColoredVertices::new(pivots, self.p_var_count);
    }

    pub fn color_projection(&self, graph: &SymbolicAsyncGraph) -> GraphColors {
        let mut result = self.bdd.clone();
        for v in graph.symbolic_context.state_variables.iter().rev() {
            result = result.var_projection(*v);
        }
        return GraphColors::new(result, self.p_var_count);
    }

    pub fn state_projection(&self, graph: &SymbolicAsyncGraph) -> GraphVertices {
        let mut result = self.bdd.clone();
        for v in &graph.symbolic_context.parameter_variables {
            // Project and fix to zero.
            result = result.var_projection(*v);
            result = result.and(&graph.symbolic_context.bdd.mk_not_var(*v))
        }
        return GraphVertices::new(result, self.p_var_count);
    }
}
