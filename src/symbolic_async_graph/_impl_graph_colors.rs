use crate::symbolic_async_graph::{GraphColors, SymbolicAsyncGraph};
use biodivine_lib_bdd::Bdd;
use biodivine_lib_std::param_graph::Params;

/* Here, we essentially want to support the same stuff we already support for BddParams */

impl GraphColors {
    pub fn new(bdd: Bdd, p_var_count: u16) -> GraphColors {
        return GraphColors { bdd, p_var_count };
    }

    pub fn into_bdd(self) -> Bdd {
        return self.bdd;
    }

    pub fn as_bdd(&self) -> &Bdd {
        return &self.bdd;
    }

    /// Essentially "sat witness" function, but it works around the fact that the BDD also contains
    /// state variables which we do not consider.
    pub fn pick_color(&self, graph: &SymbolicAsyncGraph) -> Option<GraphColors> {
        let mut witness: Bdd = self.bdd.sat_witness()?.into();
        // Remove all unnecessarily fixed BDD vars. TODO: Introduce extended sat with custom variables.
        for state_variable in graph.symbolic_context.state_variables.iter() {
            witness = witness.var_projection(*state_variable);
        }
        return Some(GraphColors::new(witness, self.p_var_count));
    }

    pub fn cardinality(&self) -> f64 {
        let s_var_count: i32 = (self.bdd.num_vars() - self.p_var_count) as i32;
        let states = (2.0f64).powi(s_var_count);
        return self.bdd.cardinality() / states;
    }

    pub fn intersect_bdd(&self, other: &Bdd) -> Self {
        return Self::new(self.bdd.and(other), self.p_var_count);
    }

    pub fn minus_bdd(&self, other: &Bdd) -> Self {
        return Self::new(self.bdd.and_not(other), self.p_var_count);
    }
}

impl Params for GraphColors {
    /* TODO: If "shields_up", check that p_var_count is the same. */

    fn union(&self, other: &Self) -> Self {
        return Self::new(self.bdd.or(&other.bdd), self.p_var_count);
    }

    fn intersect(&self, other: &Self) -> Self {
        return Self::new(self.bdd.and(&other.bdd), self.p_var_count);
    }

    fn minus(&self, other: &Self) -> Self {
        return Self::new(self.bdd.and_not(&other.bdd), self.p_var_count);
    }

    fn is_empty(&self) -> bool {
        return self.bdd.is_false();
    }

    fn is_subset(&self, other: &Self) -> bool {
        return self.bdd.and_not(&other.bdd).is_false();
    }
}
