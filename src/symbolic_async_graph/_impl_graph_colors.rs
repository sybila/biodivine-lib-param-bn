use crate::symbolic_async_graph::GraphColors;
use biodivine_lib_bdd::Bdd;
use biodivine_lib_std::param_graph::Params;
use std::ops::Shl;

/* Here, we essentially want to support the same stuff we already support for BddParams */

impl GraphColors {
    pub fn new(bdd: Bdd, p_var_count: u16) -> GraphColors {
        return GraphColors { bdd, p_var_count };
    }

    pub fn into_bdd(self) -> Bdd {
        return self.bdd;
    }

    pub fn cardinality(&self) -> f64 {
        let s_var_count = self.bdd.num_vars() - self.p_var_count;
        return self.bdd.cardinality() / (1.shl(s_var_count) as f64);
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
