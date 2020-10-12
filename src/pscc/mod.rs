
/*
    Design principles: all sets are over a common BDD variable universe where we have
    parameter variables followed by state variables (this allows simple pivot selection).

    In color sets, the state variables are ignored (so a color set A is represented as `A x V`)
    and in vertex sets, the color variables are ignored (so `C x A`). This does not influence
    normal set operations.
 */

use biodivine_lib_bdd::{BddVariableSet, Bdd};
use crate::BooleanNetwork;

pub struct PsccContext {
    /// All BDD variables representing the parameters and variables of the system.
    bdd_variables: BddVariableSet,
    /// Number of parameter variables.
    p_count: u16,
}

impl PsccContext {

    pub fn new(_bn: BooleanNetwork) -> PsccContext {
        todo!()
    }

    pub fn empty_colours(&self) -> ColorSet {
        return ColorSet { bdd: self.bdd_variables.mk_false() };
    }

    pub fn all_vertices(&self) -> ColorVertexSet {
        return ColorVertexSet { bdd: self.bdd_variables.mk_true() };
    }

    pub fn color_projection(&self, set: &ColorVertexSet) -> ColorSet {
        return ColorSet { bdd: set.bdd.projection(self.p_count) };
    }

    pub fn post(&self, _frontier: &ColorVertexSet) -> ColorVertexSet {
        todo!()
    }

    pub fn pre(&self, _frontier: &ColorVertexSet) -> ColorVertexSet {
        todo!()
    }

}

#[derive(Clone)]
pub struct ColorSet {
    bdd: Bdd
}

impl ColorSet {

    /*
        Operations on color sets are just operations on BDDs since state variables are all erased
        and do not play any role.
    */

    pub fn union(&self, other: &Self) -> Self {
        return ColorSet { bdd: self.bdd.or(&other.bdd) };
    }

    pub fn minus(&self, other: &Self) -> Self {
        return ColorSet { bdd: self.bdd.and_not(&other.bdd) };
    }

    pub fn equals(&self, other: &Self) -> bool {
        return self.bdd.eq(&other.bdd);
    }

}

#[derive(Clone)]
pub struct ColorVertexSet {
    bdd: Bdd
}

impl ColorVertexSet {

    pub fn is_empty(&self) -> bool {
        return self.bdd.is_false();
    }

    pub fn pivots(&self) -> ColorVertexSet {
        todo!()
    }

    pub fn minus(&self, other: &ColorVertexSet) -> ColorVertexSet {
        return ColorVertexSet { bdd: self.bdd.and_not(&other.bdd) };
    }

    pub fn minus_colors(&self, other: &ColorSet) -> ColorVertexSet {
        return ColorVertexSet { bdd: self.bdd.and_not(&other.bdd) };
    }

    pub fn intersect_colors(&self, other: &ColorSet) -> ColorVertexSet {
        return ColorVertexSet { bdd: self.bdd.and(&other.bdd) };
    }

    pub fn union(&self, other: &ColorVertexSet) -> ColorVertexSet {
        return ColorVertexSet { bdd: self.bdd.or(&other.bdd) };
    }

    pub fn intersect(&self, other: &ColorVertexSet) -> ColorVertexSet {
        return ColorVertexSet { bdd: self.bdd.and(&other.bdd) };
    }

    pub fn cardinality(&self) -> f64 {
        return self.bdd.cardinality();
    }

}

pub fn decomposition(context: &PsccContext, universe: ColorVertexSet) {
    if universe.is_empty() { return }
    let pivot = universe.pivots();

    let mut f = pivot.clone();
    let mut b = pivot.clone();
    let mut f_frontier = pivot.clone();
    let mut b_frontier = pivot.clone();
    let mut f_lock = context.empty_colours();
    let mut b_lock = context.empty_colours();

    let ref universe_colors = context.color_projection(&universe);
    while !f_lock.union(&b_lock).equals(universe_colors) {
        let ref new_f_frontier = context.post(&f_frontier).minus(&f);
        let ref new_b_frontier = context.pre(&b_frontier).minus(&b);
        f = f.union(new_f_frontier);
        b = b.union(new_b_frontier);
        let stopped_f_colors = context.color_projection(&f_frontier).minus(&context.color_projection(&new_f_frontier));
        let stopped_b_colors = context.color_projection(&b_frontier).minus(&context.color_projection(&new_b_frontier));
        f_lock = f_lock.union(&stopped_f_colors);
        b_lock = b_lock.union(&stopped_b_colors).minus(&f_lock);
        f_frontier = new_f_frontier.minus_colors(&b_lock);
        b_frontier = new_b_frontier.minus_colors(&f_lock);
    }

    while !f_frontier.intersect(&b).is_empty() {
        f_frontier = context.post(&f_frontier).minus(&f);
        f = f.union(&f_frontier);
    }

    while !b_frontier.intersect(&f).is_empty() {
        b_frontier = context.post(&b_frontier).minus(&b);
        b = b.union(&b_frontier);
    }

    let scc = f.intersect(&b);
    println!("Found scc: {:?}", scc.cardinality());

    let converged = f.intersect_colors(&f_lock).union(&b.intersect_colors(&b_lock));

    decomposition(context, universe.minus(&converged));
    decomposition(context, converged.minus(&scc));

}