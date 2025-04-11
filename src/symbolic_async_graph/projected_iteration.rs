//! ## Projection iterators
//!
//! In this module, we provide a set of "projection iterators". These allow us to iterate over
//! members of a symbolic set, but only up to a certain subset of variables.
//!
//! For example, in a model with 200 variables, it may not be realistic to iterate over all
//! attractor states, because the state space is simply too large. However, if we can narrow
//! this search down to, e.g., 10 variables, we can use `StateProjection` to enumerate the
//! valuations of these variables that appear in the original set.
//!
//! Similarly, we can use `FnUpdateProjection` and `MixedProjection` to iterate over instantiations
//! of individual update functions, and over combinations of variable and update function
//! instantiations.
//!
//! If you want to implement another form of projection, you can start with a `RawProjection`,
//! which iterates over a raw `BddPartialValuation`. Then, you can translate this partial
//! valuation to parameter or variable interpretations, depending on your set of retained
//! symbolic variables.
//!
//! Note that the underlying algorithm can also work safely with "extra state variables", meaning
//! they are also safely abstracted away during iteration. Also note that all projections here
//! are *existential*. In the future, we might also consider *universal* projections, but these
//! don't seem to have as wide applications for now.
//!
//!

use crate::symbolic_async_graph::{SymbolicAsyncGraph, SymbolicContext};
use crate::{FnUpdate, VariableId};
use biodivine_lib_bdd::{
    Bdd, BddPartialValuation, BddSatisfyingValuations, BddValuation, BddVariable,
};
use std::collections::HashSet;

/// A helper object that stores the result of a "raw projection" so that we can create
/// iterators over such projection.
///
/// Note that the representation is slightly misleading, because the underlying `Bdd` actually
/// has all non-retained variables fixed to `False`. This ensures that when we iterate through
/// its valuations, we do not repeat valuations that only differ in variables that
/// are not retained.
#[derive(Clone)]
pub struct RawProjection {
    retained_variables: Vec<BddVariable>,
    bdd: Bdd,
}

/// An iterator that goes through the `BddPartialValuation` objects that encode elements
/// of a symbolic set/relation.
pub struct RawSymbolicIterator<'a> {
    raw_projection: &'a RawProjection,
    inner_iterator: BddSatisfyingValuations<'a>,
}

/// A version of [RawSymbolicIterator] which actually owns the underlying [RawProjection].
/// This means the iterator is not tied to the lifetime of the projection.
///
/// Note that due to our unfortunate API design, this `struct` has to use a minor "hack" to
/// make it work. In particular, we have to "fake" a `'static` lifetime on
/// the [BddSatisfyingValuations] iterator. In our case, this is safe because (a) we don't
/// leak the inner iterator anywhere, so the hack is contained to our private code, and (b)
/// we still own the original projection, so it actually lives as long as the iterator.
/// Finally, (c), the destruction of the iterator is passive and does not perform any actions
/// on the underlying projection (which may have been destroyed at this time, depending
/// on the destructor invocation order).
///
/// Also note that the `Box` around `RawProjection` is essential! When we are constructing
/// the inner iterator, we need to reference the final memory location of the `RawProjection`.
/// Hence, we need a heap pointer that will stay the same after we move the projection into
/// the [OwnedRawSymbolicIterator].
pub struct OwnedRawSymbolicIterator {
    raw_projection: Box<RawProjection>,
    inner_iterator: BddSatisfyingValuations<'static>,
}

impl RawProjection {
    /// Create a `RawProjection` from the given set of retained variables and a `Bdd`.
    ///
    /// The constructor will first eliminate all non-retained variables from the `Bdd`. Then it
    /// will automatically restrict all non-retained variables to `false` in order
    /// to make the `Bdd` iterable in a way that visits relevant valuations only once.
    pub fn new(retained: Vec<BddVariable>, bdd: &Bdd) -> RawProjection {
        // First, eliminate all variables in the support set that are not retained:
        let to_eliminate: Vec<BddVariable> = bdd
            .support_set()
            .into_iter()
            .filter(|it| !retained.contains(it))
            .collect();
        let projection = bdd.exists(&to_eliminate);
        // Then fix everything that is not retained to `False` to ensure succinct enumeration.
        let all_false = BddValuation::all_false(projection.num_vars());
        let parameters_false = Bdd::from(all_false).exists(&retained);
        RawProjection {
            retained_variables: retained,
            bdd: projection.and(&parameters_false),
        }
    }

    pub fn iter(&self) -> RawSymbolicIterator {
        RawSymbolicIterator {
            raw_projection: self,
            inner_iterator: self.bdd.sat_valuations(),
        }
    }
}

impl IntoIterator for RawProjection {
    type Item = BddPartialValuation;
    type IntoIter = OwnedRawSymbolicIterator;

    fn into_iter(self) -> Self::IntoIter {
        let iterable = Box::new(self);
        let static_iterable = unsafe {
            (iterable.as_ref() as *const RawProjection)
                .as_ref()
                .unwrap()
        };
        OwnedRawSymbolicIterator {
            raw_projection: iterable,
            inner_iterator: static_iterable.bdd.sat_valuations(),
        }
    }
}

/// Restrict a BDD valuation only to the provided "retained" variables.
fn restrict_valuation(valuation: BddValuation, retain: &[BddVariable]) -> BddPartialValuation {
    let mut partial = BddPartialValuation::empty();
    for var in retain {
        partial.set_value(*var, valuation[*var]);
    }
    partial
}

impl Iterator for RawSymbolicIterator<'_> {
    type Item = BddPartialValuation;

    fn next(&mut self) -> Option<Self::Item> {
        // Extract only the symbolic variables that are actually retained in this projection.
        self.inner_iterator
            .next()
            .map(|valuation| restrict_valuation(valuation, &self.raw_projection.retained_variables))
    }
}

impl Iterator for OwnedRawSymbolicIterator {
    type Item = BddPartialValuation;

    fn next(&mut self) -> Option<Self::Item> {
        self.inner_iterator
            .next()
            .map(|valuation| restrict_valuation(valuation, &self.raw_projection.retained_variables))
    }
}

/// A projection to a subset of state variables.
pub struct StateProjection {
    retained_variables: Vec<VariableId>,
    raw_projection: RawProjection,
}

/// An iterator over a `StateProjection`.
pub struct StateProjectionIterator<'a> {
    projection: &'a StateProjection,
    inner_iterator: BddSatisfyingValuations<'a>,
}

impl StateProjection {
    pub fn new(
        retained: Vec<VariableId>,
        all_state_variables: &[BddVariable],
        bdd: &Bdd,
    ) -> StateProjection {
        let retained_symbolic: Vec<BddVariable> = retained
            .iter()
            .map(|it| all_state_variables[it.to_index()])
            .collect();

        StateProjection {
            retained_variables: retained,
            raw_projection: RawProjection::new(retained_symbolic, bdd),
        }
    }

    pub fn iter(&self) -> StateProjectionIterator {
        StateProjectionIterator {
            projection: self,
            inner_iterator: self.raw_projection.bdd.sat_valuations(),
        }
    }
}

impl Iterator for StateProjectionIterator<'_> {
    type Item = Vec<(VariableId, bool)>;

    fn next(&mut self) -> Option<Self::Item> {
        self.inner_iterator.next().map(|valuation| {
            let mut result = Vec::new();
            let network_variables = self.projection.retained_variables.iter();
            let symbolic_variables = self.projection.raw_projection.retained_variables.iter();
            for (v, s_v) in network_variables.zip(symbolic_variables) {
                result.push((*v, valuation.value(*s_v)));
            }
            result
        })
    }
}

/// A projection to a subset of update functions of the original `BooleanNetwork`.
///
/// Note that this projection considers unique instantiations of the network parameters (i.e.
/// uninterpreted and erased update functions). In some cases, these instantiations can lead to
/// semantically equivalent update functions. In such case, this iterator will visit such
/// update functions repeatedly, once for each instantiation.
pub struct FnUpdateProjection<'a> {
    raw_projection: RawProjection,
    context: &'a SymbolicAsyncGraph,
    retained_functions: Vec<VariableId>,
}

/// An iterator over all instantiated update functions in a particular projection.
pub struct FnUpdateProjectionIterator<'a, 'b> {
    projection: &'a FnUpdateProjection<'b>,
    inner_iterator: BddSatisfyingValuations<'a>,
}

impl<'a> FnUpdateProjection<'a> {
    pub fn new<'x>(
        retained: Vec<VariableId>,
        context: &'x SymbolicAsyncGraph,
        bdd: &Bdd,
    ) -> FnUpdateProjection<'x> {
        let retained_symbolic = collect_fn_update_parameters(context, &retained);
        let mut retained_symbolic: Vec<BddVariable> = retained_symbolic.into_iter().collect();
        retained_symbolic.sort();

        FnUpdateProjection {
            raw_projection: RawProjection::new(retained_symbolic, bdd),
            context,
            retained_functions: retained,
        }
    }

    pub fn iter<'b>(&'b self) -> FnUpdateProjectionIterator<'b, 'a> {
        FnUpdateProjectionIterator {
            projection: self,
            inner_iterator: self.raw_projection.bdd.sat_valuations(),
        }
    }
}

impl Iterator for FnUpdateProjectionIterator<'_, '_> {
    type Item = Vec<(VariableId, FnUpdate)>;

    fn next(&mut self) -> Option<Self::Item> {
        self.inner_iterator.next().map(|valuation| {
            instantiate_functions(
                self.projection.context,
                &self.projection.retained_functions,
                &valuation,
            )
        })
    }
}

/// A combination of `StateProjection` and `FnUpdateProjection` which retains some of
/// the network variables and some of the update functions.
///
/// This type of projection can be used to relate a specific state to a specific update function.
/// For example, how does a phenotype variable change with a particular update function?
///
/// Note that the same considerations regarding `FnUpdate` uniqueness as for `FnUpdateProjection`
/// apply here as well.
pub struct MixedProjection<'a> {
    raw_projection: RawProjection,
    context: &'a SymbolicAsyncGraph,
    retained_functions: Vec<VariableId>,
    retained_variables: Vec<VariableId>,
}

pub struct MixedProjectionIterator<'a, 'b> {
    projection: &'a MixedProjection<'b>,
    inner_iterator: BddSatisfyingValuations<'a>,
}

impl<'a> MixedProjection<'a> {
    pub fn new<'x>(
        retained_state: Vec<VariableId>,
        retained_update: Vec<VariableId>,
        context: &'x SymbolicAsyncGraph,
        bdd: &Bdd,
    ) -> MixedProjection<'x> {
        let symbolic_context = context.symbolic_context();
        let mut retained_symbolic = collect_fn_update_parameters(context, &retained_update);
        for var in &retained_state {
            retained_symbolic.insert(symbolic_context.get_state_variable(*var));
        }

        let mut retained_symbolic: Vec<BddVariable> = retained_symbolic.into_iter().collect();
        retained_symbolic.sort();

        MixedProjection {
            raw_projection: RawProjection::new(retained_symbolic, bdd),
            context,
            retained_functions: retained_update,
            retained_variables: retained_state,
        }
    }

    pub fn iter<'b>(&'b self) -> MixedProjectionIterator<'b, 'a> {
        MixedProjectionIterator {
            projection: self,
            inner_iterator: self.raw_projection.bdd.sat_valuations(),
        }
    }
}

impl Iterator for MixedProjectionIterator<'_, '_> {
    type Item = (Vec<(VariableId, bool)>, Vec<(VariableId, FnUpdate)>);

    fn next(&mut self) -> Option<Self::Item> {
        self.inner_iterator.next().map(|valuation| {
            let graph = self.projection.context;
            let state_data = instantiate_state(
                graph.symbolic_context(),
                &self.projection.retained_variables,
                &valuation,
            );
            let function_data =
                instantiate_functions(graph, &self.projection.retained_functions, &valuation);
            (state_data, function_data)
        })
    }
}

/// A helper function that instantiates a partial state valuation from a BDD valuation.
fn instantiate_state(
    context: &SymbolicContext,
    retained: &[VariableId],
    valuation: &BddValuation,
) -> Vec<(VariableId, bool)> {
    let mut data = Vec::new();
    for var in retained {
        let symbolic_variable = context.get_state_variable(*var);
        data.push((*var, valuation.value(symbolic_variable)))
    }
    data
}

/// A helper function that instantiates update functions based on a BDD valuation.
fn instantiate_functions(
    context: &SymbolicAsyncGraph,
    retained: &[VariableId],
    valuation: &BddValuation,
) -> Vec<(VariableId, FnUpdate)> {
    let mut data = Vec::new();
    for var in retained {
        let symbolic_function = &context.fn_update[var.to_index()];
        let fn_update = context
            .symbolic_context()
            .mk_instantiated_fn_update(valuation, symbolic_function);
        data.push((*var, fn_update));
    }
    data
}

/// Collect the symbolic parameter variables that are necessary to instantiate the
/// `retained` update functions of the network from `context`.
fn collect_fn_update_parameters(
    context: &SymbolicAsyncGraph,
    retained: &[VariableId],
) -> HashSet<BddVariable> {
    let symbolic_context = context.symbolic_context();
    let mut retained_symbolic = HashSet::new();
    // First, collect all variables that are relevant.
    for var in retained {
        let update = context.get_symbolic_fn_update(*var);
        retained_symbolic.extend(update.support_set());
    }
    // Then remove state variables to only keep parameter variables.
    for state_var in symbolic_context.state_variables() {
        retained_symbolic.remove(state_var);
    }
    retained_symbolic
}

#[cfg(test)]
mod tests {
    use crate::biodivine_std::traits::Set;
    use crate::symbolic_async_graph::SymbolicAsyncGraph;
    use crate::BooleanNetwork;

    #[test]
    pub fn test_state_projection() {
        let bn = BooleanNetwork::try_from(
            "
        a -> b
        b -> c
        c -> a
        ",
        )
        .unwrap();

        let mut v = bn.variables();
        let a = v.next().unwrap();
        let b = v.next().unwrap();
        let c = v.next().unwrap();

        let stg = SymbolicAsyncGraph::new(&bn).unwrap();

        let a0b0 = stg.mk_subspace(&[(a, false), (b, false)]);
        let b1c1 = stg.mk_subspace(&[(b, true), (c, true)]);

        let union = a0b0.union(&b1c1);

        let ab_projection = union.state_projection(&[a, b]).iter().collect::<Vec<_>>();
        let bc_projection = union.state_projection(&[b, c]).iter().collect::<Vec<_>>();

        let ab_expected = vec![
            vec![(a, false), (b, false)],
            vec![(a, false), (b, true)],
            vec![(a, true), (b, true)],
        ];

        let bc_expected = vec![
            vec![(b, false), (c, false)],
            vec![(b, false), (c, true)],
            vec![(b, true), (c, true)],
        ];

        assert_eq!(ab_projection, ab_expected);
        assert_eq!(bc_projection, bc_expected);

        // The same should be true for vertices only:

        let union = union.vertices();

        let ab_projection = union.state_projection(&[a, b]).iter().collect::<Vec<_>>();
        let bc_projection = union.state_projection(&[b, c]).iter().collect::<Vec<_>>();

        assert_eq!(ab_projection, ab_expected);
        assert_eq!(bc_projection, bc_expected);
    }

    #[test]
    pub fn test_fn_update_projection() {
        let bn = BooleanNetwork::try_from(
            "
            a ->? b
            b ->? c
            c ->? a
            $a: f_a(c)
        ",
        )
        .unwrap();

        let mut v = bn.variables();
        let a = v.next().unwrap();
        let b = v.next().unwrap();
        let c = v.next().unwrap();

        let stg = SymbolicAsyncGraph::new(&bn).unwrap();

        let can_update_a = stg.var_can_post(a, stg.unit_colored_vertices());
        let can_update_b = stg.var_can_post(b, stg.unit_colored_vertices());

        // Here, all three options are viable.
        assert_eq!(
            3,
            can_update_a.fn_update_projection(&[a], &stg).iter().count()
        );

        let a_is_true = stg.fix_network_variable(a, true);
        let b_is_false = stg.fix_network_variable(b, false);

        let a1_and_update = can_update_a.intersect(&a_is_true);

        // Here, only two options are viable, because $a: true will not update.
        assert_eq!(
            2,
            a1_and_update
                .fn_update_projection(&[a], &stg)
                .iter()
                .count()
        );
        // However, the remaining functions should be still unaffected.
        assert_eq!(
            3,
            a1_and_update
                .fn_update_projection(&[b], &stg)
                .iter()
                .count()
        );
        assert_eq!(
            3,
            a1_and_update
                .fn_update_projection(&[c], &stg)
                .iter()
                .count()
        );

        // Now, we also require b=false and remove everything that can update b.
        let set = a1_and_update.intersect(&b_is_false).minus(&can_update_b);

        // This still leaves three functions for `a`, but only one function for b: b=false.
        // This is because we know that b must be false, a must be true, and so b=true would
        // update, as well as b=a would update.
        assert_eq!(2, set.fn_update_projection(&[a], &stg).iter().count());
        assert_eq!(1, set.fn_update_projection(&[b], &stg).iter().count());
        assert_eq!(3, set.fn_update_projection(&[c], &stg).iter().count());

        // The same should be true after projection to colors only:
        let set = set.colors();
        assert_eq!(2, set.fn_update_projection(&[a], &stg).iter().count());
        assert_eq!(1, set.fn_update_projection(&[b], &stg).iter().count());
        assert_eq!(3, set.fn_update_projection(&[c], &stg).iter().count());
    }

    #[test]
    pub fn test_mixed_projection() {
        let bn = BooleanNetwork::try_from(
            "
            a ->? b
            b ->? c
            c ->? a
            $a: f_a(c)
        ",
        )
        .unwrap();

        let mut v = bn.variables();
        let a = v.next().unwrap();
        let b = v.next().unwrap();
        let c = v.next().unwrap();

        let stg = SymbolicAsyncGraph::new(&bn).unwrap();

        let can_update_a = stg.var_can_post(a, stg.unit_colored_vertices());
        let can_update_b = stg.var_can_post(b, stg.unit_colored_vertices());

        let a_is_true = stg.fix_network_variable(a, true);
        let b_is_false = stg.fix_network_variable(b, false);

        let a1_and_update = can_update_a.intersect(&a_is_true);

        // See the fn_update test for the reasoning why function counts are correct.

        // With $a=false, there are four options, but with $a=c, there are only two, since c=false
        // (because `a=true` and we require it must be updated).
        assert_eq!(
            6,
            a1_and_update
                .mixed_projection(&[b, c], &[a], &stg)
                .iter()
                .count()
        );

        // Now, we also require b=false and remove everything that can update b.
        let set = a1_and_update.intersect(&b_is_false).minus(&can_update_b);

        // Here, we have three possible functions for `c`, but `a` is fixed to true and c is free.
        assert_eq!(6, set.mixed_projection(&[a, c], &[c], &stg).iter().count());

        // Meanwhile here, we have $a=false or $a=c, such that they can be all paired with any
        // c function, as long as b is false.
        assert_eq!(6, set.mixed_projection(&[b], &[a, c], &stg).iter().count());
    }
}
