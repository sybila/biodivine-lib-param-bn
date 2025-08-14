//! This module contains algorithms and data structures for efficiently computing fixed-points
//! of large Boolean networks.
//!
//! There are two main approaches one can use to obtain the fixed-points:
//!
//! 1. A solver based method (relying on Z3). This method works well for enumerating
//!    small batches of fixed-points, but does not scale very well for high numbers
//!    of fixed-points, as each of them has to be explicitly returned by the solver.
//!
//! 2. A symbolic BDD-based method. This approach generally suffers more from the state space
//!    explosion (it can take a long time for large networks), but if the number of results
//!    if very high, it can still outperform enumeration based on solvers. Also, it can be
//!    easily restricted to arbitrary symbolic sets,

use crate::biodivine_std::traits::Set;
use crate::symbolic_async_graph::{GraphColoredVertices, SymbolicAsyncGraph};
use crate::symbolic_async_graph::{GraphColors, GraphVertices};
use biodivine_lib_bdd::{Bdd, BddVariable, BddVariableSet};
use std::collections::{HashMap, HashSet};

#[cfg(feature = "solver-z3")]
use crate::Space;
#[cfg(feature = "solver-z3")]
use crate::fixed_points::solver_iterator::{
    SolverColorIterator, SolverIterator, SolverVertexIterator,
};
#[cfg(feature = "solver-z3")]
use crate::solver_context::{BnSolver, BnSolverContext};

/// **(internal)** Implements the iterator used by `FixedPoints::symbolic_iterator`.
/// (The module is hidden, but we re-export iterator in this module)
mod symbolic_iterator;
use crate::symbolic_async_graph::projected_iteration::MixedProjection;
use crate::{BooleanNetwork, VariableId, global_log_level, log_essential, never_stop, should_log};
pub use symbolic_iterator::SymbolicIterator;

/// Implements the iterator used by `FixedPoints::solver_iterator`.
#[cfg(feature = "solver-z3")]
pub mod solver_iterator;

/// Aggregates algorithms for computing fixed point states of the given state-transition graph.
/// Typically, the operation can be also restricted to a particular subset of candidate states.
///
/// Additionally, in some instances the result is provided as an iterator. Note that for
/// the solver-based methods, there is a "color-projection" option but the iteration items
/// are the same as for the general option, because there is currently no better way to
/// represent the result in a type-safe manner. Later, there should be a better way of dealing
/// with interpretation of explicit parameters.
pub struct FixedPoints {
    _dummy: (),
}

impl FixedPoints {
    /// A naive symbolic algorithm that computes the fixed points by gradual elimination of
    /// all states with outgoing transitions.
    ///
    /// Only fixed-points from the `restriction` set are returned. However, the state has to
    /// be a *global* fixed point, not just a fixed-point within the `restriction` set.
    ///
    /// **Characteristics:** As the name suggests, this algorithm is not really suited for
    /// processing complex networks. However, we provide it as a "baseline" for testing other
    /// algorithms. In theory, due to its simplicity, it could be faster on some of the smaller
    /// networks where the symbolic explosion is not severe.
    pub fn naive_symbolic(
        stg: &SymbolicAsyncGraph,
        restriction: &GraphColoredVertices,
    ) -> GraphColoredVertices {
        if cfg!(feature = "print-progress") {
            println!(
                "Start naive symbolic fixed-point search with {}[nodes:{}] candidates.",
                restriction.approx_cardinality(),
                restriction.symbolic_size()
            );
        }

        let mut to_merge: Vec<GraphColoredVertices> = stg
            .variables()
            .map(|var| {
                let can_step = stg.var_can_post(var, stg.unit_colored_vertices());
                let is_stable = restriction.minus(&can_step);
                if cfg!(feature = "print-progress") {
                    println!(
                        " > Created initial set for {:?} using {} BDD nodes.",
                        var,
                        is_stable.symbolic_size()
                    );
                }
                is_stable
            })
            .collect();

        while to_merge.len() > 1 {
            to_merge.sort_by_key(|it| -(it.symbolic_size() as isize));

            if cfg!(feature = "print-progress") {
                let total = to_merge.iter().map(|it| it.symbolic_size()).sum::<usize>();
                println!(
                    " > Merging {} sets using {} BDD nodes.",
                    to_merge.len(),
                    total
                );
            }

            let x = to_merge.pop().unwrap();
            let y = to_merge.pop().unwrap();
            to_merge.push(x.intersect(&y));
        }

        let fixed_points = to_merge.pop().unwrap();

        if cfg!(feature = "print-progress") {
            println!(
                "Found {}[nodes:{}] fixed-points.",
                fixed_points.approx_cardinality(),
                fixed_points.symbolic_size(),
            );
        }

        fixed_points
    }

    /// A better version of the `Self::naive_symbolic` algorithm that can actually scale to
    /// reasonably sized networks (e.g. 100-200 variables + parameters).
    ///
    /// Only fixed-points from the `restriction` set are returned. However, the state has to
    /// be a *global* fixed point, not just a fixed-point within the `restriction` set.
    ///
    /// **Characteristics:** Instead of merging individual constraints one by one, this algorithm
    /// greedily selects the constraint that leads to the smallest intermediate BDD. This requires
    /// more symbolic operations, but can work better as the intermediate BDDs tend to be smaller.
    ///
    /// In particular, this tends to work better for cases where no fixed points exist, because
    /// the process will often quickly find a combination on constraints that prevent
    /// the fixed point from existing (whereas for `naive_symbolic`, this process is much more
    /// random).
    ///
    /// Also note that the algorithm can benefit from parallelization, but we do not implement
    /// it here, as it is a bit problematic to implement in a platform-independent manner.
    ///
    /// You can often scale the algorithm to very large networks as well, but the hardest
    /// bottleneck seems to be the total number of fixed points. As such, if the network is large
    /// (e.g. 1000 variables) but has only a few fixed points, it can often still be solved by this
    /// method. However, if there are many parameters (e.g. >50) and the number of fixed points
    /// is proportional to the number of parameters, you will be bounded by the inherent
    /// combinatorial complexity of the resulting set of states.
    pub fn symbolic(
        stg: &SymbolicAsyncGraph,
        restriction: &GraphColoredVertices,
    ) -> GraphColoredVertices {
        Self::_symbolic(stg, restriction, global_log_level(), &never_stop).unwrap()
    }

    /// A version of [FixedPoints::symbolic] with cancellation
    /// and logging.
    pub fn _symbolic<E, F: Fn() -> Result<(), E>>(
        stg: &SymbolicAsyncGraph,
        restriction: &GraphColoredVertices,
        log_level: usize,
        interrupt: &F,
    ) -> Result<GraphColoredVertices, E> {
        if should_log(log_level) {
            println!(
                "Start symbolic fixed-point search with {}[nodes:{}] candidates.",
                restriction.approx_cardinality(),
                restriction.symbolic_size()
            );
        }

        let mut to_merge = Self::prepare_to_merge(stg, log_level, interrupt)?;

        /*
           Note to self: There is actually a marginally faster version of this algorithm that
           does not throw away the intermediate results but instead carries them over to the
           next iteration. Nevertheless, this version also wastes much more memory, as all
           results have to be preserved, so I ultimately decided not to use it.
        */

        // Finally add the global requirement on the whole state space, if it is relevant.
        if !stg.unit_colored_vertices().is_subset(restriction) {
            to_merge.push(restriction.as_bdd().clone());
        }

        interrupt()?;

        let fixed_points = Self::symbolic_merge(
            stg.symbolic_context().bdd_variable_set(),
            to_merge,
            HashSet::default(),
        );

        interrupt()?;

        let fixed_points = stg.unit_colored_vertices().copy(fixed_points);

        if should_log(log_level) {
            println!(
                "Found {}[nodes:{}] fixed-points.",
                fixed_points.approx_cardinality(),
                fixed_points.symbolic_size(),
            );
        }

        Ok(fixed_points)
    }

    /// This is a general symbolic projected fixed-point algorithm. It works on the same
    /// principle as `Self::symbolic`, `Self::symbolic_colors` and `Self::symbolic_vertices`.
    /// However, it allows projection to arbitrary network components.
    ///
    /// In theory, this should be the same as running `Self::symbolic` and computing
    /// a `MixedProjection` on the result. However, the benefit here is that the projection
    /// is applied gradually during fixed-point search. This means we can potentially handle
    /// much larger networks, because at no point is the exact result fully represented.
    /// The same is true for `Self::symbolic_colors` and `Self::symbolic_vertices`, but here
    /// we have a much finer control over what network elements are retained.
    ///
    /// Naturally, you can use empty `retain_state` or `retain_function` to implement a projection
    /// to subset of states/functions. For now, we do not provide extra methods for this, as it
    /// is not a very common use case. But if you want it, get in touch.
    pub fn symbolic_projection<'a>(
        network: &BooleanNetwork,
        stg: &'a SymbolicAsyncGraph,
        restriction: &GraphColoredVertices,
        retain_state: &[VariableId],
        retain_function: &[VariableId],
    ) -> MixedProjection<'a> {
        if cfg!(feature = "print-progress") {
            println!(
                "Start symbolic projected fixed-point search with {}[nodes:{}] candidates.",
                restriction.approx_cardinality(),
                restriction.symbolic_size()
            );
        }

        let mut to_merge = Self::prepare_to_merge(stg, global_log_level(), &never_stop).unwrap();

        // Now compute the BDD variables that should be projected away.
        let ctx = stg.symbolic_context();

        // Initially, "remove" all variables.
        let mut project: HashSet<BddVariable> =
            ctx.bdd_variable_set().variables().into_iter().collect();
        // Now, remove all state and parameter variables that we want to keep.
        for var in retain_state {
            project.remove(&ctx.get_state_variable(*var));
        }
        for var in retain_function {
            if let Some(function) = network.get_update_function(*var) {
                for p_id in function.collect_parameters() {
                    for p in ctx.get_explicit_function_table(p_id).symbolic_variables() {
                        project.remove(p);
                    }
                }
            } else {
                for p in ctx
                    .get_implicit_function_table(*var)
                    .unwrap()
                    .symbolic_variables()
                {
                    project.remove(p);
                }
            }
        }

        // Finally add the global requirement on the whole state space, if it is relevant.
        if !stg.unit_colored_vertices().is_subset(restriction) {
            to_merge.push(restriction.as_bdd().clone());
        }

        let fixed_points =
            Self::symbolic_merge(stg.symbolic_context().bdd_variable_set(), to_merge, project);

        if cfg!(feature = "print-progress") {
            println!(
                "Found {}[nodes:{}] projected results.",
                fixed_points.cardinality(),
                fixed_points.size(),
            );
        }

        MixedProjection::new(
            retain_state.to_vec(),
            retain_function.to_vec(),
            stg,
            &fixed_points,
        )
    }

    /// This is a helper method that is used by `Self::symbolic_vertices` and
    /// `Self::symbolic_colors`.
    ///
    /// It greedily performs a conjunction of the given BDDs, but eliminates the symbolic
    /// variables given in `project`. Using this method, you can implement arbitrary projected
    /// fixed-point detection. However, the method is inherently unsafe because currently
    /// there is no way to give a type-safe result for operations other than `symbolic_vertices`
    /// and `symbolic_colors`, so it is up to you to understand whether the result is
    /// actually what you wanted.
    pub fn symbolic_merge(
        universe: &BddVariableSet,
        to_merge: Vec<Bdd>,
        // The set of variables that will be eliminated from the result.
        project: HashSet<BddVariable>,
    ) -> Bdd {
        Self::_symbolic_merge(universe, to_merge, project, global_log_level(), &never_stop).unwrap()
    }

    /// A version of [FixedPoints::symbolic_merge] with cancellation
    /// and logging.
    pub fn _symbolic_merge<E, F: Fn() -> Result<(), E>>(
        universe: &BddVariableSet,
        to_merge: Vec<Bdd>,
        mut project: HashSet<BddVariable>,
        log_level: usize,
        interrupt: &F,
    ) -> Result<Bdd, E> {
        // First, assign each merge item a unique integer identifier.
        let mut to_merge: HashMap<usize, Bdd> = to_merge.into_iter().enumerate().collect();

        // And compute the support set for each of them.
        let support_sets: HashMap<usize, HashSet<BddVariable>> = to_merge
            .iter()
            .map(|(id, set)| (*id, set.support_set()))
            .collect();

        // Now, for every projection variable, determine which merge items depend on said variable.
        // Once all of these items appear in the final result, the variable can be removed.
        let dependency_map: HashMap<BddVariable, HashSet<usize>> = project
            .iter()
            .map(|bdd_var| {
                let dependencies = support_sets
                    .iter()
                    .filter(|(_, set)| set.contains(bdd_var))
                    .map(|(id, _)| *id)
                    .collect::<HashSet<usize>>();
                (*bdd_var, dependencies)
            })
            .collect();

        let mut result = universe.mk_true();
        let mut merged = HashSet::new();
        interrupt()?;

        /*
           Note to self: It seems that not all projections are always beneficial to the BDD size.
           At the same time, a non-optimal merge may enable a very useful projection. It is
           not entirely clear how to greedily apply these two observations. Ideally, we'd like
           to prioritize merges that lead to projections, but this is not universally true.

           Maybe we could at least greedily prefer merging sets that will immediately lead to
           projections? But even this is not an entirely clear win.
        */

        while !to_merge.is_empty() || !project.is_empty() {
            for p_var in project.clone() {
                let dependencies = dependency_map.get(&p_var).unwrap();
                if dependencies.is_subset(&merged) {
                    result = result.var_exists(p_var);
                    project.remove(&p_var);
                    interrupt()?;

                    if log_essential(log_level, result.size()) {
                        println!(
                            " > Projection. New result has {} BDD nodes. Remaining projections: {}.",
                            result.size(),
                            project.len()
                        );
                    }
                }
            }

            let mut best_result = universe.mk_true();
            let mut best_result_size = usize::MAX;
            let mut best_index = 0;

            // Ensure deterministic iteration of results.
            let mut merge_iter: Vec<usize> = to_merge.keys().cloned().collect();
            merge_iter.sort_by_cached_key(|it| to_merge[it].size());

            for i in merge_iter {
                let set = &to_merge[&i];
                let bdd = Bdd::binary_op_with_limit(
                    best_result_size,
                    set,
                    &result,
                    biodivine_lib_bdd::op_function::and,
                );
                interrupt()?;

                if let Some(bdd) = bdd {
                    // At this point, the size of the BDD should be smaller or equal to the
                    // best result, so we can just update it.
                    assert!(bdd.size() <= best_result_size);
                    best_result = bdd;
                    best_result_size = best_result.size();
                    best_index = i;
                }
            }

            // This may not be true in the last iteration if the only thing left to do
            // are projections.
            if best_result_size != usize::MAX {
                result = best_result;
                to_merge.remove(&best_index);
                merged.insert(best_index);

                if result.is_false() {
                    return Ok(universe.mk_false());
                }

                if log_essential(log_level, result.size()) {
                    println!(
                        " > Merge. New result has {} BDD nodes. Remaining constraints: {}.",
                        result.size(),
                        to_merge.len(),
                    );
                }
            }
        }

        interrupt()?;

        if should_log(log_level) {
            println!("Merge finished with {} BDD nodes.", result.size(),);
        }

        // All projection variables are indeed gone.
        assert!(project.is_empty());
        // And everything was merged.
        assert_eq!(merged.len(), support_sets.len());

        Ok(result)
    }

    /// The result of the function are all vertices that can appear as fixed-points for **some**
    /// parameter valuation. That is, for every returned vertex, there is at least one color
    /// for which the vertex is a fixed-point.
    ///
    /// **Characteristics:** If the network has no parameters, the result is equivalent to the
    /// result of `Self::symbolic`. However, if there are parameters in the network, the result
    /// is often much smaller and can be computed much faster.
    ///
    /// In particular, it is possible to use the result (or subsets of the result) as `restriction`
    /// sets for `Self::symbolic` to obtain the full information later. In some cases, this is also
    /// faster than running `Self::symbolic` directly.
    ///
    /// If you are only interested in certain combinations of variables within the fixed-points,
    /// you can also write a custom projection query using `Self::symbolic_merge`.
    pub fn symbolic_vertices(
        stg: &SymbolicAsyncGraph,
        restriction: &GraphColoredVertices,
    ) -> GraphVertices {
        Self::_symbolic_vertices(stg, restriction, global_log_level(), &never_stop).unwrap()
    }

    /// A version of [FixedPoints::symbolic_vertices] with cancellation
    /// and logging.
    pub fn _symbolic_vertices<E, F: Fn() -> Result<(), E>>(
        stg: &SymbolicAsyncGraph,
        restriction: &GraphColoredVertices,
        log_level: usize,
        interrupt: &F,
    ) -> Result<GraphVertices, E> {
        if should_log(log_level) {
            println!(
                "Start symbolic fixed-point vertex search with {}[nodes:{}] candidates.",
                restriction.approx_cardinality(),
                restriction.symbolic_size()
            );
        }

        let mut to_merge = Self::prepare_to_merge(stg, log_level, interrupt)?;

        // Finally add the global requirement on the whole state space, if it is relevant.
        if !stg.unit_colored_vertices().is_subset(restriction) {
            to_merge.push(restriction.as_bdd().clone());
        }

        let project: HashSet<BddVariable> = stg
            .symbolic_context()
            .parameter_variables()
            .iter()
            .cloned()
            .collect();

        interrupt()?;

        let bdd =
            Self::symbolic_merge(stg.symbolic_context().bdd_variable_set(), to_merge, project);

        let vertices = stg.empty_colored_vertices().vertices().copy(bdd);

        interrupt()?;

        if should_log(log_level) {
            println!(
                "Found {}[nodes:{}] fixed-point vertices.",
                vertices.approx_cardinality(),
                vertices.symbolic_size(),
            );
        }

        Ok(vertices)
    }

    /// Similar to `Self::symbolic_vertices`, but only returns colors for which there exists
    /// at least one fixed-point within `restriction`.
    pub fn symbolic_colors(
        stg: &SymbolicAsyncGraph,
        restriction: &GraphColoredVertices,
    ) -> GraphColors {
        Self::_symbolic_colors(stg, restriction, global_log_level(), &never_stop).unwrap()
    }

    /// A version of [FixedPoints::symbolic_colors] with cancellation
    /// and logging.
    pub fn _symbolic_colors<E, F: Fn() -> Result<(), E>>(
        stg: &SymbolicAsyncGraph,
        restriction: &GraphColoredVertices,
        log_level: usize,
        interrupt: &F,
    ) -> Result<GraphColors, E> {
        if should_log(log_level) {
            println!(
                "Start symbolic fixed-point color search with {}[nodes:{}] candidates.",
                restriction.approx_cardinality(),
                restriction.symbolic_size()
            );
        }

        let mut to_merge = Self::prepare_to_merge(stg, log_level, interrupt)?;

        // Finally add the global requirement on the whole state space, if it is relevant.
        if !stg.unit_colored_vertices().is_subset(restriction) {
            to_merge.push(restriction.as_bdd().clone());
        }

        let project: HashSet<BddVariable> = stg
            .symbolic_context()
            .state_variables()
            .iter()
            .cloned()
            .collect();

        interrupt()?;

        let bdd =
            Self::symbolic_merge(stg.symbolic_context().bdd_variable_set(), to_merge, project);

        let colors = stg.empty_colored_vertices().colors().copy(bdd);

        interrupt()?;

        if should_log(log_level) {
            println!(
                "Found {}[nodes:{}] fixed-point colors.",
                colors.approx_cardinality(),
                colors.symbolic_size(),
            );
        }

        Ok(colors)
    }

    /// This function creates an iterator that yields symbolic sets of fixed-point states, such
    /// that eventually, all fixed-points are returned (and there are no duplicates).
    ///
    /// As with `Self::symbolic`, you can use the `restriction` set to limit the search to
    /// a particular subset of states. Furthermore, you can use `size_limit` to give the algorithm
    /// a hint as to how large (in terms of BDD nodes) you want the resulting sets to be.
    /// This value depends on how much memory and time you have, but a good starting value
    /// tends to be somewhere between `1_000_000` and `10_000_000`. If you'd rather want more
    /// smaller sets, but get them quickly, you can go as low as `10_000` or `100_000` (given
    /// the model is not too large).
    ///
    /// It is not strictly guaranteed that the results are within this size limit, but the
    /// algorithm makes a reasonable effort to achieve this.
    ///
    /// **Characteristics:** The algorithm is based on `Self::symbolic`, but once the expected
    /// size of the result exceeds the given `size_limit`, it will try to fork the computation
    /// based on one of the constraint clauses into two branches that can be completed
    /// independently. As long as there are still clauses to fork on, this should result in
    /// sets that are within the given size limit.
    ///
    /// Note that computing the result like this is almost always slower than just using
    /// `Self::symbolic`. However, there are possible advantages to this approach:
    ///
    /// 1. Depending on the chosen `size_limit`, the algorithm might use less memory to
    ///    compute the result than `Self::symbolic` (assuming you actually free the yielded
    ///    results or store them outside the main memory).
    ///
    /// 2. While the runtime of the whole algorithm is typically longer, it should usually
    ///    take less time to get the *first* item than fully running `Self::symbolic`. Also,
    ///    you can often "tune" this time-to-first-answer using the `size_limit`, as smaller
    ///    results tend to be faster to find (iterating over all of them is longer though).
    ///
    /// Furthermore, it is relatively easy to extend this implementation to incorporate even
    /// more parallelism than in `Self::symbolic`. Also, we could decrease memory
    /// usage by storing some of the intermediate results on disk instead of RAM.
    ///
    /// Finally, note that there is a certain minimal value of `size_limit` below which the
    /// algorithm cannot really fork effectively, because the sets are simply too large for the
    /// limit. For truly large networks (>1000 nodes), it is not always a good idea to set the
    /// limit too low. If you only want to find *some* fixed point for *some* parametrisation,
    /// it is recommended that you either use the solver-based approach (`Self::solver_iterator`),
    /// or one of the projection methods (`Self::symbolic_vertices` or `Self::symbolic_colors`).
    pub fn symbolic_iterator<'a>(
        stg: &'a SymbolicAsyncGraph,
        restriction: &GraphColoredVertices,
        size_limit: usize,
    ) -> SymbolicIterator<'a> {
        SymbolicIterator::new(stg, restriction, size_limit)
    }

    /// Constructs an iterator that uses Z3 to enumerate all fixed-points appearing within
    /// the given list of `positive_restriction` subspaces while avoiding any of the
    /// `negative_restriction` subspaces.
    ///
    /// Keep in mind that the `positive_restriction` is by default empty, i.e. no fixed-points
    /// are returned. You can use `Space::new` to create a subspace of all states for this
    /// purpose. Restrictions on parameter valuations will be automatically applied based on
    /// the `BooleanNetwork` associated with the provided `BnSolverContext`.
    ///
    /// Note that the states must be global fixed-points, not just fixed-points within the
    /// restriction candidates.
    ///
    /// This method works very well for finding small numbers of fixed-points,
    /// but since the fixed-points are computed individually, it cannot really enumerate
    /// all fixed-points of models with a lot of parameters.
    ///
    /// However, you can conceivably use it to sample the space of possible fixed-points
    /// using various values for the `restriction` set.
    #[cfg(feature = "solver-z3")]
    pub fn solver_iterator(
        context: &BnSolverContext,
        positive_restrictions: &[Space],
        negative_restriction: &[Space],
    ) -> SolverIterator {
        let solver = Self::make_fixed_points_solver(context);
        solver.assert_within_spaces(positive_restrictions);
        solver.assert_not_within_spaces(negative_restriction);
        SolverIterator::new_with_solver(context, solver)
    }

    /// Same as `FixedPoints::solver_iterator`, but the resulting iterator only goes through
    /// the unique fixed-point vertices, ignoring the associated colors.
    #[cfg(feature = "solver-z3")]
    pub fn solver_vertex_iterator(
        context: &BnSolverContext,
        positive_restrictions: &[Space],
        negative_restriction: &[Space],
    ) -> SolverVertexIterator {
        let solver = Self::make_fixed_points_solver(context);
        solver.assert_within_spaces(positive_restrictions);
        solver.assert_not_within_spaces(negative_restriction);
        SolverVertexIterator::new_with_solver(context, solver)
    }

    /// Same as `FixedPoints::solver_iterator`, but the resulting iterator only goes through
    /// the unique fixed-point colors, ignoring the associated colors.
    #[cfg(feature = "solver-z3")]
    pub fn solver_color_iterator(
        context: &BnSolverContext,
        positive_restrictions: &[Space],
        negative_restriction: &[Space],
    ) -> SolverColorIterator {
        let solver = Self::make_fixed_points_solver(context);
        solver.assert_within_spaces(positive_restrictions);
        solver.assert_not_within_spaces(negative_restriction);
        SolverColorIterator::new_with_solver(context, solver)
    }

    /// Build a solver that is satisfied exactly by all combinations of fixed-point
    /// vertices and parameter valuations.
    ///
    /// This is mainly for building very custom fixed-point iterators, and you don't have to call
    /// it explicitly unless you really know that you need a custom solver.
    #[cfg(feature = "solver-z3")]
    pub fn make_fixed_points_solver(context: &BnSolverContext) -> BnSolver {
        // Make a solver with all static constraints applied.
        let solver = context.mk_network_solver();

        // Add a bunch of x <=> f(x) constraints to describe a fixed-point.
        for var in context.as_network().variables() {
            let var_is_true = context.var(var);
            let update_is_true = context.mk_update_function(var);

            let assertion = update_is_true.iff(var_is_true);
            solver.as_z3_solver().assert(&assertion);
        }

        solver
    }

    fn prepare_to_merge<E, F: Fn() -> Result<(), E>>(
        stg: &SymbolicAsyncGraph,
        log_level: usize,
        interrupt: &F,
    ) -> Result<Vec<Bdd>, E> {
        let mut to_merge = Vec::new();
        for var in stg.variables() {
            let can_step = stg.var_can_post(var, stg.unit_colored_vertices());
            let is_stable = stg.unit_colored_vertices().minus(&can_step);
            interrupt()?;

            if log_essential(log_level, is_stable.symbolic_size()) {
                println!(
                    " > Created initial set for {:?} using {} BDD nodes.",
                    var,
                    is_stable.symbolic_size()
                );
            }
            to_merge.push(is_stable.into_bdd());
        }
        Ok(to_merge)
    }
}

#[cfg(test)]
mod tests {
    use crate::biodivine_std::traits::Set;
    use crate::fixed_points::FixedPoints;
    use crate::symbolic_async_graph::SymbolicAsyncGraph;
    use crate::{BooleanNetwork, VariableId};

    #[test]
    pub fn simple_fixed_point_test() {
        let bn = BooleanNetwork::try_from_file("aeon_models/g2a_p9.aeon").unwrap();
        let stg = SymbolicAsyncGraph::new(&bn).unwrap();

        let naive = FixedPoints::naive_symbolic(&stg, stg.unit_colored_vertices());
        let symbolic = FixedPoints::symbolic(&stg, stg.unit_colored_vertices());
        let vertices = FixedPoints::symbolic_vertices(&stg, stg.unit_colored_vertices());
        let colors = FixedPoints::symbolic_colors(&stg, stg.unit_colored_vertices());

        assert!(naive.is_subset(&symbolic));
        assert!(symbolic.is_subset(&naive));

        let symbolic_colors = symbolic.colors();
        let symbolic_vertices = symbolic.vertices();

        assert!(symbolic_colors.is_subset(&colors));
        assert!(colors.is_subset(&symbolic_colors));
        assert!(symbolic_vertices.is_subset(&vertices));
        assert!(vertices.is_subset(&symbolic_vertices));

        let iterator = FixedPoints::symbolic_iterator(
            &stg,
            stg.unit_colored_vertices(),
            usize::from(stg.symbolic_context().bdd_variable_set().num_vars()) + 2,
        );

        let mut expected = symbolic;

        for set in iterator {
            assert!(set.is_subset(&expected));
            expected = expected.minus(&set);
        }

        assert!(expected.is_empty());
    }

    #[test]
    pub fn simple_projected_fixed_point_test() {
        let bn = BooleanNetwork::try_from_file("aeon_models/g2a_p9.aeon").unwrap();
        let stg = SymbolicAsyncGraph::new(&bn).unwrap();

        let ccr_m = bn.as_graph().find_variable("CcrM").unwrap();
        let dna = bn.as_graph().find_variable("DnaA").unwrap();

        // Compute how DnaA/CcrM fixed-points depend on the CcrM function.
        let projection = FixedPoints::symbolic_projection(
            &bn,
            &stg,
            stg.unit_colored_vertices(),
            &[ccr_m, dna],
            &[ccr_m],
        );

        // There are 4 fixed points. Two have CcrM=True and two have CcrM=False. The remaining
        // variables are false.

        assert_eq!(4, projection.iter().count());

        let mut has_true = false;
        let mut has_false = false;
        for (state, function) in projection.iter() {
            assert_eq!(1, function.len());
            // All functions should be non-trivial. That's all I've got.
            assert!(function[0].1.as_binary().is_some());
            assert_eq!((VariableId(2), false), state[1]);
            if state[0].1 {
                has_true = true;
            } else {
                has_false = true;
            }
        }
        assert!(has_true && has_false);
    }
}
