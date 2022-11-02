//! This module contains algorithms and data structures for efficiently computing fixed-points
//! of large Boolean networks.
//!
//! There are two main approaches one can use to obtain the fixed-points:
//!
//! 1. A solver based method (relying on Z3). This method works well for enumerating
//!     small batches of fixed-points, but does not scale very well for high numbers
//!     of fixed-points, as each of them has to be explicitly returned by the solver.
//!
//! 2. A symbolic BDD-based method. This approach generally suffers more from the state space
//!     explosion (it can take a long time for large networks), but if the number of results
//!     if very high, it can still outperform enumeration based on solvers. Also, it can be
//!     easily restricted to arbitrary symbolic sets,

use crate::biodivine_std::traits::Set;
use crate::symbolic_async_graph::{GraphColoredVertices, SymbolicAsyncGraph};
use crate::{BooleanNetwork, ParameterId, SdGraph, Sign, VariableId};
use crate::symbolic_async_graph::{GraphColors, GraphVertices};
use crate::{BinaryOp, FnUpdate};
use biodivine_lib_bdd::{Bdd, BddPartialValuation, BddVariable, BddVariableSet};
use std::collections::{HashMap, HashSet};
use std::slice::SliceIndex;
use z3::ast::{Ast, Dynamic};
use z3::{ast, FuncDecl, Sort};

pub use symbolic_iterator::SymbolicIterator;

/// **(internal)** Implements the iterator used by `FixedPoints::symbolic_iterator`.
mod symbolic_iterator;

pub struct FixedPoints {
    _dummy: (),
}

/// Aggregates algorithms for computing fixed point states of the given state-transition graph.
/// Typically, the operation can be also restricted to a particular subset of candidate states.
pub struct FixedPoints2 {
    _dummy: (),
}

impl FixedPoints2 {
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
            .as_network()
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
        if cfg!(feature = "print-progress") {
            println!(
                "Start symbolic fixed-point search with {}[nodes:{}] candidates.",
                restriction.approx_cardinality(),
                restriction.symbolic_size()
            );
        }

        let mut to_merge: Vec<Bdd> = stg
            .as_network()
            .variables()
            .map(|var| {
                let can_step = stg.var_can_post(var, stg.unit_colored_vertices());
                let is_stable = stg.unit_colored_vertices().minus(&can_step);
                if cfg!(feature = "print-progress") {
                    println!(
                        " > Created initial set for {:?} using {} BDD nodes.",
                        var,
                        is_stable.symbolic_size()
                    );
                }
                is_stable.into_bdd()
            })
            .collect();

        /*
           Note to self: There is actually a marginally faster version of this algorithm that
           does not throw away the intermediate results but instead carries them over to the
           next iteration. Nevertheless, this version also wastes much more memory, as all
           results have to be preserved, so I ultimately decided not to use it.
        */

        // Finally add the global requirement on the whole state space, if it is relevant.
        if !stg.unit_colored_vertices().is_subset(&restriction) {
            to_merge.push(restriction.as_bdd().clone());
        }

        let fixed_points = Self::symbolic_merge(
            stg.symbolic_context().bdd_variable_set(),
            to_merge,
            HashSet::default(),
        );

        let fixed_points = stg.unit_colored_vertices().copy(fixed_points);

        if cfg!(feature = "print-progress") {
            println!(
                "Found {}[nodes:{}] fixed-points.",
                fixed_points.approx_cardinality(),
                fixed_points.symbolic_size(),
            );
        }

        fixed_points
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
        mut project: HashSet<BddVariable>,
    ) -> Bdd {
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
                    .filter(|(_, set)| set.contains(&bdd_var))
                    .map(|(id, _)| *id)
                    .collect::<HashSet<usize>>();
                (*bdd_var, dependencies)
            })
            .collect();

        let mut result = universe.mk_true();
        let mut merged = HashSet::new();

        /*
           Note to self: It seems that not all projections are always beneficial to the BDD size.
           At the same time, a non-optimal merge may enable a very useful projection. It is
           not entirely clear how to greedily apply these two observations. Ideally, we'd like
           to prioritize merges that lead to projections, but this is not universally true.

           Maybe we could at least greedily prefer merging sets that will immediately lead to
           projections? But even this is not an entirely clear win.
        */

        'merge: while !to_merge.is_empty() || !project.is_empty() {
            for p_var in project.clone() {
                let dependencies = dependency_map.get(&p_var).unwrap();
                if dependencies.is_subset(&merged) {
                    result = result.var_project(p_var);
                    project.remove(&p_var);

                    if cfg!(feature = "print-progress") {
                        println!(" > Projection. New result has {} BDD nodes. Remaining projections: {}.",
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
            merge_iter.reverse();

            for i in merge_iter {
                let set = &to_merge[&i];
                let bdd = Bdd::binary_op_with_limit(
                    best_result_size,
                    set,
                    &result,
                    biodivine_lib_bdd::op_function::and,
                );
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
                    return universe.mk_false();
                }

                if cfg!(feature = "print-progress") {
                    println!(
                        " > Merge. New result has {} BDD nodes. Remaining constraints: {}.",
                        result.size(),
                        to_merge.len(),
                    );
                }
            }
        }

        if cfg!(feature = "print-progress") {
            println!("Merge finished with {} BDD nodes.", result.size(),);
        }

        // All projection variables are indeed gone.
        assert!(project.is_empty());
        // And everything was merged.
        assert_eq!(merged.len(), support_sets.len());

        result
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
        if cfg!(feature = "print-progress") {
            println!(
                "Start symbolic fixed-point vertex search with {}[nodes:{}] candidates.",
                restriction.approx_cardinality(),
                restriction.symbolic_size()
            );
        }

        let mut to_merge: Vec<Bdd> = stg
            .as_network()
            .variables()
            .map(|var| {
                let can_step = stg.var_can_post(var, stg.unit_colored_vertices());
                let is_stable = stg.unit_colored_vertices().minus(&can_step);
                if cfg!(feature = "print-progress") {
                    println!(
                        " > Created initial set for {:?} using {} BDD nodes.",
                        var,
                        is_stable.symbolic_size()
                    );
                }
                is_stable.into_bdd()
            })
            .collect();

        // Finally add the global requirement on the whole state space, if it is relevant.
        if !stg.unit_colored_vertices().is_subset(&restriction) {
            to_merge.push(restriction.as_bdd().clone());
        }

        let mut project: HashSet<BddVariable> = stg
            .symbolic_context()
            .parameter_variables()
            .iter()
            .cloned()
            .collect();

        let bdd =
            Self::symbolic_merge(stg.symbolic_context().bdd_variable_set(), to_merge, project);

        let vertices = stg.empty_vertices().vertices().copy(bdd);

        if cfg!(feature = "print-progress") {
            println!(
                "Found {}[nodes:{}] fixed-point vertices.",
                vertices.approx_cardinality(),
                vertices.symbolic_size(),
            );
        }

        vertices
    }

    /// Similar to `Self::symbolic_vertices`, but only returns colors for which there exists
    /// at least one fixed-point within `restriction`.
    pub fn symbolic_colors(
        stg: &SymbolicAsyncGraph,
        restriction: &GraphColoredVertices,
    ) -> GraphColors {
        if cfg!(feature = "print-progress") {
            println!(
                "Start symbolic fixed-point color search with {}[nodes:{}] candidates.",
                restriction.approx_cardinality(),
                restriction.symbolic_size()
            );
        }

        let mut to_merge: Vec<Bdd> = stg
            .as_network()
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
                is_stable.into_bdd()
            })
            .collect();

        // Finally add the global requirement on the whole state space, if it is relevant.
        if !stg.unit_colored_vertices().is_subset(&restriction) {
            to_merge.push(restriction.as_bdd().clone());
        }

        let mut project: HashSet<BddVariable> = stg
            .symbolic_context()
            .state_variables()
            .iter()
            .cloned()
            .collect();

        let bdd =
            Self::symbolic_merge(stg.symbolic_context().bdd_variable_set(), to_merge, project);

        let colors = stg.empty_vertices().colors().copy(bdd);

        if cfg!(feature = "print-progress") {
            println!(
                "Found {}[nodes:{}] fixed-point colors.",
                colors.approx_cardinality(),
                colors.symbolic_size(),
            );
        }

        colors
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
    ///     compute the result than `Self::symbolic` (assuming you actually free the yielded
    ///     results or store them outside of the main memory).
    ///
    /// 2. While the runtime of the whole algorithm is typically longer, it should usually
    ///     take less time to get the *first* item than fully running `Self::symbolic`. Also,
    ///     you can often "tune" this time-to-first-answer using the `size_limit`, as smaller
    ///     results tend to be faster to find (iterating over all of them is longer though).
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
    pub fn symbolic_iterator(
        stg: &SymbolicAsyncGraph,
        restriction: &GraphColoredVertices,
        size_limit: usize,
    ) {
        todo!()
    }

    /// Constructs an iterator that enumerates all fixed-points within the given
    /// `restriction` subset using the Z3 solver.
    ///
    /// Similar notes on the `restriction` set as for `Self::symbolic_iterator` apply.
    /// However, also note that the set has to be translated to a Boolean expression for
    /// use in Z3, so try to avoid using too complicated BDDs here.
    ///
    /// Note that this method works very well for finding small numbers of fixed-points,
    /// but since the fixed-points are computed individually, it cannot really enumerate
    /// all fixed-points of models with a lot of parameters.
    ///
    /// However, you can use it to sample the space of possible fixed-points using various
    /// values for the `restriction` set.
    pub fn solver_iterator(stg: &SymbolicAsyncGraph, restriction: &GraphColoredVertices) {
        todo!()
    }
}

impl FixedPoints {
    pub fn conflict_clause(stg: &SymbolicAsyncGraph, restriction: &GraphColoredVertices) {
        let mut clauses: Vec<BddPartialValuation> = stg
            .as_network()
            .variables()
            .flat_map(|it| {
                let can_step = stg.var_can_post(it, restriction);
                let is_stable = restriction.minus(&can_step);
                let clauses = is_stable
                    .as_bdd()
                    .sat_clauses()
                    .take(100)
                    .collect::<Vec<_>>()
                    .into_iter();
                clauses
            })
            .collect();

        fn has_conflict(
            stg: &SymbolicAsyncGraph,
            cx: &BddPartialValuation,
            cy: &BddPartialValuation,
        ) -> bool {
            for var in stg.symbolic_context().bdd_variable_set().variables() {
                if cx.has_value(var) && cy.has_value(var) && cx.get_value(var) != cy.get_value(var)
                {
                    return true;
                }
            }
            return false;
        }

        let cloned = clauses.clone();
        println!("There are {} clauses.", clauses.len());
        // Sort clauses such that the most conflicting one is the last.
        clauses.sort_by_cached_key(|clause| {
            /*cloned.iter()
            .filter(|it| has_conflict(stg, clause, it))
            .count()*/
            //clause.to_values()[0].0
            //clause.last_fixed_variable().unwrap()
            clause.cardinality()
        });
        clauses.reverse();
        /*for clause in &clauses {
            let conflicts = clauses.iter()
                .filter(|it| has_conflict(stg, clause, it))
                .count();
            println!("Clause of card. {} has {} conflicts.", clause.cardinality(), conflicts);
        }*/

        let mut is_stable: Vec<GraphColoredVertices> = stg
            .as_network()
            .variables()
            .map(|it| {
                let can_step = stg.var_can_post(it, restriction);
                restriction.minus(&can_step)
            })
            .collect();

        fn rec(
            stg: &SymbolicAsyncGraph,
            mut is_stable: Vec<GraphColoredVertices>,
            clauses: &[BddPartialValuation],
        ) {
            while is_stable.len() > 1 {
                is_stable.sort_by_key(|it| it.symbolic_size());
                is_stable.reverse();

                let mut total_cardinality = 0.0;
                let mut total_size = 0;
                for x in &is_stable {
                    total_cardinality += x.approx_cardinality();
                    total_size += x.symbolic_size();
                    //println!(" >>> {}", stg.expand_to_space(&x.vertices()));
                }
                let average = total_size / is_stable.len();

                println!(
                    " > [{}] Remaining states: {}[nodes:{}]; avr. {}",
                    is_stable.len(),
                    total_cardinality,
                    total_size,
                    average
                );

                if average > 200_000 {
                    println!("Start splitting.");
                    let mut clause_index = 0;
                    while clause_index < clauses.len() {
                        let clause = &clauses[clause_index];
                        let clause_bdd = stg
                            .symbolic_context()
                            .bdd_variable_set()
                            .mk_conjunctive_clause(&clause);
                        let clause_set = stg.unit_colored_vertices().copy(clause_bdd);

                        let with_clause: Vec<GraphColoredVertices> = is_stable
                            .iter()
                            .map(|it| it.intersect(&clause_set))
                            .collect();

                        let with_clause_has_empty = with_clause.iter().any(|it| it.is_empty());
                        if with_clause_has_empty {
                            //println!("No fixed-point has this clause. Continue without it.");
                            clause_index += 1;
                            continue;
                            //return rec(stg, minus_clause, &clauses[clause_index+1..]);
                        }

                        let minus_clause: Vec<GraphColoredVertices> =
                            is_stable.iter().map(|it| it.minus(&clause_set)).collect();

                        let minus_clause_has_empty = minus_clause.iter().any(|it| it.is_empty());
                        if minus_clause_has_empty {
                            //println!("All fixed-points have this clause. Continue with it.");
                            //return rec(stg, with_clause, &clauses[clause_index+1..]);
                            clause_index += 1;
                            continue;
                        }

                        let with_clause_total = with_clause
                            .iter()
                            .map(|it| it.symbolic_size())
                            .sum::<usize>();
                        let minus_clause_total = minus_clause
                            .iter()
                            .map(|it| it.symbolic_size())
                            .sum::<usize>();
                        let with_clause_average = with_clause_total / with_clause.len();
                        let minus_clause_average = minus_clause_total / minus_clause.len();
                        println!("Split to {} / {}", with_clause_total, minus_clause_total);

                        //if with_clause_average > 150_000 || minus_clause_average > 150_000 || with_clause_total + minus_clause_total > total_size + total_size {
                        if with_clause_average > 200_000
                            || minus_clause_average > 200_000
                            || with_clause_total + minus_clause_total > total_size + total_size
                        {
                            println!("Split is bigger than current result. Skip clause. Remaining clauses: {}", clauses.len() - clause_index - 1);
                        } else {
                            println!("Split is useful... start with clause.");
                            rec(stg, with_clause, &clauses[clause_index + 1..]);
                            println!("Continue split without clause...");
                            rec(stg, minus_clause, &clauses[clause_index + 1..]);
                            return;
                        }
                        clause_index += 1;
                    }
                    panic!("Nothing to split on.");
                } else {
                    let item = is_stable.pop().unwrap();
                    if item.is_empty() {
                        println!("Empty.");
                        return;
                    }
                    is_stable = is_stable
                        .into_iter()
                        .map(|it| it.intersect(&item))
                        .collect();
                }
            }

            let sinks = is_stable.pop().unwrap();
            println!(
                "Found fixed points: {} / {}",
                sinks.approx_cardinality(),
                sinks.symbolic_size()
            );
        }

        rec(stg, is_stable, &clauses);
    }

}

struct Context {
    z3: z3::Context,
}

struct MyContext<'ctx> {
    pub ctx: &'ctx Context,
    pub e_bool: (Sort<'ctx>, Vec<FuncDecl<'ctx>>, Vec<FuncDecl<'ctx>>),
    pub variables: Vec<FuncDecl<'ctx>>,
}

impl<'ctx> MyContext<'ctx> {
    pub fn new(z3: &'ctx Context, network: &BooleanNetwork) -> Self {
        let sort = Sort::enumeration(&z3.z3, "ebool".into(), &["0".into(), "1".into(), "*".into()]);
        let constructors = network
            .variables()
            .map(|it| {
                let name = network.get_variable_name(it);
                FuncDecl::new::<&str>(&z3.z3, name.as_str(), &[], &sort.0)
            })
            .collect();
        MyContext {
            ctx: z3,
            e_bool: sort,
            variables: constructors,
        }
    }

    pub fn is_zero(&self, x: &dyn ast::Ast<'ctx>) -> ast::Bool<'ctx> {
        self.e_bool.2[0].apply(&[x]).as_bool().unwrap()
    }

    pub fn is_one(&self, x: &dyn ast::Ast<'ctx>) -> ast::Bool<'ctx> {
        self.e_bool.2[1].apply(&[x]).as_bool().unwrap()
    }

    pub fn is_star(&self, x: &dyn ast::Ast<'ctx>) -> ast::Bool<'ctx> {
        self.e_bool.2[2].apply(&[x]).as_bool().unwrap()
    }

    pub fn mk_zero(&self) -> Dynamic {
        self.e_bool.1[0].apply(&[])
    }

    pub fn mk_one(&self) -> Dynamic {
        self.e_bool.1[1].apply(&[])
    }

    pub fn mk_star(&self) -> Dynamic {
        self.e_bool.1[2].apply(&[])
    }

    pub fn e_bool_and(&self, left: &dyn ast::Ast<'ctx>, right: &dyn ast::Ast<'ctx>) -> Dynamic {
        let left_is_one = self.is_one(left);
        let right_is_one = self.is_one(right);
        let left_is_zero = self.is_zero(left);
        let right_is_zero = self.is_zero(right);
        let left_and_right_is_zero = left_is_zero & right_is_zero;
        let left_or_right_is_one = left_is_one | right_is_one;
        /*
           if left == One or right == One {
               One
           } else if left == Zero and right == Zero {
               Zero
           } else {
               Star
           }
        */
        let x = left_and_right_is_zero.ite(&self.mk_zero(), &self.mk_star());
        let x = left_or_right_is_one.ite(&self.mk_one(), &x);
        x
    }

    pub fn e_bool_or(&self, left: &dyn ast::Ast<'ctx>, right: &dyn ast::Ast<'ctx>) -> Dynamic {
        let left_is_one = self.is_one(left);
        let right_is_one = self.is_one(right);
        let left_is_zero = self.is_zero(left);
        let right_is_zero = self.is_zero(right);
        let left_or_right_is_zero = left_is_zero | right_is_zero;
        let left_and_right_is_one = left_is_one & right_is_one;
        /*
           if left == Zero or right == Zero {
               Zero
           } else if left == One and right == One {
               One
           } else {
               Star
           }
        */
        let x = left_and_right_is_one.ite(&self.mk_one(), &self.mk_star());
        let x = left_or_right_is_zero.ite(&self.mk_zero(), &x);
        x
    }

    pub fn e_bool_not(&self, inner: &dyn ast::Ast<'ctx>) -> Dynamic {
        let inner_is_one = self.is_one(inner);
        let inner_is_zero = self.is_zero(inner);
        let x = inner_is_zero.ite(&self.mk_one(), &self.mk_star());
        let x = inner_is_one.ite(&self.mk_zero(), &x);
        x
    }

    pub fn check_eq(&self, left: &ast::Datatype<'ctx>, right: &ast::Datatype<'ctx>) -> ast::Bool {
        left._eq(right)
    }
}
