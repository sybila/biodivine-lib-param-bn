//! This module contains algorithms and data structures for efficiently computing fixed-points
//! of large Boolean networks.
//!
//! There are two main approaches one can use to obtain the fixed-points:
//!
//!     1. A solver based method (relying on Z3). This method works well for enumerating
//!     small batches of fixed-points, but does not scale very well for very high numbers
//!     of fixed-points, as each of them has to be explicitly returned by the solver.
//!
//!     2. A symbolic BDD-based method. This approach generally suffers more from the state space
//!     explosion (it can take a long time for large networks), but if the number of results
//!     if very high, it can still outperform enumeration based on solvers.

use crate::biodivine_std::traits::Set;
use crate::symbolic_async_graph::{GraphColoredVertices, SymbolicAsyncGraph};
use crate::{BooleanNetwork, ParameterId, SdGraph, Sign, VariableId};
use std::collections::{HashMap, HashSet};
use crate::trap_spaces::{ExtendedBoolean, Space};

/// Aggregates algorithms for computing fixed point states of the given state-transition graph.
/// Typically, the operation can be also restricted to a particular subset of candidate states.
pub struct FixedPoints {
    _dummy: (),
}

impl FixedPoints {
    /// A naive algorithm that simply performs symbolic elimination of successor states in the
    /// reverse order of variable ordering.
    ///
    /// This is largely a "baseline" algorithm for symbolic computation and cannot really scale
    /// well to large networks.
    pub fn naive_bdd(
        stg: &SymbolicAsyncGraph,
        restriction: &GraphColoredVertices,
    ) -> GraphColoredVertices {
        let mut candidates = restriction.clone();
        if cfg!(feature = "print-progress") {
            println!(
                "Start naive fixed-point search with {}[nodes:{}] candidates.",
                candidates.approx_cardinality(),
                candidates.symbolic_size()
            );
        }
        for var in stg.as_network().variables().rev() {
            let can_step = stg.var_can_post(var, stg.unit_colored_vertices());
            candidates = candidates.minus(&can_step);

            if cfg!(feature = "print-progress") {
                println!(
                    " > [{}] Remaining: {}[nodes:{}] candidates.",
                    var.to_index(),
                    candidates.approx_cardinality(),
                    candidates.symbolic_size()
                );
            }
        }
        candidates
    }

    pub fn only_states(
        stg: &SymbolicAsyncGraph,
        restriction: &GraphColoredVertices
    ) -> GraphColoredVertices {
        let mut result = restriction.clone();

        let mut is_stable: Vec<GraphColoredVertices> = stg
            .as_network()
            .variables()
            .map(|it| {
                let item = stg.var_can_post(it, restriction);
                let mut item = restriction.minus(&item);
                for p in stg.symbolic_context().parameter_variables() {
                    item = item.copy(item.as_bdd().var_project(*p));
                }
                /*if cfg!(feature = "print-progress") {
                    println!(
                        " > Initial candidates for variable {}[id:{}]: {}[nodes:{}].",
                        stg.as_network().get_variable_name(it),
                        it.to_index(),
                        item.approx_cardinality(),
                        item.symbolic_size()
                    );
                }*/
                item
            })
            .collect();

        while is_stable.len() > 1 {
            is_stable.sort_by_key(|it| it.symbolic_size());
            is_stable.reverse();

            let item = is_stable.pop().unwrap();
            is_stable = is_stable
                .into_iter()
                .map(|it| it.intersect(&item))
                .collect();

            if cfg!(feature = "print-progress") {
                let mut total_cardinality = 0.0;
                let mut total_size = 0;
                for x in &is_stable {
                    total_cardinality += x.approx_cardinality();
                    total_size += x.symbolic_size();
                    //println!(" >>> {}", stg.expand_to_space(&x.vertices()));
                }

                println!(
                    " > [{}] Remaining states: {}[nodes:{}]",
                    is_stable.len(),
                    total_cardinality,
                    total_size
                );
            }
        }

        //let only_states = is_stable.pop().unwrap();

        let mut to_process = Vec::new();

        'expand: while !is_stable.is_empty() {
            let item = is_stable.pop().unwrap();

            let original_size = item.symbolic_size();
            //println!("Total: {}", only_states.symbolic_size());
            for var in stg.as_network().variables() {
                let positive_size = item.fix_network_variable(var ,true).symbolic_size();
                let negative_size = item.fix_network_variable(var, false).symbolic_size();
                if positive_size < 10 || negative_size < 10 {
                    continue;
                }
                //println!("Split by {:?}: {} / {}", var, positive_size, negative_size);
                let gain = (original_size as f64) / ((positive_size as f64 / 2.0) + (negative_size as f64 / 2.0));
                //println!("Split by {:?}: {} / {}. Gain: {}", var, positive_size, negative_size, gain);
                if gain > 2.0 {
                    is_stable.push(item.fix_network_variable(var, true));
                    is_stable.push(item.fix_network_variable(var, false));
                    println!("Expanding: {}", is_stable.len());
                    continue 'expand;
                }
            }

            println!("Forwarding..");
            to_process.push(item);
        }


        println!("Separated into {} partial results.", to_process.len());
        for (i, item) in to_process.into_iter().enumerate() {
            println!("Start partial item {}", i);
            let partial = Self::naive_bdd(stg, &item);
            println!("Partial: {} / {}", partial.approx_cardinality(), partial.symbolic_size());
        }

        stg.mk_empty_vertices()
    }

    /// Another "naive" algorithm that instead selects the "best" variable for transition
    /// elimination based on the size of the eliminated BDD.
    ///
    /// This often works surprisingly well for moderately sized networks, but the approach is
    /// "accidentally quadratic" and thus quickly becomes infeasible once the variable count
    /// is too large.
    pub fn naive_greedy_bdd(
        stg: &SymbolicAsyncGraph,
        restriction: &GraphColoredVertices,
    ) -> GraphColoredVertices {
        if cfg!(feature = "print-progress") {
            println!(
                "Start naive greedy fixed-point search with {}[nodes:{}] candidates.",
                restriction.approx_cardinality(),
                restriction.symbolic_size()
            );
        }

        let mut is_stable: Vec<GraphColoredVertices> = stg
            .as_network()
            .variables()
            .map(|it| {
                let item = stg.var_can_post(it, restriction);
                let item = restriction.minus(&item);
                /*if cfg!(feature = "print-progress") {
                    println!(
                        " > Initial candidates for variable {}[id:{}]: {}[nodes:{}].",
                        stg.as_network().get_variable_name(it),
                        it.to_index(),
                        item.approx_cardinality(),
                        item.symbolic_size()
                    );
                }*/
                item
            })
            .collect();

        while is_stable.len() > 1 {
            is_stable.sort_by_key(|it| it.symbolic_size());
            is_stable.reverse();

            let item = is_stable.pop().unwrap();
            is_stable = is_stable
                .into_iter()
                .map(|it| it.intersect(&item))
                .collect();

            if cfg!(feature = "print-progress") {
                let mut total_cardinality = 0.0;
                let mut total_size = 0;
                for x in &is_stable {
                    total_cardinality += x.approx_cardinality();
                    total_size += x.symbolic_size();
                    //println!(" >>> {}", stg.expand_to_space(&x.vertices()));
                }

                println!(
                    " > [{}] Remaining states: {}[nodes:{}]",
                    is_stable.len(),
                    total_cardinality,
                    total_size
                );
            }
        }

        is_stable.pop().unwrap()
    }

    pub fn greedy_recursive_2(
        stg: &SymbolicAsyncGraph,
        restriction: &GraphColoredVertices,
    ) -> GraphColoredVertices {

        fn rec(
            stg: &SymbolicAsyncGraph,
            mut to_merge: Vec<GraphColoredVertices>,
            depth: usize,
            mut split_vars: HashSet<VariableId>
        ) -> GraphColoredVertices {
            println!("Start iteration with {} nodes.", to_merge.iter().map(|it| it.symbolic_size()).sum::<usize>());
            let mut split_iter = Vec::from_iter(split_vars.iter().cloned());
            split_iter.sort();
            //let mut fixed_variables = HashSet::new();

            /*let mut subspaces: Vec<Space> = to_merge.iter()
                .map(|it| {
                    let space = stg.expand_to_space(&it.vertices());
                    println!(" >> {}", space);
                    space
                })
                .collect();

            while subspaces.len() > 1 {
                let x = subspaces.pop().unwrap();
                let y = subspaces.pop().unwrap();
                if let Some(x) = x.intersect(&y) {
                    subspaces.push(x);
                } else {
                    return stg.mk_empty_vertices();
                }
            }

            let subspace = subspaces.pop().unwrap();
            println!("Subspace: {}", subspace);*/
            if to_merge[0].is_empty() {
                return stg.mk_empty_vertices();
            }

            /*let subspace = stg.expand_to_space(&to_merge[0].vertices());

            for var in split_iter {
                if subspace[var] == ExtendedBoolean::One {
                    fixed_variables.insert((var, true));
                } else if subspace[var] == ExtendedBoolean::Zero {
                    fixed_variables.insert((var, false));
                }
            }*/

            /*for var in split_iter {
                let var_true = stg.fix_network_variable(var, true);
                let var_false = stg.fix_network_variable(var, false);
                for set in &to_merge {
                    if set.is_subset(&var_true) {
                        fixed_variables.insert((var, true));
                        //println!("Fixing {} to 1.", var.to_index());
                        /*let tt_merge: Vec<GraphColoredVertices> = to_merge.into_iter()
                            .map(|it| it.restrict_network_variable(var, true))
                            .collect();
                        let tt_stg = stg.fix_variable_in_graph(var, true);
                        split_vars.remove(&var);
                        return rec(&tt_stg, tt_merge, depth, split_vars)
                            .fix_network_variable(var, true);*/
                    }
                    if set.is_subset(&var_false) {
                        fixed_variables.insert((var, false));
                        //println!("Fixing {} to 0.", var.to_index());
                        /*let ff_merge: Vec<GraphColoredVertices> = to_merge.into_iter()
                            .map(|it| it.restrict_network_variable(var, false))
                            .collect();
                        let ff_stg = stg.fix_variable_in_graph(var, false);
                        split_vars.remove(&var);
                        return rec(&ff_stg, ff_merge, depth, split_vars)
                            .fix_network_variable(var, false);*/
                    }
                }
                println!("Done {}.", var.to_index());
            }*/

            /*println!("Fix {} variables.", fixed_variables.len());
            if !fixed_variables.is_empty() {
                let mut stg = stg.clone();
                for (var, value) in fixed_variables.clone() {
                    to_merge = to_merge.into_iter()
                        .map(|it| it.restrict_network_variable(var, value))
                        .collect();
                    stg = stg.fix_variable_in_graph(var, value);
                    split_vars.remove(&var);
                    println!("Fixed {}={}.", var.to_index(), value);
                }
                let mut result = rec(&stg, to_merge, depth, split_vars);

                if result.is_empty() {
                    return result;
                }

                println!("Result: {}", result.symbolic_size());
                for (var, value) in fixed_variables.clone() {
                    result = result.fix_network_variable(var, value);
                    println!("Result: {}", result.symbolic_size());
                }

                return result;
            }*/

            while to_merge.len() > 1 {
                to_merge.sort_by_key(|it| it.symbolic_size());
                to_merge.reverse();

                let total_size: usize = to_merge.iter().map(|it| it.symbolic_size()).sum();

                println!("Bound: {} > {}", total_size/to_merge.len(), 10_000 * (depth * depth * depth * depth));
                if total_size/to_merge.len() > 10_000 * (depth * depth * depth * depth) && split_vars.len() > 0 && to_merge.len() > 2 {
                    let mut sizes = vec![0usize; stg.symbolic_context().bdd_variable_set().num_vars() as usize];
                    for x in &to_merge {
                        let size = x.as_bdd().size_per_variable();
                        for i in 0..size.len() {
                            sizes[i] += size[i]
                        }
                    }
                    println!("Size: {:?}", sizes);
                    let all_variables = stg.symbolic_context().bdd_variable_set().variables();
                    let (_, split_var) = stg.symbolic_context().state_variables()
                        .iter()
                        .zip(stg.as_network().variables())
                        .max_by_key(|(it, _)| {
                            let index: usize = all_variables.iter().position(|x| *it == x).unwrap();
                            sizes[index]
                        })
                        .unwrap();
                    //let mut split_vec: Vec<VariableId> = split_vars.iter().cloned().collect();
                    //split_vec.sort();
                    //let split_var = split_vec[split_vec.len() / 2];
                    //let split_var = split_vars.iter().max().cloned().unwrap();
                    split_vars.remove(&split_var);

                    println!("Branching {} to 1.", split_var.to_index());
                    let tt_merge: Vec<GraphColoredVertices> = to_merge.iter()
                        .map(|it| it.restrict_network_variable(split_var, true))
                        .collect();
                    let tt_stg = stg.fix_variable_in_graph(split_var, true);
                    let _tt_result = rec(&tt_stg, tt_merge, depth + 1, split_vars.clone())
                        .fix_network_variable(split_var, true);

                    println!("Branching {} to 0.", split_var.to_index());
                    let ff_merge: Vec<GraphColoredVertices> = to_merge.iter()
                        .map(|it| it.restrict_network_variable(split_var, false))
                        .collect();
                    let ff_stg = stg.fix_variable_in_graph(split_var, false);
                    let _ff_result = rec(&ff_stg, ff_merge, depth + 1, split_vars.clone())
                        .fix_network_variable(split_var, false);

                    return stg.mk_empty_vertices();//tt_result.union(&ff_result);
                }

                let item = to_merge.pop().unwrap();

                if item.is_empty() {
                    println!("Empty.");
                    return item;
                }

                to_merge = to_merge
                    .into_iter()
                    .map(|it| it.intersect(&item))
                    .collect();

                if cfg!(feature = "print-progress") {
                    let mut total_cardinality = 0.0;
                    let mut total_size = 0;
                    for x in &to_merge {
                        total_cardinality += x.approx_cardinality();
                        total_size += x.symbolic_size();
                        //println!(" >>> {}", stg.expand_to_space(&x.vertices()));
                    }

                    println!(
                        " > [{}] Remaining states: {}[nodes:{}]",
                        to_merge.len(),
                        total_cardinality,
                        total_size
                    );
                }
            }

            let result = to_merge.pop().unwrap();
            println!("Result: {}", result.symbolic_size());
            result
        }

        let mut to_merge = stg
            .as_network()
            .variables()
            .filter_map(|it| {
                let item = stg.var_can_post(it, restriction);
                if item.is_empty() {
                    None
                } else {
                    let item = restriction.minus(&item);
                    let clauses = item.as_bdd().sat_clauses().count();
                    println!("Clauses: {}", clauses);
                    Some((item, clauses))
                }
            })
            .collect::<Vec<_>>();

        to_merge.sort_by_key(|(_,x)| *x);

        while to_merge.len() > 1 {
            let (x, cx) = to_merge.pop().unwrap();
            to_merge = to_merge.into_iter()
                .map(|(y, _)| {
                    let z = x.intersect(&y);
                    let cz = z.as_bdd().sat_clauses().count();
                    (z, cz)
                })
                .collect();
            //let (y, cy) = to_merge.pop().unwrap();
            //let z = x.intersect(&y);
            //let cz = z.as_bdd().sat_clauses().count();
            //println!("Clauses: {} + {} = {}", cx, cy, cz);
            //to_merge.push((z, cz));
            to_merge.sort_by_key(|(_,x)| *x);
            to_merge.reverse();
            let sizes = to_merge.iter().map(|(x, it)| (x.symbolic_size(), *it)).collect::<Vec<_>>();
            println!("Sizes: {:?}", sizes);
            let total_clauses = sizes.iter().map(|(_, x)| *x).sum::<usize>();
            let total_nodes = sizes.iter().map(|(x, _)| *x).sum::<usize>();
            println!("[{}] Total nodes {}, total clauses {}", to_merge.len(),total_nodes, total_clauses);
            if total_clauses > 10_000_000 {
                break;
            }
        }


        let mut to_merge: Vec<GraphColoredVertices> = to_merge.into_iter().map(|(it, _)| it).collect();

        /*while to_merge.len() > 1 {
            to_merge.sort_by_key(|it| it.symbolic_size());
            to_merge.reverse();

            let item = to_merge.pop().unwrap();
            to_merge = to_merge
                .into_iter()
                .map(|it| it.intersect(&item))
                .collect();

            if cfg!(feature = "print-progress") {
                let mut total_cardinality = 0.0;
                let mut total_size = 0;
                for x in &to_merge {
                    total_cardinality += x.approx_cardinality();
                    total_size += x.symbolic_size();
                    //println!(" >>> {}", stg.expand_to_space(&x.vertices()));
                }

                println!(
                    " > [{}] Remaining states: {}[nodes:{}]",
                    to_merge.len(),
                    total_cardinality,
                    total_size
                );

                if total_size > 10_000_000 {
                    let mut sizes = vec![0usize; stg.symbolic_context().bdd_variable_set().num_vars() as usize];
                    for x in &to_merge {
                        let size = x.as_bdd().size_per_variable();
                        for i in 0..size.len() {
                            sizes[i] += size[i]
                        }
                    }
                    println!("Size: {:?}", sizes);
                    let all_variables = stg.symbolic_context().bdd_variable_set().variables();
                    let (_, split_var) = stg.symbolic_context().state_variables()
                        .iter()
                        .zip(stg.as_network().variables())
                        .max_by_key(|(it, _)| {
                            let index: usize = all_variables.iter().position(|x| *it == x).unwrap();
                            sizes[index]
                        })
                        .unwrap();

                    let item = stg.var_can_post(split_var, restriction);
                    let item = restriction.minus(&item);
                    println!("Original: {:?}", to_merge.iter().map(|it| it.symbolic_size()).collect::<Vec<_>>());
                    for clause in item.as_bdd().sat_clauses() {
                        let clause_bdd = stg.symbolic_context().bdd_variable_set().mk_conjunctive_clause(&clause);
                        let transformed: Vec<usize> = to_merge.iter()
                            .map(|it| {
                                let mut result = it.as_bdd().clone();
                                for x in clause.clone().to_values() {
                                    result = result.var_restrict(x.0, x.1);
                                }
                                result = result.var_project(stg.symbolic_context().get_state_variable(split_var));
                                //it.as_bdd().and(&clause).size()
                                result.size()
                            })
                            .collect();
                        println!("Sizes: {:?} / {}", transformed, transformed.iter().cloned().sum::<usize>());
                    }

                    panic!();
                }
            }
        }*/

        let variables = HashSet::from_iter(stg.as_network().variables());

        return rec(stg, to_merge, 1, variables);
    }

    pub fn greedy_recursive(
        stg: &SymbolicAsyncGraph,
        restriction: &GraphColoredVertices,
        branch_variables: &[VariableId],
        depth: usize,
    ) -> GraphColoredVertices {
        if cfg!(feature = "print-progress") {
            println!(
                "Start naive greedy fixed-point search with {}[nodes:{}] candidates.",
                restriction.approx_cardinality(),
                restriction.symbolic_size()
            );
            println!("{}", stg.expand_to_space(&restriction.vertices()));
        }

        let mut is_stable: Vec<GraphColoredVertices> = stg
            .as_network()
            .variables()
            .filter_map(|it| {
                let item = stg.var_can_post(it, restriction);
                if item.is_empty() {
                    None
                } else {
                    Some(restriction.minus(&item))
                }
            })
            /*.map(|it| {
                let item = stg.var_can_post(it, restriction);
                let item = restriction.minus(&item);
                /*if cfg!(feature = "print-progress") {
                    println!(
                        " > Initial candidates for variable {}[id:{}]: {}[nodes:{}].",
                        stg.as_network().get_variable_name(it),
                        it.to_index(),
                        item.approx_cardinality(),
                        item.symbolic_size()
                    );
                }*/
                item
            })
            .filter(|it| !restriction.is_subset(it))
             */
            .collect();

        if is_stable.is_empty() {
            return restriction.clone();
        }

        while is_stable.len() > 1 {

            is_stable.sort_by_key(|it| it.symbolic_size());
            is_stable.reverse();

            let max_size: usize = is_stable[0].symbolic_size();
            let total_size: usize = is_stable.iter().map(|it| it.symbolic_size()).sum();

            //if (max_size > 1_00_000 && total_size > 10_000_000) && branch_variables.len() > 0 {
            println!("Bound: {} > {}", total_size/is_stable.len(), 100_000 * (depth * depth));
            if total_size/is_stable.len() > 100_000 * (depth * depth) && branch_variables.len() > 0 {
                let new_restriction = is_stable.pop().unwrap();
                let split_var = branch_variables[0];

                println!("Splitting on {:?}", split_var);

                //let tt_set = new_restriction.fix_network_variable(split_var, true);
                let tt_set = new_restriction.restrict_network_variable(split_var, true);
                let tt_stg = stg.fix_variable_in_graph(split_var, true);

                let tt = if !tt_set.is_empty() {
                    Self::greedy_recursive(
                        &tt_stg,
                        &tt_set,
                        &branch_variables[1..],
                        depth + 1
                    ).fix_network_variable(split_var, true)
                } else {
                    stg.mk_empty_vertices()
                };

                //let ff_set = new_restriction.fix_network_variable(split_var, false);
                let ff_set = new_restriction.restrict_network_variable(split_var, false);
                let ff_stg = stg.fix_variable_in_graph(split_var, false);

                let ff = if !ff_set.is_empty() {
                    Self::greedy_recursive(
                        &ff_stg,
                        &ff_set,
                        &branch_variables[1..],
                        depth + 1
                    ).fix_network_variable(split_var, false)
                } else {
                    stg.mk_empty_vertices()
                };

                return tt.union(&ff);
            }

            let item = is_stable.pop().unwrap();

            if item.is_empty() {
                return item;
            }

            is_stable = is_stable
                .into_iter()
                .map(|it| it.intersect(&item))
                .collect();

            if cfg!(feature = "print-progress") {
                let mut total_cardinality = 0.0;
                let mut total_size = 0;
                for x in &is_stable {
                    total_cardinality += x.approx_cardinality();
                    total_size += x.symbolic_size();
                    //println!(" >>> {}", stg.expand_to_space(&x.vertices()));
                }

                println!(
                    " > [{}] Remaining states: {}[nodes:{}]",
                    is_stable.len(),
                    total_cardinality,
                    total_size
                );
            }
        }

        is_stable.pop().unwrap()
    }

    pub fn greedy(
        stg: &SymbolicAsyncGraph,
        restriction: &GraphColoredVertices
    ) -> GraphColoredVertices {
        let mut candidates: HashMap<VariableId, GraphColoredVertices> = stg.as_network()
            .variables()
            .map(|it| {
                let item = stg.var_can_post(it, restriction);
                let item = stg.unit_colored_vertices().minus(&item);
                (it, item)
            })
            .collect();

        while candidates.len() > 1 {
            let mut best_var = VariableId::from_index(0);
            let mut best_size = usize::MAX;
            for (var, set) in &candidates {
                if set.symbolic_size() < best_size {
                    best_var = *var;
                    best_size = set.symbolic_size();
                }
            }

            let item = candidates.remove(&best_var).unwrap();

            for target in stg.as_network().targets(best_var) {
                if let Some(set) = candidates.get_mut(&target) {
                    *set = set.intersect(&item);
                }
            }

            if cfg!(feature = "print-progress") {
                let mut total_cardinality = 0.0;
                let mut total_size = 0;
                for (_, x) in &candidates {
                    total_cardinality += x.approx_cardinality();
                    total_size += x.symbolic_size();
                }

                println!(
                    " > [{}] Remaining states: {}[nodes:{}]",
                    candidates.len(),
                    total_cardinality,
                    total_size
                );
            }
        }

        candidates.into_iter().next().unwrap().1
    }

    /// Structural symbolic algorithm picks variables for elimination based on the regulatory
    /// graph of the network.
    ///
    /// In particular, it first tries to perform "constant propagation" on as many variables
    /// as possible. Then, it picks one of the remaining cycles and resolves it completely,
    /// potentially resulting in more variables that can be resolved through constant propagation.
    ///
    /// This algorithm seems to actually perform reasonably well even on networks that are quite
    /// large or that have a non-trivial amount of inputs. At the very least, it is better than
    /// naive solver-based approaches when dealing with large number of parameters.
    pub fn structural_bdd(
        stg: &SymbolicAsyncGraph,
        restriction: &GraphColoredVertices,
    ) -> GraphColoredVertices {
        let sd_graph = SdGraph::from(stg.as_network().as_graph());
        let unit_set = stg.unit_colored_vertices();

        let mut candidates = restriction.clone();
        let mut candidate_vars = HashSet::from_iter(stg.as_network().variables());

        /// Tests whether the variable (`var`) has some regulators within the `restriction`
        /// subset of `network` variables.
        fn has_regulator(
            network: &BooleanNetwork,
            restriction: &HashSet<VariableId>,
            var: VariableId,
        ) -> bool {
            network
                .as_graph()
                .regulators(var)
                .into_iter()
                .any(|it| restriction.contains(&it))
        }

        while !candidate_vars.is_empty() {
            // Find all variables where every regulator is already resolved.
            let input_variables: Vec<VariableId> = candidate_vars
                .iter()
                .filter(|it| !has_regulator(stg.as_network(), &candidate_vars, **it))
                .cloned()
                .collect();

            if !input_variables.is_empty() {
                // If the set is not empty, try to propagate the values of these "constant"
                // variables to their successors.
                let mut steps = stg.mk_empty_vertices();
                for x in input_variables {
                    steps = steps.union(&stg.var_can_post(x, unit_set));
                    candidate_vars.remove(&x);
                }
                candidates = candidates.minus(&steps);
            } else {
                // If there are no variables that can do constant propagation, find the shortest
                // cycle and eliminate all variables on that cycle.
                unimplemented!()
            }
        }

        candidates
    }

    pub fn trap_2(
        stg: &SymbolicAsyncGraph,
        candidates: &GraphColoredVertices
    ) {
        let mut ratios: Vec<(VariableId, f64)> = stg.as_network().variables()
            .map(|var| {
                let true_trap = candidates.fix_network_variable(var, true);
                let true_trap = forward_closed(stg, &true_trap);

                let false_trap = candidates.fix_network_variable(var, false);
                let false_trap = forward_closed(stg, &false_trap);

                let ratio = true_trap.approx_cardinality() / false_trap.approx_cardinality();
                println!("Variable {} ratio = {}", var.to_index(), ratio);
                (var, ratio)
            })
            .collect();

        ratios.sort_by(|(_,x), (_,y)| x.total_cmp(y));

        let (best, _) = ratios.pop().unwrap();

        println!("Branch {} = true", best);
        Self::trap_2(stg, &candidates.fix_network_variable(best, true));
        println!("Branch {} = false", best);
        Self::trap_2(stg, &candidates.fix_network_variable(best, false));
    }

    pub fn trap_recursive(
        stg: &SymbolicAsyncGraph,
        restriction: &GraphColoredVertices
    ) {
        let mut ratios: Vec<(VariableId, f64)> = stg.as_network().variables()
            .map(|var| {
                let true_trap = stg.fix_network_variable(var, true);
                let true_trap = forward_closed(stg, &true_trap);

                let false_trap = stg.fix_network_variable(var, false);
                let false_trap = forward_closed(stg, &false_trap);

                let ratio = true_trap.approx_cardinality() / false_trap.approx_cardinality();
                println!("Variable {} ratio = {}", var.to_index(), ratio);
                (var, ratio)
            })
            .collect();

        ratios.sort_by(|(_,x), (_,y)| x.total_cmp(y));

        let mut is_stable: Vec<GraphColoredVertices> = stg
            .as_network()
            .variables()
            .map(|it| {
                let item = stg.var_can_post(it, restriction);
                let item = restriction.minus(&item);
                if cfg!(feature = "print-progress") {
                    println!(
                        " > Initial candidates for variable {}[id:{}]: {}[nodes:{}].",
                        stg.as_network().get_variable_name(it),
                        it.to_index(),
                        item.approx_cardinality(),
                        item.symbolic_size()
                    );
                }
                item
            })
            .collect();

        fn rec(
            stg: &SymbolicAsyncGraph,
            mut is_stable: Vec<GraphColoredVertices>,
            mut ratios: Vec<(VariableId, f64)>,
            depth: usize,
        ) {
            while is_stable.len() > 1 {
                is_stable.sort_by_key(|it| it.symbolic_size());
                is_stable.reverse();

                let item = is_stable.pop().unwrap();

                if item.is_empty() {
                    println!("Empty branch.");
                    return;
                }

                is_stable = is_stable
                    .into_iter()
                    .map(|it| it.intersect(&item))
                    .collect();

                let mut total_cardinality = 0.0;
                let mut total_size = 0;
                for x in &is_stable {
                    total_cardinality += x.approx_cardinality();
                    total_size += x.symbolic_size();
                    //println!(" >>> {}", stg.expand_to_space(&x.vertices()));
                }

                if total_size >= 100_000_000 && is_stable.len() > 2 {

                    println!(
                        " > [{}] Remaining states: {}[nodes:{}]",
                        is_stable.len(),
                        total_cardinality,
                        total_size
                    );

                    let (split_var, ratio) = ratios.pop().unwrap();

                    println!("[{}] Branch {}=false with ratio {}.", depth, split_var.to_index(), ratio);
                    let ff_stable = is_stable.iter()
                        .map(|it| it.fix_network_variable(split_var, false))
                        .collect();
                    rec(&stg, ff_stable, ratios.clone(), depth+1);
                    println!("[{}] Branch {}=true with ratio {}.", depth, split_var.to_index(), ratio);
                    let tt_stable = is_stable.iter()
                        .map(|it| it.fix_network_variable(split_var, true))
                        .collect();
                    rec(&stg, tt_stable, ratios.clone(), depth+1);
                    return;
                }
            }

            let sinks = is_stable.pop().unwrap();
            println!("Found {} sinks with {} nodes.", sinks.approx_cardinality(), sinks.symbolic_size());
        }

        rec(stg, is_stable, ratios, 0);

        unimplemented!()
    }
}

impl SymbolicAsyncGraph {
    pub fn fixed_points_2(&self) -> GraphColoredVertices {
        let sd_graph = SdGraph::from(self.as_network().as_graph());
        let mut candidate_states = self.mk_unit_colored_vertices();
        let mut remaining_vars: HashSet<VariableId> = self.as_network().variables().collect();
        while !remaining_vars.is_empty() {
            let initial: Vec<VariableId> = remaining_vars
                .iter()
                .filter(|it| {
                    // Retain only initial states (with respect to remaining_vars).
                    !self
                        .as_network()
                        .regulators(**it)
                        .into_iter()
                        .any(|it| remaining_vars.contains(&it))
                })
                .cloned()
                .collect();
            if !initial.is_empty() {
                let mut initial_steps = self.mk_empty_vertices();
                for x in initial {
                    let step = self.var_can_post(x, self.unit_colored_vertices());
                    initial_steps = initial_steps.union(&step);
                    remaining_vars.remove(&x);
                    println!("Initial BDD: {}", initial_steps.symbolic_size());
                }
                candidate_states = candidate_states.minus(&initial_steps);
                println!(
                    "New candidates[{}]: {} / {}",
                    remaining_vars.len(),
                    candidate_states.symbolic_size(),
                    candidate_states.approx_cardinality()
                );
            } else {
                let mut best_cycle = Vec::new();
                let mut best_cycle_length = usize::MAX;

                // Ensures determinism.
                let mut remaining_iter: Vec<VariableId> = remaining_vars.iter().cloned().collect();
                remaining_iter.sort();
                for pivot in remaining_iter {
                    if let Some(cycle) =
                        sd_graph.shortest_cycle(&remaining_vars, pivot, best_cycle_length)
                    {
                        best_cycle_length = cycle.len();
                        best_cycle = cycle;
                    }
                }

                println!("Found cycle: {:?}", best_cycle);
                let mut cycle_steps = self.mk_empty_vertices();
                for x in best_cycle {
                    let step = self.var_can_post(x, self.unit_colored_vertices());
                    cycle_steps = cycle_steps.union(&step);
                    remaining_vars.remove(&x);
                    println!("Cycle BDD: {}", cycle_steps.symbolic_size());
                }
                candidate_states = candidate_states.minus(&cycle_steps);
                println!(
                    "New candidates[{}]: {} / {}",
                    remaining_vars.len(),
                    candidate_states.symbolic_size(),
                    candidate_states.approx_cardinality()
                );
            }
        }
        return candidate_states;
    }

    pub fn fixed_points(&self) -> GraphColoredVertices {
        fn fixed_points_recursive(
            stg: &SymbolicAsyncGraph,
            sd_graph: &SdGraph,
            mut var_restriction: HashSet<VariableId>,
        ) -> GraphColoredVertices {
            let mut best_pivot = VariableId::from_index(0);
            let mut best_cycle_length = usize::MAX;
            for var in &var_restriction {
                let best_cycle_in_var =
                    sd_graph.shortest_cycle_length(&var_restriction, *var, best_cycle_length);
                if let Some(length) = best_cycle_in_var {
                    best_pivot = *var;
                    best_cycle_length = length;
                }
            }

            println!(
                "Weak components: {}",
                sd_graph
                    .restricted_weakly_connected_components(&var_restriction)
                    .len()
            );
            if best_cycle_length == usize::MAX {
                // There are no more cycles within `var_restriction`. Let's just
                // try to evaluate the fixed-points symbolically.
                let mut candidates = stg.mk_unit_colored_vertices();
                'propagation: while !var_restriction.is_empty() {
                    let mut initial = HashSet::new();
                    for var in var_restriction.clone() {
                        let remaining_regulators = stg
                            .as_network()
                            .as_graph()
                            .regulators(var)
                            .into_iter()
                            .filter(|it| var_restriction.contains(it))
                            .count();
                        if remaining_regulators == 0 {
                            initial.insert(var);
                        }
                    }

                    println!("Total initial variables: {}", initial.len());
                    /*let mut best_candidate = initial.iter().next().cloned().unwrap();
                    let mut best_candidate_size = usize::MAX;
                    for x in &initial {
                        let can_step = stg.var_can_post(*x, &candidates);
                        candidates = candidates.minus(&can_step);
                        if candidates.symbolic_size() < best_candidate_size {
                            best_candidate = *x;
                            best_candidate_size = candidates.symbolic_size();
                        }
                    }*/

                    let best_candidate = initial.into_iter().max().unwrap();

                    let can_step = stg.var_can_post(best_candidate, &candidates);
                    candidates = candidates.minus(&can_step);
                    println!(
                        "Candidates[{}]: {}/{}",
                        var_restriction.len(),
                        candidates.symbolic_size(),
                        candidates.approx_cardinality()
                    );
                    var_restriction.remove(&best_candidate);
                    //continue 'propagation;
                }
                /*for var in &var_restriction {
                    let can_step = stg.var_can_post(*var, &candidates);
                    candidates = candidates.minus(&can_step);
                    println!("Candidates: {}/{}", candidates.symbolic_size(), candidates.approx_cardinality());
                }*/
                return candidates;
            }

            var_restriction.remove(&best_pivot);

            println!("Branch on: {:?}", best_pivot);

            let inner_candidates = fixed_points_recursive(stg, sd_graph, var_restriction);

            println!(
                "Inner candidates: {}/{}",
                inner_candidates.symbolic_size(),
                inner_candidates.approx_cardinality()
            );

            let can_step = stg.var_can_post(best_pivot, &inner_candidates);
            return inner_candidates.minus(&can_step);
        }

        let variables: HashSet<VariableId> = self.as_network().variables().collect();
        let sd_graph = SdGraph::from(self.as_network().as_graph());
        return fixed_points_recursive(self, &sd_graph, variables);
    }
}


/// Compute the largest forward closed subset of the `initial` set. That is, the states that can
/// only reach states inside `initial`.
///
/// In particular, if the initial set is a weak basin, the result is a strong basin.
pub fn forward_closed(
    graph: &SymbolicAsyncGraph,
    initial: &GraphColoredVertices,
) -> GraphColoredVertices {
    let mut i = 0;
    let mut basin = initial.clone();
    loop {
        i += 1;
        let mut stop = true;
        for var in graph.as_network().variables().rev() {
            let can_go_out = graph.var_can_post_out(var, &basin);
            //let outside_successors = graph.var_post(var, &basin).minus(&basin);
            //let can_go_out = graph.var_pre(var, &outside_successors).intersect(&basin);

            if !can_go_out.is_empty() {
                basin = basin.minus(&can_go_out);
                stop = false;
                break;
            }
        }
        if basin.as_bdd().size() > 10_000 {
            //println!("Skip");
            //return graph.mk_empty_vertices();
            println!("Forward closed progress: {}", basin.as_bdd().size())
        }
        if stop {
            //println!("I: {}", i);
            return basin;
        }
    }
}


struct Context {
    z3: z3::Context,
}
