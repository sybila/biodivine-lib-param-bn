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
use crate::{BooleanNetwork, SdGraph, Sign, VariableId};
use std::collections::HashSet;

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
                let item = stg.unit_colored_vertices().minus(&item);
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

struct Context {
    z3: z3::Context,
}
