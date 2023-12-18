use crate::biodivine_std::traits::Set;
use crate::symbolic_async_graph::{GraphColoredVertices, SymbolicAsyncGraph};
use crate::VariableId;
use std::cmp::max;
use std::collections::{HashMap, HashSet};

pub struct Reachability {
    _dummy: (),
}

impl Reachability {
    pub fn reach_fwd(
        graph: &SymbolicAsyncGraph,
        initial: &GraphColoredVertices,
    ) -> GraphColoredVertices {
        Self::reach(graph, initial, |g, s, v| g.var_post_out(v, s))
    }

    pub fn reach_bwd(
        graph: &SymbolicAsyncGraph,
        initial: &GraphColoredVertices,
    ) -> GraphColoredVertices {
        Self::reach(graph, initial, |g, s, v| g.var_pre_out(v, s))
    }

    pub fn reach_fwd_basic(
        graph: &SymbolicAsyncGraph,
        initial: &GraphColoredVertices,
    ) -> GraphColoredVertices {
        Self::reach_basic_saturation(graph, initial, |g, s, v| g.var_post_out(v, s))
    }

    pub fn reach_bwd_basic(
        graph: &SymbolicAsyncGraph,
        initial: &GraphColoredVertices,
    ) -> GraphColoredVertices {
        Self::reach_basic_saturation(graph, initial, |g, s, v| g.var_pre_out(v, s))
    }

    pub fn reach_basic_saturation<
        F: Fn(&SymbolicAsyncGraph, &GraphColoredVertices, VariableId) -> GraphColoredVertices,
    >(
        graph: &SymbolicAsyncGraph,
        initial: &GraphColoredVertices,
        step: F,
    ) -> GraphColoredVertices {
        if cfg!(feature = "print-progress") {
            println!(
                "Start basic symbolic reachability with {}[nodes:{}] candidates.",
                initial.approx_cardinality(),
                initial.symbolic_size()
            );
        }

        let mut result = initial.clone();

        let mut max_size = 0;

        'reach: loop {
            for var in graph.variables().rev() {
                let step = step(graph, &result, var);
                if !step.is_empty() {
                    result = result.union(&step);
                    max_size = max(max_size, result.symbolic_size());

                    if cfg!(feature = "print-progress") {
                        let current = result.approx_cardinality();
                        let max = graph.unit_colored_vertices().approx_cardinality();
                        println!(
                            " >> Reach progress: {}[nodes:{}] candidates ({:.2} log-%).",
                            result.approx_cardinality(),
                            result.symbolic_size(),
                            (current.log2() / max.log2()) * 100.0
                        );
                    }

                    continue 'reach;
                }
            }

            if cfg!(feature = "print-progress") {
                println!(
                    "Basic reachability done: {}[nodes:{}] candidates. Max intermediate size: {}.",
                    result.approx_cardinality(),
                    result.symbolic_size(),
                    max_size
                );
            }

            return result;
        }
    }

    /// Use [`SymbolicAsyncGraph::restrict`] to limit the reachability search to a particular
    /// subgraph.
    pub fn reach<
        F: Fn(&SymbolicAsyncGraph, &GraphColoredVertices, VariableId) -> GraphColoredVertices,
    >(
        graph: &SymbolicAsyncGraph,
        initial: &GraphColoredVertices,
        step: F,
    ) -> GraphColoredVertices {
        if cfg!(feature = "print-progress") {
            println!(
                "Start symbolic reachability with {}[nodes:{}] candidates.",
                initial.approx_cardinality(),
                initial.symbolic_size()
            );
        }

        // Construct a symbolic regulators relation (this is more accurate than the normal regulatory graph,
        // and does not require an underlying Boolean network).
        let targets_of_var = graph
            .variables()
            .map(|regulator| {
                let targets = graph
                    .variables()
                    .filter(|var| {
                        let update = graph.get_symbolic_fn_update(*var);
                        let state_variable = graph.symbolic_context().get_state_variable(regulator);
                        update.support_set().contains(&state_variable)
                    })
                    .collect::<Vec<_>>();
                (regulator, targets)
            })
            .collect::<HashMap<_, _>>();

        let mut result = initial.clone();
        let mut max_size = 0;

        // A set of saturated variables. We can only remove a variable from here if it's regulator has been changed.
        let mut saturated = HashSet::new();
        'reach: loop {
            for var in graph.variables().rev() {
                let next_step = step(graph, &result, var);
                if next_step.is_empty() {
                    saturated.insert(var);
                } else {
                    result = result.union(&next_step);
                    max_size = max(max_size, result.symbolic_size());

                    if cfg!(feature = "print-progress") {
                        let current = result.approx_cardinality();
                        let max = graph.unit_colored_vertices().approx_cardinality();
                        println!(
                            " >> [{}/{} saturated] Reach progress: {}[nodes:{}] candidates ({:.2} log-%).",
                            saturated.len(),
                            graph.num_vars(),
                            result.approx_cardinality(),
                            result.symbolic_size(),
                            (current.log2() / max.log2()) * 100.0
                        );
                    }

                    if !saturated.contains(&var) {
                        for t in &targets_of_var[&var] {
                            saturated.remove(t);
                        }
                        continue 'reach;
                    }
                }
            }

            if cfg!(feature = "print-progress") {
                println!(
                    "Basic reachability done: {}[nodes:{}] candidates. Max intermediate size: {}.",
                    result.approx_cardinality(),
                    result.symbolic_size(),
                    max_size
                );
            }

            return result;
        }
    }
}
