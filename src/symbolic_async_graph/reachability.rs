use crate::biodivine_std::traits::Set;
use crate::symbolic_async_graph::{GraphColoredVertices, SymbolicAsyncGraph};
use crate::{VariableId, global_log_level, log_essential, never_stop, should_log};
use std::cmp::max;

pub struct Reachability {
    _dummy: (),
}

impl Reachability {
    /// A FWD reachability procedure that uses "structural saturation".
    pub fn reach_fwd(
        graph: &SymbolicAsyncGraph,
        initial: &GraphColoredVertices,
    ) -> GraphColoredVertices {
        Self::reach(graph, initial, |g, s, v| g.var_post_out(v, s))
    }

    /// A BWD reachability procedure that uses "structural saturation".
    pub fn reach_bwd(
        graph: &SymbolicAsyncGraph,
        initial: &GraphColoredVertices,
    ) -> GraphColoredVertices {
        Self::reach(graph, initial, |g, s, v| g.var_pre_out(v, s))
    }

    /// "Basic" saturation FWD reachability procedure.
    pub fn reach_fwd_basic(
        graph: &SymbolicAsyncGraph,
        initial: &GraphColoredVertices,
    ) -> GraphColoredVertices {
        Self::reach_basic_saturation(graph, initial, |g, s, v| g.var_post_out(v, s))
    }

    /// "Basic" saturation BWD reachability procedure.
    pub fn reach_bwd_basic(
        graph: &SymbolicAsyncGraph,
        initial: &GraphColoredVertices,
    ) -> GraphColoredVertices {
        Self::reach_basic_saturation(graph, initial, |g, s, v| g.var_pre_out(v, s))
    }

    /// A basic saturation procedure which performs reachability over all transition functions of a graph.
    pub fn reach_basic_saturation<
        F: Fn(&SymbolicAsyncGraph, &GraphColoredVertices, VariableId) -> GraphColoredVertices,
    >(
        graph: &SymbolicAsyncGraph,
        initial: &GraphColoredVertices,
        step: F,
    ) -> GraphColoredVertices {
        Self::_reach_basic_saturation(graph, initial, step, global_log_level(), &never_stop)
            .unwrap()
    }

    /// A version of [Reachability::reach_basic_saturation] with cancellation
    /// and logging.
    pub fn _reach_basic_saturation<F, I, E>(
        graph: &SymbolicAsyncGraph,
        initial: &GraphColoredVertices,
        step: F,
        log_level: usize,
        interrupt: &I,
    ) -> Result<GraphColoredVertices, E>
    where
        F: Fn(&SymbolicAsyncGraph, &GraphColoredVertices, VariableId) -> GraphColoredVertices,
        I: Fn() -> Result<(), E>,
    {
        if should_log(log_level) {
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
                interrupt()?;
                if !step.is_empty() {
                    result = result.union(&step);
                    max_size = max(max_size, result.symbolic_size());

                    if log_essential(log_level, result.symbolic_size()) {
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

            if should_log(log_level) {
                println!(
                    "Basic reachability done: {}[nodes:{}] candidates. Max intermediate size: {}.",
                    result.approx_cardinality(),
                    result.symbolic_size(),
                    max_size
                );
            }

            return Ok(result);
        }
    }

    /// A "structural" reachability procedure which uses the dependencies between the update functions to reduce
    /// the number of transitions that need to be tested.
    ///
    /// This sometimes increases the size of the BDDs a little bit, but is overall beneficial in the vast majority
    /// of cases.
    pub fn reach<
        F: Fn(&SymbolicAsyncGraph, &GraphColoredVertices, VariableId) -> GraphColoredVertices,
    >(
        graph: &SymbolicAsyncGraph,
        initial: &GraphColoredVertices,
        step: F,
    ) -> GraphColoredVertices {
        Reachability::_reach(graph, initial, step, global_log_level(), &never_stop).unwrap()
    }

    /// A version of [Reachability::reach] with cancellation
    /// and logging.
    pub fn _reach<F, E, I>(
        graph: &SymbolicAsyncGraph,
        initial: &GraphColoredVertices,
        step: F,
        log_level: usize,
        interrupt: &I,
    ) -> Result<GraphColoredVertices, E>
    where
        F: Fn(&SymbolicAsyncGraph, &GraphColoredVertices, VariableId) -> GraphColoredVertices,
        I: Fn() -> Result<(), E>,
    {
        Self::_reach_basic_saturation(graph, initial, step, log_level, interrupt)

        // TODO:
        //   The algorithm below is useful, but apparently not always complete. We need to
        //   fix this in the subsequent releases.

        /*if should_log(log_level) {
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

        interrupt()?;

        let mut result = initial.clone();
        let mut max_size = 0;

        // A set of saturated variables. We can only remove a variable from here if it's regulator has been changed.
        let mut saturated = HashSet::new();
        'reach: loop {
            for var in graph.variables().rev() {
                let next_step = step(graph, &result, var);
                interrupt()?;

                if next_step.is_empty() {
                    saturated.insert(var);
                } else {
                    result = result.union(&next_step);
                    max_size = max(max_size, result.symbolic_size());

                    if log_essential(log_level, result.symbolic_size()) {
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

            if should_log(log_level) {
                println!(
                    "Structural reachability done: {}[nodes:{}] candidates. Max intermediate size: {}.",
                    result.approx_cardinality(),
                    result.symbolic_size(),
                    max_size
                );
            }

            return Ok(result);
        }*/
    }
}
