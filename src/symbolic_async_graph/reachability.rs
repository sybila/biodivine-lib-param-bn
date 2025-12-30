use crate::biodivine_std::traits::Set;
use crate::symbolic_async_graph::{GraphColoredVertices, SymbolicAsyncGraph};
use crate::{VariableId, global_log_level, log_essential, should_log};
use cancel_this::{Cancellable, is_cancelled};
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
        Self::_reach_basic_saturation(graph, initial, step, global_log_level()).unwrap()
    }

    /// A version of [Reachability::reach_basic_saturation] with cancellation
    /// and logging.
    ///
    /// Cancellation implemented using [cancel-this](https://crates.io/crates/cancel-this).
    /// For more information, see crate documentation.
    pub fn _reach_basic_saturation<F>(
        graph: &SymbolicAsyncGraph,
        initial: &GraphColoredVertices,
        step: F,
        log_level: usize,
    ) -> Cancellable<GraphColoredVertices>
    where
        F: Fn(&SymbolicAsyncGraph, &GraphColoredVertices, VariableId) -> GraphColoredVertices,
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
                is_cancelled!()?;
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
        Reachability::_reach(graph, initial, step, global_log_level()).unwrap()
    }

    /// A version of [Reachability::reach] with cancellation
    /// and logging.
    ///
    /// Cancellation implemented using [cancel-this](https://crates.io/crates/cancel-this).
    /// For more information, see crate documentation.
    pub fn _reach<F>(
        graph: &SymbolicAsyncGraph,
        initial: &GraphColoredVertices,
        step: F,
        log_level: usize,
    ) -> Cancellable<GraphColoredVertices>
    where
        F: Fn(&SymbolicAsyncGraph, &GraphColoredVertices, VariableId) -> GraphColoredVertices,
    {
        Self::_reach_basic_saturation(graph, initial, step, log_level)
        // Note: There used to be a fancy algorithm here, but it turns out it was not correct.
        // So for now, we just delegate to the basic implementation.
    }
}
