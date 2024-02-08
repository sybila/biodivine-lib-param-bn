use crate::_impl_regulatory_graph::signed_directed_graph::{SdGraph, Sign};
use crate::{never_stop, should_log, VariableId, LOG_NOTHING};
use std::collections::HashSet;

impl SdGraph {
    /// Find all non-trivial strongly connected components of this `SdGraph`.
    ///
    /// The result is sorted by component size.
    pub fn strongly_connected_components(&self) -> Vec<HashSet<VariableId>> {
        self.restricted_strongly_connected_components(&self.mk_all_vertices())
    }

    /// Find all non-trivial strongly connected components in the given `restriction` of this `SdGraph`.
    ///
    /// The result is sorted by component size.
    pub fn restricted_strongly_connected_components(
        &self,
        restriction: &HashSet<VariableId>,
    ) -> Vec<HashSet<VariableId>> {
        self._restricted_strongly_connected_components(restriction, LOG_NOTHING, &never_stop)
            .unwrap()
    }

    /// A version of [SdGraph::restricted_strongly_connected_components] with cancellation
    /// and logging.
    pub fn _restricted_strongly_connected_components<E, F: Fn() -> Result<(), E>>(
        &self,
        restriction: &HashSet<VariableId>,
        log_level: usize,
        interrupt: &F,
    ) -> Result<Vec<HashSet<VariableId>>, E> {
        let mut results = Vec::new();
        scc_recursive(
            self,
            restriction.clone(),
            &mut results,
            log_level,
            interrupt,
        )?;
        results.sort_by_key(|it| it.len());
        Ok(results)
    }
}

/// **(internal)** A recursive procedure for finding non-trivial SCCs in a restricted state space.
///
/// The complexity of the procedure is $n^2$. It can be (in theory) improved to $n \cdot log(n)$,
/// but at the moment I don't really see a benefit to it as it is still sufficiently fast for
/// most reasonable cases.
fn scc_recursive<E, F: Fn() -> Result<(), E>>(
    graph: &SdGraph,
    mut universe: HashSet<VariableId>,
    results: &mut Vec<HashSet<VariableId>>,
    log_level: usize,
    interrupt: &F,
) -> Result<(), E> {
    trim_trivial(&graph.successors, &mut universe);
    interrupt()?;
    trim_trivial(&graph.predecessors, &mut universe);
    interrupt()?;

    if universe.is_empty() {
        return Ok(());
    }

    let pivot = universe.iter().next().cloned().unwrap();

    let fwd = graph.restricted_forward_reachable(&universe, HashSet::from([pivot]));
    interrupt()?;

    let bwd = graph.restricted_backward_reachable(&universe, HashSet::from([pivot]));
    interrupt()?;

    let fwd_or_bwd: HashSet<VariableId> = fwd.union(&bwd).cloned().collect();
    let fwd_and_bwd: HashSet<VariableId> = fwd.intersection(&bwd).cloned().collect();

    if is_non_trivial(graph, &fwd_and_bwd) {
        if should_log(log_level) {
            println!("Found SCC with {} nodes.", fwd_or_bwd.len());
        }
        results.push(fwd_and_bwd);
    }

    let universe_rest: HashSet<VariableId> = universe.difference(&fwd_or_bwd).cloned().collect();
    let fwd_rest: HashSet<VariableId> = fwd.difference(&bwd).cloned().collect();
    let bwd_rest: HashSet<VariableId> = bwd.difference(&fwd).cloned().collect();

    if !universe_rest.is_empty() {
        scc_recursive(graph, universe_rest, results, log_level, interrupt)?;
    }

    if !fwd_rest.is_empty() {
        scc_recursive(graph, fwd_rest, results, log_level, interrupt)?;
    }

    if !bwd_rest.is_empty() {
        scc_recursive(graph, bwd_rest, results, log_level, interrupt)?;
    }

    Ok(())
}

/// **(internal)** Check if an SCC is trivial.
///
/// Note that this does not verify that the set is an actual SCC. It just checks for self-loops
/// on single-state SCCs.
fn is_non_trivial(graph: &SdGraph, scc: &HashSet<VariableId>) -> bool {
    if scc.len() > 1 {
        true
    } else {
        // Check if the vertex has a self-loop.
        let state = scc.iter().cloned().next().unwrap();
        graph.successors[state.to_index()]
            .iter()
            .any(|(x, _)| *x == state)
    }
}

/// **(internal)** Remove all vertices from `set` that can be trivially shown to be outside
/// of any cycle using the given `edge` set.
///
/// Note that this does not eliminate *all* trivial SCCs, just a part of them that can be detected
/// using this particular method.
fn trim_trivial(edges: &[Vec<(VariableId, Sign)>], set: &mut HashSet<VariableId>) {
    let mut continue_trimming = true;
    while continue_trimming {
        continue_trimming = false;
        for x in set.clone() {
            let non_trivial = edges[x.to_index()].iter().any(|(x, _)| set.contains(x));
            if !non_trivial {
                set.remove(&x);
                continue_trimming = true;
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::_impl_regulatory_graph::_impl_misc::tests::build_test_regulatory_graph;
    use crate::_impl_regulatory_graph::signed_directed_graph::SdGraph;
    use std::collections::HashSet;

    #[test]
    pub fn test_scc_decomposition() {
        // See method for high-level graph description.
        let rg = build_test_regulatory_graph();

        let _a = rg.find_variable("a").unwrap(); // 'a' is a trivial component.
        let b_1 = rg.find_variable("b_1").unwrap();
        let b_2 = rg.find_variable("b_2").unwrap();
        let c = rg.find_variable("c").unwrap();
        let d_1 = rg.find_variable("d_1").unwrap();
        let d_2 = rg.find_variable("d_2").unwrap();
        let d_3 = rg.find_variable("d_3").unwrap();
        let e = rg.find_variable("e").unwrap();

        let graph = SdGraph::from(&rg);

        let scc = graph.strongly_connected_components();
        assert_eq!(scc.len(), 3);
        assert_eq!(scc[0], HashSet::from([e]));
        assert_eq!(scc[1], HashSet::from([b_1, b_2]));
        assert_eq!(scc[2], HashSet::from([d_1, d_2, d_3]));

        let scc =
            graph.restricted_strongly_connected_components(&HashSet::from([d_1, d_2, c, b_1, e]));
        assert_eq!(scc.len(), 2);
        assert_eq!(scc[0], HashSet::from([e]));
        assert_eq!(scc[1], HashSet::from([d_1, d_2]));
    }
}
