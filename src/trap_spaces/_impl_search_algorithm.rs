use crate::trap_spaces::OptionalExtendedBoolean::{Any, One, Unknown, Zero};
use crate::trap_spaces::{PartialSpace, Space};
use crate::{BooleanNetwork, SdGraph, VariableId};
use std::collections::HashSet;

impl BooleanNetwork {
    pub fn minimal_trap_spaces(&self) -> Vec<Space> {
        let mut fvs: Vec<VariableId> = self.graph.feedback_vertex_set().into_iter().collect();
        fvs.sort();
        minimal_trap_search(
            self,
            &SdGraph::from(self.as_graph()),
            PartialSpace::new_unknown(self),
            &fvs,
            &mut HashSet::new(),
        )
    }

    pub fn restricted_minimal_trap_spaces(&self, _restriction: &Space) -> Vec<Space> {
        unimplemented!()
    }
}

/// Find all trap spaces that are minimal among the spaces that the given `candidate` partial
/// space can specialize to.
///
/// In other words, the function searches spaces that can be created from `candidate`
/// by restricting variables with "unknown" values to either "zero", "one", or "any". As such,
/// the result is not guaranteed to be minimal globally, but only within the possible
/// specializations of the given `candidate`.
fn minimal_trap_search(
    network: &BooleanNetwork,
    sd_graph: &SdGraph,
    candidate: PartialSpace,
    fvs: &Vec<VariableId>,
    conflicts: &mut HashSet<Space>,
) -> Vec<Space> {
    // (1) Propagate all any values that we can (also called "percolation").
    let candidate = candidate.constant_propagation(network);

    // (2) Check if there is a conflicting variable. If yes, the whole space is transient
    // and there cannot be any trap space in it.
    if let Some(conflict) = candidate.trap_conflict_variable(network) {
        //println!("Conflict: {:?}", conflict);
        if conflicts.insert(conflict) {
            println!(" > New! {}", conflicts.len());
        }
        return Vec::new();
    }

    // (3) Check if there are still unknown variables. If everything is known, this is either
    // a trap space, or it is not. Either way we are done.
    if let Some(space) = candidate.try_as_space() {
        return if space.is_trap_space(network) {
            vec![space]
        } else {
            Vec::new()
        };
    }

    //let space = candidate.clone().to_space();
    let mut candidate = candidate;
    let mut restart = 0;
    for conflict in conflicts.iter() {
        if candidate.try_subtract(conflict) {
            //println!("Simplify by conflict: {}", candidate);
            restart += 1;
        }
    }
    if restart > 0 {
        println!("Resolved: {}", restart);
        return minimal_trap_search(network, sd_graph, candidate, fvs, conflicts);
    }

    //println!("Test {}", candidate);

    // (4) Try to see if the graph of remaining unknown variables is strongly connected. If not,
    // search for the smallest top SCC that we can exploit to decompose the problem.
    let unknown_variables = candidate.unknown_variables();
    if let Some(top_scc) = minimal_top_scc(sd_graph, unknown_variables.clone()) {
        if top_scc.len() > 10 {
            println!("Test SCC: {}", top_scc.len());
        }
        // (5a) If the SCC exists, fix every variable outside of the SCC to "any", and look for
        // minimal trap spaces in that specification.
        let mut inner_candidate = candidate.clone();
        for var in &unknown_variables {
            if !top_scc.contains(var) {
                inner_candidate[*var] = Any;
            }
        }

        let traps_in_subspace =
            minimal_trap_search(network, sd_graph, inner_candidate, fvs, conflicts);
        if top_scc.len() > 10 {
            println!("Found {} subspaces", traps_in_subspace.len());
        }

        // (6a) Afterwards, try to extend each result with results for the
        // remaining unknown variables.
        let mut result = Vec::new();
        for candidate in traps_in_subspace {
            let mut candidate = candidate.to_partial_space();
            for var in &unknown_variables {
                if !top_scc.contains(var) {
                    candidate[*var] = Unknown;
                }
            }

            result.append(&mut minimal_trap_search(
                network, sd_graph, candidate, fvs, conflicts,
            ));
        }

        result
    } else {
        // (5b) Find a variable that belongs to the shortest cycle in the space
        // of unknown variables.
        //let var = variable_with_shortest_cycle(sd_graph, unknown_variables.clone()).unwrap(); // The variable must exist because unknown variables are an SCC.
        let var = {
            *fvs.iter()
                .find(|it| unknown_variables.contains(*it))
                .unwrap()
        };

        if unknown_variables.len() > 10 {
            println!("Branch on {:?}", var);
        }

        // (6b) Branch on this variable, considering all three possible known values in its place.
        let mut result = Vec::new();
        let mut candidate = candidate.clone();

        candidate[var] = One;
        result.append(&mut minimal_trap_search(
            network,
            sd_graph,
            candidate.clone(),
            fvs,
            conflicts,
        ));

        candidate[var] = Zero;
        result.append(&mut minimal_trap_search(
            network,
            sd_graph,
            candidate.clone(),
            fvs,
            conflicts,
        ));

        candidate[var] = Any;
        'inner: for trap in
            minimal_trap_search(network, sd_graph, candidate.clone(), fvs, conflicts)
        {
            // These results do not have to be minimal with respect to results of previous
            // calls, we thus have to test them to see if they are truly relevant.
            for existing in &result {
                if existing < &trap {
                    continue 'inner;
                }
            }

            result.push(trap);
        }

        result
    }
}

/// Compute the minimal top SCC of the given `SdGraph` restricted to the given `universe`. If the
/// whole graph is strongly connected, returns `None`.
///
/// Note that the top SCC can be trivial, however this is not generally expected in this context
/// because constant propagation should eliminate trivial SCCs.
fn minimal_top_scc(
    sd_graph: &SdGraph,
    universe: HashSet<VariableId>,
) -> Option<HashSet<VariableId>> {
    let initial_size = universe.len();
    let mut remaining = universe;

    let mut best_scc = HashSet::new();
    let mut best_scc_size = usize::MAX;

    while !remaining.is_empty() {
        // Minimum ensures the result is deterministic.
        let pivot = *remaining.iter().min().unwrap();

        let fwd = sd_graph.restricted_forward_reachable(&remaining, HashSet::from([pivot]));
        let bwd = sd_graph.restricted_backward_reachable(&remaining, HashSet::from([pivot]));

        // Everything in FWD is either this component, or not a top component,
        // hence we can remove it.
        remaining.retain(|it| !fwd.contains(it));

        if bwd.is_subset(&fwd) {
            // BWD is a top component and we can try to report it.
            if bwd.len() < best_scc_size {
                best_scc_size = bwd.len();
                best_scc = bwd;
            }
        }
    }

    if best_scc_size == initial_size {
        None
    } else {
        Some(best_scc)
    }
}
