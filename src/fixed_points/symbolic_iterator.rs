use biodivine_lib_bdd::{Bdd, BddPartialValuation, BddVariableSet};
use crate::biodivine_std::traits::Set;
use crate::symbolic_async_graph::{GraphColoredVertices, SymbolicAsyncGraph};

pub struct RawSymbolicIterator<'a> {
    universe: &'a BddVariableSet,
    limit: usize,
    clauses: Vec<Bdd>,
    stack: Vec<(usize, Bdd, Vec<Bdd>)>
}

pub struct SymbolicIterator<'a> {
    stg: &'a SymbolicAsyncGraph,
    inner: RawSymbolicIterator<'a>
}

impl<'a> Iterator for RawSymbolicIterator<'a> {
    type Item = Bdd;

    fn next(&mut self) -> Option<Self::Item> {
        'main: loop {
            if let Some((mut next_clause, mut result, mut to_merge)) = self.stack.pop() {
                while !to_merge.is_empty() {

                    if result.is_false() {
                        // In some cases, the result may be empty. In that case, we can skip this
                        // branch and continue to the next item on stack.
                        continue 'main;
                    }

                    if result.size() > self.limit {
                        // Result is too large, we should try to split it first.
                        while next_clause < self.clauses.len() {
                            let clause = &self.clauses[next_clause];
                            next_clause += 1;

                            let result_with_clause = result.and(&clause);
                            let result_without_clause = result.and_not(&clause);

                            // If the clause is irrelevant, ignore it.
                            if result_with_clause.is_false() || result_without_clause.is_false() {
                                continue;
                            }

                            // If the results are too large, ignore the clause.
                            if result_with_clause.size() + result_without_clause.size() > 2 * result.size() {
                                continue;
                            }

                            // Branch on the clause, but make sure the smaller result
                            // is on top of the stack.
                            if result_with_clause.size() < result_without_clause.size() {
                                self.stack.push((next_clause, result_without_clause, to_merge.clone()));
                                self.stack.push((next_clause, result_with_clause, to_merge.clone()));
                            } else {
                                self.stack.push((next_clause, result_with_clause, to_merge.clone()));
                                self.stack.push((next_clause, result_without_clause, to_merge.clone()));
                            }

                            // Finally, restart the main loop with the new stack top.
                            continue 'main;
                        }
                        // All clauses have been exhausted, so let's just try to brute force
                        // the rest of the result.
                    }

                    // Find the best merge item to split on.
                    let mut best_result = self.universe.mk_false();
                    let mut best_size = usize::MAX;
                    let mut best_index = 0;

                    for (i, set) in to_merge.iter().enumerate() {
                        let bdd = Bdd::binary_op_with_limit(
                            best_size,
                            set,
                            &result,
                            biodivine_lib_bdd::op_function::and,
                        );
                        if let Some(bdd) = bdd {
                            // At this point, the size of the BDD should be smaller or equal to the
                            // best result, so we can just update it.
                            assert!(bdd.size() <= best_size);
                            best_result = bdd;
                            best_size = best_result.size();
                            best_index = i;
                        }
                    }

                    assert_ne!(best_size, usize::MAX);

                    result = best_result;
                    to_merge.remove(best_index);
                }

                // Finally, to_merge is empty and we can return the result (as long as it
                // is actually not empty).
                if result.is_false() {
                    continue 'main;
                } else {
                    return Some(result);
                }
            } else {
                // Everything is done.
                return None
            }
        }
    }
}

impl<'a> Iterator for SymbolicIterator<'a> {
    type Item = GraphColoredVertices;

    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next()
            .map(|bdd| {
                self.stg.empty_vertices().copy(bdd)
            })
    }
}

impl<'a> SymbolicIterator<'a> {

    pub fn new(stg: &'a SymbolicAsyncGraph, restriction: &GraphColoredVertices, limit: usize) -> SymbolicIterator<'a> {
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
        if !stg.unit_colored_vertices().is_subset(restriction) {
            to_merge.push(restriction.as_bdd().clone());
        }

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

        clauses.sort_by_cached_key(|clause| {
            clause.cardinality()
        });
        clauses.reverse();
        let clauses = clauses.into_iter()
            .map(|it| {
                stg.symbolic_context().bdd_variable_set().mk_conjunctive_clause(&it)
            })
            .collect::<Vec<_>>();

        SymbolicIterator {
            stg,
            inner: RawSymbolicIterator {
                universe: stg.symbolic_context().bdd_variable_set(),
                limit,
                clauses,
                stack: vec![(0, stg.symbolic_context().bdd_variable_set().mk_true(), to_merge)]
            }
        }
    }

}