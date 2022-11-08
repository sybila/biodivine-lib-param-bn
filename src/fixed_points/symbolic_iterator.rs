use crate::biodivine_std::traits::Set;
use crate::symbolic_async_graph::{GraphColoredVertices, SymbolicAsyncGraph};
use biodivine_lib_bdd::{Bdd, BddPartialValuation, BddVariableSet};

/// **(internal)** An iterator that performs a conjunction of several `Bdd` objects but forks the
/// computation if the result becomes too large. It uses clauses from the initial BDDs to perform
/// the forking.
///
/// At the moment, it can only do normal conjunction, but hopefully in the future it should be
/// feasible to extend it such that it also performs projections and can be thus used for projected
/// enumeration. Also, in the future, we would probably like to modify the iterator such that
/// it provides a wide range of different results as soon as possible, as right now the returned
/// fixed-points will largely share similar properties dues to the way the forking works.
///
/// Also note that you can dynamically update the limit of the iterator, for example to increase it
/// gradually once enough results have been returned.
#[derive(Clone)]
pub struct RawSymbolicIterator<'a> {
    universe: &'a BddVariableSet,
    limit: usize,
    clauses: Vec<Bdd>,
    stack: Vec<(usize, Bdd, Vec<Bdd>)>,
}

/// An iterator that gradually returns all fixed-points of the given `SymbolicAsyncGraph`, but
/// tries to keep the intermediate results at the desired level by forking the computation into
/// multiple branches.
///
/// In general, this is slower than computing all fixed-points at once, but it should be much less
/// memory intensive. Also, it allows to compute a (relatively) large group of fixed-points
/// quickly by specifying a small limit and then increasing it gradually to cover more results.
#[derive(Clone)]
pub struct SymbolicIterator<'a> {
    stg: &'a SymbolicAsyncGraph,
    inner: RawSymbolicIterator<'a>,
}

impl<'a> Iterator for RawSymbolicIterator<'a> {
    type Item = Bdd;

    fn next(&mut self) -> Option<Self::Item> {
        'main: loop {
            if let Some((mut next_clause, mut result, mut to_merge)) = self.stack.pop() {
                if cfg!(feature = "print-progress") {
                    println!(
                        "Resume search with {} BDD nodes, {} constraints, and {} branches.",
                        result.size(),
                        to_merge.len(),
                        self.stack.len() + 1,
                    );
                }

                while !to_merge.is_empty() {
                    if result.is_false() {
                        // In some cases, the result may be empty. Then we can skip this
                        // branch and continue to the next item on stack.
                        continue 'main;
                    }

                    if result.size() > self.limit && to_merge.len() > 1 {
                        if cfg!(feature = "print-progress") {
                            println!("Try to fork with {} branches.", self.stack.len() + 1);
                        }
                        // Result is too large, we should try to split it first.
                        while next_clause < self.clauses.len() {
                            let clause = &self.clauses[next_clause];
                            next_clause += 1;

                            let result_with_clause = result.and(clause);
                            let result_without_clause = result.and_not(clause);

                            // If the clause is irrelevant, ignore it.
                            if result_with_clause.is_false() || result_without_clause.is_false() {
                                continue;
                            }

                            // If the results are too large, ignore the clause.
                            if result_with_clause.size() + result_without_clause.size()
                                > 2 * result.size()
                            {
                                continue;
                            }

                            if cfg!(feature = "print-progress") {
                                println!(
                                    "Forking on clause {}/{} into {} and {} nodes.",
                                    next_clause,
                                    self.clauses.len(),
                                    result_with_clause.size(),
                                    result_without_clause.size(),
                                );
                            }

                            // Branch on the clause, but make sure the smaller result
                            // is on top of the stack.
                            let with_item = (next_clause, result_with_clause, to_merge.clone());
                            let without_item =
                                (next_clause, result_without_clause, to_merge.clone());
                            if with_item.1.size() < without_item.1.size() {
                                self.stack.push(without_item);
                                self.stack.push(with_item);
                            } else {
                                self.stack.push(with_item);
                                self.stack.push(without_item);
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

                    if cfg!(feature = "print-progress") {
                        println!(
                            " > Merge. New result has {} BDD nodes. Remaining constraints: {}.",
                            result.size(),
                            to_merge.len(),
                        );
                    }
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
                return None;
            }
        }
    }
}

impl<'a> RawSymbolicIterator<'a> {
    /// Try to split this iterator into two independent disjoint iterators, assuming there are
    /// enough forks to permit such operation.
    pub fn try_split(&mut self) -> Option<Self> {
        if self.stack.len() > 1 {
            let split_item = self.stack.remove(0);
            Some(RawSymbolicIterator {
                universe: self.universe,
                limit: self.limit,
                clauses: self.clauses.clone(),
                stack: vec![split_item],
            })
        } else {
            None
        }
    }
}

impl<'a> Iterator for SymbolicIterator<'a> {
    type Item = GraphColoredVertices;

    fn next(&mut self) -> Option<Self::Item> {
        self.inner
            .next()
            .map(|bdd| self.stg.empty_vertices().copy(bdd))
    }
}

impl<'a> SymbolicIterator<'a> {
    /// Create a new `SymbolicIterator` based on the given `SymbolicAsyncGraph`, `restriction` set,
    /// and `limit` size.
    pub fn new(
        stg: &'a SymbolicAsyncGraph,
        restriction: &GraphColoredVertices,
        limit: usize,
    ) -> SymbolicIterator<'a> {
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
                    .take(200)
                    .collect::<Vec<_>>()
                    .into_iter();
                clauses
            })
            .collect();

        clauses.sort_by_cached_key(|clause| clause.last_fixed_variable());
        //clauses.reverse();
        let clauses = clauses
            .into_iter()
            .map(|it| {
                stg.symbolic_context()
                    .bdd_variable_set()
                    .mk_conjunctive_clause(&it)
            })
            .collect::<Vec<_>>();

        SymbolicIterator {
            stg,
            inner: RawSymbolicIterator {
                universe: stg.symbolic_context().bdd_variable_set(),
                limit,
                clauses,
                stack: vec![(
                    0,
                    stg.symbolic_context().bdd_variable_set().mk_true(),
                    to_merge,
                )],
            },
        }
    }

    /// Get the current limit.
    pub fn get_limit(&self) -> usize {
        self.inner.limit
    }

    /// Update the current limit.
    ///
    /// Note that this does not influence forks that were already performed, but
    /// impacts all future decisions.
    pub fn set_limit(&mut self, limit: usize) {
        self.inner.limit = limit
    }

    /// Try to divide the remaining work between two disjoint iterators (this one, and the newly
    /// created one). This can return `None` if not enough forks were performed yet.
    ///
    /// You can use this method to perform basic parallel enumeration. Or you can also try to
    /// diversify the enumerated sets, as the forked iterator should cover states that are
    /// different from the upcoming states in the current iterator.
    pub fn try_split(&mut self) -> Option<Self> {
        self.inner.try_split().map(|it| SymbolicIterator {
            stg: self.stg,
            inner: it,
        })
    }
}

#[cfg(test)]
mod tests {
    use crate::biodivine_std::traits::Set;
    use crate::fixed_points::{FixedPoints, SymbolicIterator};
    use crate::symbolic_async_graph::SymbolicAsyncGraph;
    use crate::BooleanNetwork;

    #[test]
    pub fn test_symbolic_iterator() {
        let bn = BooleanNetwork::try_from_file("aeon_models/g2a_p1026.aeon").unwrap();
        let stg = SymbolicAsyncGraph::new(bn).unwrap();

        let mut set = FixedPoints::naive_symbolic(&stg, stg.unit_colored_vertices());

        let limit = usize::from(stg.symbolic_context().bdd_variable_set().num_vars()) + 2;
        let sets =
            SymbolicIterator::new(&stg, stg.unit_colored_vertices(), limit).collect::<Vec<_>>();

        // Just check that our very small limit worked and there was indeed a fork.
        assert!(sets.len() > 1);

        for partial in sets {
            assert!(partial.is_subset(&set));
            set = set.minus(&partial);
        }

        assert!(set.is_empty());
    }
}
