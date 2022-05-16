use crate::biodivine_std::traits::Set;
use crate::symbolic_async_graph::{GraphColoredVertices, SymbolicAsyncGraph};
use crate::ParameterId;

/// Here, we provide several basic symbolic algorithms for exploring the `SymbolicAsyncGraph`.
/// This mainly includes reachability and similar fixed-point properties.
///
/// In some cases, you may want to re-implement these algorithms, since they do not have
/// more advanced features, like logging or cancellation. But for most general use-cases, these
/// should be the best we can do right now in terms of performance.
impl SymbolicAsyncGraph {
    /// Compute the set of forward-reachable vertices from the given `initial` set.
    ///
    /// In other words, the result is the smallest forward-closed superset of `initial`.
    pub fn reach_forward(&self, initial: &GraphColoredVertices) -> GraphColoredVertices {
        let mut result = initial.clone();
        'fwd: loop {
            for var in self.network.variables().rev() {
                let step = self.var_post_out(var, &result);
                if !step.is_empty() {
                    result = result.union(&step);
                    continue 'fwd;
                }
            }

            return result;
        }
    }

    /// Compute the set of backward-reachable vertices from the given `initial` set.
    ///
    /// In other words, the result is the smallest backward-closed superset of `initial`.
    pub fn reach_backward(&self, initial: &GraphColoredVertices) -> GraphColoredVertices {
        let mut result = initial.clone();
        'bwd: loop {
            for var in self.network.variables().rev() {
                let step = self.var_pre_out(var, &result);
                if !step.is_empty() {
                    result = result.union(&step);
                    continue 'bwd;
                }
            }

            return result;
        }
    }

    /// Compute the subset of `initial` vertices that can only reach other vertices within
    /// the `initial` set.
    ///
    /// In other words, the result is the largest forward-closed subset of `initial`.
    pub fn trap_forward(&self, initial: &GraphColoredVertices) -> GraphColoredVertices {
        let mut result = initial.clone();
        'fwd: loop {
            for var in self.network.variables().rev() {
                let step = self.var_can_post_out(var, &result);
                if !step.is_empty() {
                    result = result.minus(&step);
                    continue 'fwd;
                }
            }

            return result;
        }
    }


    fn gain(a: f64, b: f64, c: f64) -> f64 {
        a - (b * 0.5 + c * 0.5)
    }

    pub fn trap_forward_2(
        &self,
        initial: &GraphColoredVertices,
        limit: usize,
    ) -> GraphColoredVertices {
        let mut result = initial.clone();
        'fwd: loop {
            if result.bdd.size() > 10_000 {
                println!(
                    "Progress: {} {}",
                    result.bdd.size(),
                    result.approx_cardinality()
                );
            }
            if result.bdd.size() > limit {
                println!("Initial size: {}.", result.bdd.size());
                let mut best_gain = None;
                for par in self.network.parameters() {
                    let par_true = self
                        .symbolic_context
                        .mk_uninterpreted_function_is_true(par, &[]);

                    let bdd_true = result.bdd.and(&par_true);
                    let bdd_false = result.bdd.and_not(&par_true);
                    let gain = Self::gain(
                        result.bdd.size() as f64,
                        bdd_true.size() as f64,
                        bdd_false.size() as f64,
                    );
                    if let Some((current, _)) = best_gain {
                        if gain > current {
                            best_gain = Some((gain, par));
                        }
                    } else if gain > 0.0 {
                        best_gain = Some((gain, par));
                    }
                    println!(
                        "Split on {:?}: {} + {} = {}",
                        par,
                        bdd_true.size(),
                        bdd_false.size(),
                        bdd_true.size() + bdd_false.size()
                    );
                }

                let mut line = String::new();
                std::io::stdin().read_line(&mut line).unwrap();

                best_gain = Some((10., ParameterId(line.trim().parse::<usize>().unwrap())));

                if let Some((best, par)) = best_gain {
                    println!("Split on parameter {:?} with gain: {}", par, best);

                    let par_true = self
                        .symbolic_context
                        .mk_uninterpreted_function_is_true(par, &[]);

                    let bdd_true = result.bdd.and(&par_true);
                    let bdd_false = result.bdd.and_not(&par_true);

                    println!(
                        "Split into: {} / {} / {}",
                        result.bdd.size(),
                        bdd_true.size(),
                        bdd_false.size()
                    );

                    let split_true = result.copy(bdd_true);
                    let split_false = result.copy(bdd_false);

                    let result_true = self.trap_forward_2(&split_true, 2 * limit);
                    let result_false = self.trap_forward_2(&split_false, 2 * limit);

                    return result_true.union(&result_false);
                } else {
                    println!("Cannot split.");
                }
            }
            for var in self.network.variables().rev() {
                let step = self.var_can_post_out(var, &result);
                if !step.is_empty() {
                    result = result.minus(&step);
                    continue 'fwd;
                }
            }

            return result;
        }
    }

    /// Compute the subset of `initial` vertices that can only be reached from vertices within
    /// the `initial` set.
    ///
    /// In other words, the result is the largest backward-closed subset of `initial`.
    pub fn trap_backward(&self, initial: &GraphColoredVertices) -> GraphColoredVertices {
        let mut result = initial.clone();
        'bwd: loop {
            for var in self.network.variables().rev() {
                let step = self.var_can_pre_out(var, &result);
                if !step.is_empty() {
                    result = result.minus(&step);
                    continue 'bwd;
                }
            }

            return result;
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::biodivine_std::traits::Set;
    use crate::symbolic_async_graph::SymbolicAsyncGraph;
    use crate::BooleanNetwork;

    #[test]
    pub fn basic_algorithms_test() {
        // Right now, there isn't really a strategy on how this should be tested, so for now
        // we only test if we can run through all the code and get reasonable results.
        let bn = BooleanNetwork::try_from(
            r"
            b ->? a
            c ->? a
            a -|? a
            a -> b
            a -> c
            c -| b
        ",
        )
        .unwrap();

        let stg = SymbolicAsyncGraph::new(bn).unwrap();

        let pivot = stg.unit_colored_vertices().pick_vertex();
        let fwd = stg.reach_forward(&pivot);
        let bwd = stg.reach_backward(&pivot);
        let scc = fwd.intersect(&bwd);

        // Should contain all cases where pivot is in an attractor.
        let attractor_basin = stg.trap_forward(&bwd);
        // Should contain all cases where pivot is in a repeller.
        let repeller_basin = stg.trap_backward(&fwd);

        assert!(fwd.approx_cardinality() > pivot.approx_cardinality());
        assert!(bwd.approx_cardinality() > pivot.approx_cardinality());
        assert!(scc.approx_cardinality() > pivot.approx_cardinality());
        assert!(attractor_basin.approx_cardinality() > pivot.approx_cardinality());
        // For some reason, there is only a very small number of parameter valuations
        // where this is not empty -- less than in the pivot in fact.
        assert!(!repeller_basin.is_empty());
    }
}
