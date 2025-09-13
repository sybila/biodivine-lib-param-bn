use crate::solver_context::{BnSolver, BnSolverModel, RawBnModelIterator};
use z3::SatResult::Sat;
use z3::ast::Bool;

impl RawBnModelIterator {
    /// Construct a new iterator using the given solver.
    pub fn new(solver: BnSolver, enumeration_terms: Vec<Bool>) -> RawBnModelIterator {
        RawBnModelIterator {
            solver,
            enumeration_terms,
            stack: Vec::new(),
        }
    }

    /// Get a reference to the underlying Z3 context.
    pub fn as_z3(&self) -> &z3::Context {
        self.solver.as_z3()
    }

    /// Get a reference to the underlying solver wrapper.
    ///
    /// If you modify the solver in any way, you have to undo all your changes before calling
    /// `next` on the iterator again.
    pub fn as_solver(&self) -> &BnSolver {
        &self.solver
    }

    /// Get a reference to the underlying solver.
    ///
    /// Same restrictions as in `Self::as_solver` apply.
    pub fn as_z3_solver(&self) -> &z3::Solver {
        self.solver.as_z3_solver()
    }

    /// Get a reference to the underlying enumeration terms.
    pub fn enumeration_terms(&self) -> &Vec<Bool> {
        &self.enumeration_terms
    }

    /// A utility method to read the current model of the underlying solver.
    pub fn get_z3_model(&self) -> Option<z3::Model> {
        self.solver.get_z3_model()
    }

    /// A utility method to read the current model of the underlying solver.
    ///
    /// In theory, you can use this method to "replay" the last iterator item,
    /// but don't quote me on that.
    pub fn get_model(&self) -> Option<BnSolverModel> {
        self.solver.get_model()
    }

    /// Use the enumeration term specified by `index` to assert that its value must be
    /// different from what it currently is in the given `model`.
    fn block_term(&self, model: &z3::Model, index: usize) -> Bool {
        self.fix_term(model, index).not()
    }

    /// Use the enumeration term specified by `index` to assert that its value must be
    /// the same as in the given `model`.
    fn fix_term(&self, model: &z3::Model, index: usize) -> Bool {
        let term: &Bool = &self.enumeration_terms[index];
        let term_value = model.eval(term, true).unwrap();
        self.enumeration_terms[index].iff(&term_value)
    }
}

impl Iterator for RawBnModelIterator {
    type Item = z3::Model;

    fn next(&mut self) -> Option<Self::Item> {
        if self.stack.is_empty() {
            return if self.solver.check() == Sat {
                // This is the very first "iteration". We create a new stack item based on the
                // current model and return it. (We have to retrieve the model twice, as it is
                // not clone-able)
                let result = self.get_z3_model().unwrap();
                let stack_model = self.get_z3_model().unwrap();
                self.stack.push((stack_model, 0, 0));
                self.solver.push();
                Some(result)
            } else {
                // When the iterator is finished, a contradiction is inserted to make it
                // unsatisfiable, so we always end up here.
                None
            };
        }

        // We can pop data for one "iteration" and try to advance it further.
        while let Some((model, i_start, i_block)) = self.stack.pop() {
            assert!(i_block >= i_start);
            if i_block >= self.enumeration_terms.len() {
                // There is nothing else to condition on in this layer. So just pop the solver,
                // allowing the underlying layer to advance to the next iteration.
                self.solver.pop();
                if self.stack.is_empty() {
                    // This was the last item, we are done.
                    // Just add an explicit contradiction to the solver
                    // so that it is not satisfiable ever again.
                    let contradiction = Bool::from_bool(false);
                    self.as_z3_solver().assert(&contradiction);
                    return None;
                }
            } else {
                // Apply the current block term restriction.
                self.solver.push();
                self.as_z3_solver()
                    .assert(&self.block_term(&model, i_block));
                for i in i_start..i_block {
                    self.as_z3_solver().assert(&self.fix_term(&model, i));
                }

                if self.solver.check() == Sat {
                    // If the restriction is satisfiable, continue the "virtual" for-loop,
                    // but also start a new recursive search.
                    let result = self.get_z3_model().unwrap();
                    let stack_model = self.get_z3_model().unwrap();
                    // Continue this layer, but with the next block term. (this will happen
                    // once the next layer pops the solver)
                    self.stack.push((model, i_start, i_block + 1));
                    // Add the next layer to test before returning to this layer.
                    // This layer will start testing terms *after* the current block.
                    self.stack.push((stack_model, i_block + 1, i_block + 1));
                    return Some(result);
                } else {
                    // If it is not satisfiable, then continue the "virtual" for-loop
                    // by moving on to the next term.
                    self.solver.pop();
                    self.stack.push((model, i_start, i_block + 1));
                }
            }
        }

        // Technically, we should never get here. If the stack becomes empty,
        // we return from the loop. For next invocation, we return from the first if condition.
        unreachable!("Recursion stack is empty.")
    }
}
