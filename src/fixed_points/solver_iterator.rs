use z3::ast::Bool;
use z3::{Model, SatResult};
use z3::SatResult::Sat;
use crate::BooleanNetwork;
use crate::solver_context::{BnSolver, BnSolverContext, BnSolverModel};

struct RawSolverIterator<'z3> {
    enum_terms: Vec<Bool<'z3>>,
    solver: BnSolver<'z3>,
    // Stack of terms that still need to be explored.
    stack: Vec<(Model<'z3>, usize, usize)>,
}

pub struct SolverIterator<'z3> {
    inner: RawSolverIterator<'z3>,
}

impl<'z3> SolverIterator<'z3> {

    pub fn new(context: &'z3 BnSolverContext<'z3>) -> SolverIterator<'z3> {
        // Make a solver with all static constraints applied.
        let solver = context.mk_network_solver();

        for var in context.as_network().variables() {
            let var_is_true = context.var(var);
            let update_is_true = context.mk_update_function(var);

            let assertion = update_is_true.iff(&var_is_true);
            //println!("{:?}", assertion);
            solver.as_native_solver().assert(&assertion);
        }

        /*
            TODO:
             - Enum terms must include parameters.
             - Add iterator variant for just vertices/just parameters by restricting enum terms.
             - Add some way to construct the raw fixed-point iterator with arbitrary enum terms.
             - BnSolverModel should return ArrayBitVector as representation of states.
             - BnSolverModel should be able to return some representation of uninterpreted functions.
             - This could just be an instantiated Boolean network without parameters?
             - Or just a GraphColors singleton?
             - It seems that z3-sys actually has methods that can read the uninterpreted function,
               but they are not available in this library. Maybe we can make them available?
             - ... do the same for trap spaces?
         */

        let enum_terms: Vec<Bool<'z3>> = context.as_network().variables()
            .map(|it| context.mk_var(it))
            .collect();

        SolverIterator {
            inner: RawSolverIterator {
                solver,
                enum_terms,
                stack: Vec::new(),
            }
        }
    }

}

impl<'z3> Iterator for SolverIterator<'z3> {
    type Item = BnSolverModel<'z3>;

    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next()
    }
}

impl<'z3> Iterator for RawSolverIterator<'z3> {
    type Item = BnSolverModel<'z3>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.stack.is_empty() {
            println!("Stack is empty and solver is {:?}", self.solver.check());
            return if self.solver.check() == Sat {
                let model = self.solver.get_model().unwrap();
                self.stack.push((self.solver.as_native_solver().get_model().unwrap(), 0, 0));
                self.solver.push();
                Some(model)
            } else {
                None
            }
        }

        while let Some((model, i_start, i_block)) = self.stack.pop() {
            assert!(i_block >= i_start);
            if i_block >= self.enum_terms.len() {
                //println!("i_block >= enum_terms.len()... Pop.");
                // There is nothing else to condition on in this layer. So just pop the solver,
                // allowing the underlying layer to advance to the next iteration.
                self.solver.pop();
                if self.stack.is_empty() {
                    // This was the last item... just add an explicit contradiction to the solver
                    // so that it is not satisfiable ever again.
                    self.solver.as_native_solver().assert(
                        &Bool::from_bool(self.solver.as_z3(), false)
                    );
                }
            } else {
                // Apply the current restriction.

                // At this point, the model must exist, because that is the only way we could have
                // gotten to the next recursive layer (i.e. a new push happens only if we have `Sat`).
                //assert_eq!(self.solver.check(), Sat);
                //let model = self.solver.as_native_solver().get_model().unwrap();
                //println!("Push.");
                self.solver.push();
                //println!("Block !{}", i_block);
                let block_term = model.eval(&self.enum_terms[i_block], true).unwrap();
                self.solver.as_native_solver().assert(&self.enum_terms[i_block].iff(&block_term).not());
                for i in i_start..i_block {
                    let fix_term = model.eval(&self.enum_terms[i], true).unwrap();
                    self.solver.as_native_solver().assert(&self.enum_terms[i].iff(&fix_term));
                    //println!(" > Fix {}", i);
                }
                if self.solver.check() == Sat {
                    // If the restriction is satisfiable, continue the "virtual" for-loop,
                    // but also start a new recursive search.
                    let new_model = self.solver.get_model().unwrap();
                    self.stack.push((model, i_start, i_block + 1));
                    self.stack.push((self.solver.as_native_solver().get_model().unwrap(), i_block + 1, i_block + 1));
                    //println!("Block sat. Recursion...");
                    return Some(new_model);
                } else {
                    // If it is not satisfiable, then continue the "virtual" for-loop
                    // by conditioning on the next term.
                    self.solver.pop();
                    //println!("Block unsat. Pop.");
                    self.stack.push((model, i_start, i_block + 1));
                }
            }
        }

        None
    }

}
