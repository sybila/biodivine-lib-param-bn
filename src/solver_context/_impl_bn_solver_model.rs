use z3::ast::Bool;
use z3::FuncDecl;
use crate::solver_context::BnSolverModel;

impl<'z3> BnSolverModel<'z3> {

    pub fn as_z3_model(&self) -> &z3::Model<'z3> {
        &self.model
    }

    /// Extract the network state defined by the state variables of the associated
    /// `BnSolverContext`.
    pub fn get_state(&self) -> Vec<bool> {
        self.context.variable_constants.iter()
            .map(|var| {
                self.model.eval(var, true)
                    .unwrap()
                    .as_bool()
                    .unwrap()
            })
            .collect()
    }

    /// Extract the values of particular state variables (given as Boolean constant expressions).
    ///
    /// Note that it is your responsibility to ensure that the variable expressions match the
    /// order of variables in the original Boolean network.
    pub fn get_raw_state(&self, variables: &[Bool<'z3>]) -> Vec<bool> {
        assert_eq!(variables.len(), self.context.network.num_vars());
        let mut state = Vec::new();
        for var in variables {
            let result = self.model.eval(var, true).unwrap();
            state.push(result.as_bool().unwrap());
        }
        state
    }

}