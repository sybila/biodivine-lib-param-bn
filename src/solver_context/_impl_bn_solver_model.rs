use crate::biodivine_std::bitvector::ArrayBitVector;
use crate::solver_context::{BnSolverContext, BnSolverModel};
use crate::symbolic_async_graph::{
    GraphColoredVertices, GraphColors, GraphVertices, SymbolicContext,
};
use crate::ExtendedBoolean::{One, Zero};
use crate::Space;
use biodivine_lib_bdd::{BddPartialValuation, BddVariable};
use std::fmt::{Debug, Formatter};
use z3::ast::Bool;

impl<'z3> Debug for BnSolverModel<'z3> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", self.model)
    }
}

impl<'z3> BnSolverModel<'z3> {
    pub fn new(context: &'z3 BnSolverContext<'z3>, model: z3::Model<'z3>) -> BnSolverModel<'z3> {
        BnSolverModel { context, model }
    }

    pub fn as_z3_model(&self) -> &z3::Model<'z3> {
        &self.model
    }

    /// Extract the network state defined in this model as a symbolic singleton set
    /// (in the context of the given `SymbolicContext`).
    ///
    /// WARNING: The solver context and symbolic context must be created from the same Boolean
    /// network with the same variable ordering, otherwise the result is undefined.
    pub fn get_symbolic_state(&self, symbolic: &SymbolicContext) -> GraphVertices {
        let mut data: Vec<(BddVariable, bool)> = Vec::new();
        self.read_symbolic_state_data(symbolic, &mut data);
        let partial_valuation = BddPartialValuation::from_values(&data);

        let bdd = symbolic
            .bdd_variable_set()
            .mk_conjunctive_clause(&partial_valuation);

        GraphVertices::new(bdd, symbolic)
    }

    /// Extract the network state defined in this model as a symbolic singleton set
    /// (in the context of the given `SymbolicContext`).
    ///
    /// WARNING: The solver context and symbolic context must be created from the same Boolean
    /// network with the same variable ordering, otherwise the result is undefined.
    pub fn get_symbolic_colors(&self, symbolic: &SymbolicContext) -> GraphColors {
        let mut data: Vec<(BddVariable, bool)> = Vec::new();
        self.read_symbolic_color_data(symbolic, &mut data);
        let partial_valuation = BddPartialValuation::from_values(&data);

        let bdd = symbolic
            .bdd_variable_set()
            .mk_conjunctive_clause(&partial_valuation);

        GraphColors::new(bdd, symbolic)
    }

    /// Extract the vertex-color pair defined in this model as a symbolic singleton set
    /// (in the context of the given `SymbolicContext`).
    ///
    /// WARNING: The solver context and symbolic context must be created from the same Boolean
    /// network with the same variable ordering, otherwise the result is undefined.
    pub fn get_symbolic_model(&self, symbolic: &SymbolicContext) -> GraphColoredVertices {
        let mut data: Vec<(BddVariable, bool)> = Vec::new();
        self.read_symbolic_state_data(symbolic, &mut data);
        self.read_symbolic_color_data(symbolic, &mut data);
        let partial_valuation = BddPartialValuation::from_values(&data);

        let bdd = symbolic
            .bdd_variable_set()
            .mk_conjunctive_clause(&partial_valuation);

        GraphColoredVertices::new(bdd, symbolic)
    }

    /// Extract the network state defined by the state variables of the associated
    /// `BnSolverContext`.
    pub fn get_state(&self) -> ArrayBitVector {
        let data: Vec<bool> = self
            .context
            .variable_constants
            .iter()
            .map(|var| self.get_bool(var))
            .collect();
        ArrayBitVector::from(data)
    }

    /// **(internal)** A helper method for reading the value of a Boolean term from
    /// the underlying model.
    fn get_bool(&self, term: &Bool<'z3>) -> bool {
        self.model.eval(term, true).unwrap().as_bool().unwrap()
    }

    /// **(internal)** Used to extract state data from the model in a format that the symbolic
    /// APIs can understand.
    fn read_symbolic_state_data(
        &self,
        symbolic: &SymbolicContext,
        data: &mut Vec<(BddVariable, bool)>,
    ) {
        for variable in self.context.as_network().variables() {
            let bdd_var = symbolic.get_state_variable(variable);
            let z3_var = self.context.var(variable);
            let value = self.get_bool(z3_var);
            data.push((bdd_var, value));
        }
    }

    /// **(internal)** Used to extract color data from the model in a format that the symbolic
    /// APIs can understand.
    fn read_symbolic_color_data(
        &self,
        symbolic: &SymbolicContext,
        data: &mut Vec<(BddVariable, bool)>,
    ) {
        let network = self.context.as_network();
        for variable in network.variables() {
            if network.get_update_function(variable).is_none() {
                let table = symbolic.get_implicit_function_table(variable);
                for (input, bdd_var) in table {
                    let z3_term = self.context.mk_implicit_const_parameter(variable, &input);
                    let value = self.get_bool(&z3_term);
                    data.push((bdd_var, value));
                }
            }
        }

        for parameter in network.parameters() {
            let table = symbolic.get_explicit_function_table(parameter);
            for (input, bdd_var) in table {
                let z3_term = self.context.mk_explicit_const_parameter(parameter, &input);
                let value = self.get_bool(&z3_term);
                data.push((bdd_var, value));
            }
        }
    }

    /// Extract the values of particular state variables (given as Boolean constant expressions).
    ///
    /// Note that it is your responsibility to ensure that the variable expressions match the
    /// order of variables in the original Boolean network.
    pub fn get_raw_state(&self, variables: &[Bool<'z3>]) -> Vec<bool> {
        assert_eq!(variables.len(), self.context.network.num_vars());
        let mut state = Vec::new();
        for var in variables {
            state.push(self.get_bool(var));
        }
        state
    }

    pub fn get_space(
        &self,
        positive_variables: &[Bool<'z3>],
        negative_variables: &[Bool<'z3>],
    ) -> Space {
        let mut space = Space::new(self.context.as_network());
        let ones = self.get_raw_state(positive_variables);
        let zeros = self.get_raw_state(negative_variables);
        for var in self.context.as_network().variables() {
            if ones[var.to_index()] && !zeros[var.to_index()] {
                space[var] = One;
            }
            if !ones[var.to_index()] && zeros[var.to_index()] {
                space[var] = Zero;
            }
        }
        space
    }
}
