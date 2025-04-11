use crate::biodivine_std::bitvector::ArrayBitVector;
use crate::fixed_points::FixedPoints;
use crate::solver_context::{BnSolver, BnSolverContext, BnSolverModel, RawBnModelIterator};
use biodivine_lib_bdd::ValuationsOfClauseIterator;
use num_traits::ToPrimitive;
use z3::ast::Bool;

/// An iterator that walks all satisfying results of the Z3 solver in order to list all
/// fixed-point vertices of the associated BN.
///
/// The items of the iterator as `BnSolverModel` instances, from which you can extract both
/// state and color information.
pub struct SolverIterator<'z3> {
    context: &'z3 BnSolverContext<'z3>,
    inner: RawBnModelIterator<'z3>,
}

/// A version of the `SolverIterator` that only goes through all the distinct fixed-point
/// vertices.
pub struct SolverVertexIterator<'z3> {
    context: &'z3 BnSolverContext<'z3>,
    inner: RawBnModelIterator<'z3>,
}

/// A version of the `SolverIterator` that only goes through all the distinct fixed-point
/// colors.
///
/// Note that at the moment, these are just represented as generic `BnSolverModel` instances,
/// since there is no better type-safe object to represent them.
pub struct SolverColorIterator<'z3> {
    context: &'z3 BnSolverContext<'z3>,
    inner: RawBnModelIterator<'z3>,
}

impl<'z3> SolverIterator<'z3> {
    /// Create a `SolverIterator` from a pre-existing solver, assuming that the solver
    /// has all fixed-points constraints applied (e.g. using
    /// `FixedPoints::make_fixed_points_solver`).
    ///
    /// Don't use it unless you are really sure you need a custom solver.
    pub fn new_with_solver(
        context: &'z3 BnSolverContext<'z3>,
        solver: BnSolver<'z3>,
    ) -> SolverIterator<'z3> {
        let mut enumeration_terms = Vec::new();
        enumeration_terms.append(&mut variable_enumeration_terms(context));
        enumeration_terms.append(&mut explicit_parameter_enumeration_terms(context));
        enumeration_terms.append(&mut implicit_parameter_enumeration_terms(context));

        SolverIterator {
            context,
            inner: RawBnModelIterator::new(solver, enumeration_terms),
        }
    }

    pub fn new(context: &'z3 BnSolverContext<'z3>) -> SolverIterator<'z3> {
        SolverIterator::new_with_solver(context, FixedPoints::make_fixed_points_solver(context))
    }
}

impl<'z3> SolverVertexIterator<'z3> {
    /// Create a `SolverVertexIterator` from a pre-existing solver, assuming that the solver
    /// has all fixed-points constraints applied (e.g. using
    /// `FixedPoints::make_fixed_points_solver`).
    ///
    /// Don't use it unless you are really sure you need a custom solver.
    pub fn new_with_solver(
        context: &'z3 BnSolverContext<'z3>,
        solver: BnSolver<'z3>,
    ) -> SolverVertexIterator<'z3> {
        // List only vertex enumeration terms.
        let mut enumeration_terms = Vec::new();
        enumeration_terms.append(&mut variable_enumeration_terms(context));

        SolverVertexIterator {
            context,
            inner: RawBnModelIterator::new(solver, enumeration_terms),
        }
    }

    /// Create a new `SolverVertexIterator` with default constraints applied
    /// based on the provided `BnSolverContext`.
    pub fn new(context: &'z3 BnSolverContext<'z3>) -> SolverVertexIterator<'z3> {
        Self::new_with_solver(context, FixedPoints::make_fixed_points_solver(context))
    }
}

impl<'z3> SolverColorIterator<'z3> {
    /// Create a `SolverColorIterator` from a pre-existing solver, assuming that the solver
    /// has all fixed-points constraints applied (e.g. using
    /// `FixedPoints::make_fixed_points_solver`).
    ///
    /// Don't use it unless you are really sure you need a custom solver.
    pub fn new_with_solver(
        context: &'z3 BnSolverContext<'z3>,
        solver: BnSolver<'z3>,
    ) -> SolverColorIterator<'z3> {
        // List only vertex enumeration terms.
        let mut enumeration_terms = Vec::new();
        enumeration_terms.append(&mut explicit_parameter_enumeration_terms(context));
        enumeration_terms.append(&mut implicit_parameter_enumeration_terms(context));

        SolverColorIterator {
            context,
            inner: RawBnModelIterator::new(solver, enumeration_terms),
        }
    }

    /// Create a new `SolverColorIterator` with default constraints applied
    /// based on the provided `BnSolverContext`.
    pub fn new(context: &'z3 BnSolverContext<'z3>) -> SolverColorIterator<'z3> {
        Self::new_with_solver(context, FixedPoints::make_fixed_points_solver(context))
    }
}

impl<'z3> Iterator for SolverIterator<'z3> {
    type Item = BnSolverModel<'z3>;

    fn next(&mut self) -> Option<Self::Item> {
        self.inner
            .next()
            .map(|it| BnSolverModel::new(self.context, it))
    }
}

impl<'z3> Iterator for SolverVertexIterator<'z3> {
    type Item = ArrayBitVector;

    fn next(&mut self) -> Option<Self::Item> {
        self.inner
            .next()
            .map(|it| BnSolverModel::new(self.context, it).get_state())
    }
}

impl<'z3> Iterator for SolverColorIterator<'z3> {
    type Item = BnSolverModel<'z3>;

    fn next(&mut self) -> Option<Self::Item> {
        self.inner
            .next()
            .map(|it| BnSolverModel::new(self.context, it))
    }
}

/// **(internal)** List the Boolean terms that distinguish all state variables.
fn variable_enumeration_terms<'z3>(context: &BnSolverContext<'z3>) -> Vec<Bool<'z3>> {
    context
        .as_network()
        .variables()
        .map(|var| context.mk_var(var))
        .collect()
}

/// **(internal)** List the Boolean terms that distinguish all explicit parameter valuations.
fn explicit_parameter_enumeration_terms<'z3>(context: &'z3 BnSolverContext<'z3>) -> Vec<Bool<'z3>> {
    let mut result = Vec::new();
    for parameter_id in context.as_network().parameters() {
        let parameter = context.as_network().get_parameter(parameter_id);
        let arity = parameter.get_arity().to_u16().unwrap();
        for row in ValuationsOfClauseIterator::new_unconstrained(arity) {
            let inputs = row.vector();
            let term = context.mk_explicit_const_parameter(parameter_id, &inputs);
            result.push(term);
        }
    }
    result
}

/// **(internal)** List the Boolean terms that distinguish all implicit parameter valuations.
fn implicit_parameter_enumeration_terms<'z3>(context: &'z3 BnSolverContext<'z3>) -> Vec<Bool<'z3>> {
    let mut result = Vec::new();
    for var in context.as_network().variables() {
        if context.as_network().get_update_function(var).is_none() {
            let arity = context.as_network().regulators(var).len();
            let arity = arity.to_u16().unwrap();
            for row in ValuationsOfClauseIterator::new_unconstrained(arity) {
                let inputs = row.vector();
                let term = context.mk_implicit_const_parameter(var, &inputs);
                result.push(term);
            }
        }
    }
    result
}

#[cfg(test)]
mod tests {
    use crate::biodivine_std::traits::Set;
    use crate::fixed_points::solver_iterator::{
        SolverColorIterator, SolverIterator, SolverVertexIterator,
    };
    use crate::fixed_points::FixedPoints;
    use crate::solver_context::BnSolverContext;
    use crate::symbolic_async_graph::SymbolicAsyncGraph;
    use crate::BooleanNetwork;

    #[test]
    pub fn basic_solver_test() {
        let z3 = z3::Context::new(&z3::Config::new());

        let bn = BooleanNetwork::try_from_file("aeon_models/g2a_p1026.aeon").unwrap();
        let stg = SymbolicAsyncGraph::new(&bn).unwrap();
        let ctx = BnSolverContext::new(&z3, bn.clone());

        let mut fixed_points = FixedPoints::naive_symbolic(&stg, stg.unit_colored_vertices());
        let mut fixed_vertices = fixed_points.vertices();
        let mut fixed_colors = fixed_points.colors();

        println!("Fixed points: {}", fixed_points.approx_cardinality());

        let everything_iterator = SolverIterator::new(&ctx);
        let vertex_iterator = SolverVertexIterator::new(&ctx);
        let color_iterator = SolverColorIterator::new(&ctx);

        for model in everything_iterator {
            let symbolic_model = model.get_symbolic_model(stg.symbolic_context());
            assert!(symbolic_model.is_subset(&fixed_points));
            fixed_points = fixed_points.minus(&symbolic_model);
        }
        assert!(fixed_points.is_empty());

        for model in vertex_iterator {
            let vertex = stg.vertex(&model).vertices();
            assert!(vertex.is_subset(&fixed_vertices));
            fixed_vertices = fixed_vertices.minus(&vertex);
        }
        assert!(fixed_vertices.is_empty());

        for model in color_iterator {
            let color = model.get_symbolic_colors(stg.symbolic_context());
            assert!(color.is_subset(&fixed_colors));
            fixed_colors = fixed_colors.minus(&color);
        }
        assert!(fixed_colors.is_empty())
    }
}
