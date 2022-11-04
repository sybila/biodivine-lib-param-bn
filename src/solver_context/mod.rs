//! Solver context provides a way of interfacing between `lib-param-bn` and the Z3 SMT prover.
//!
//! In particular, it provides a canonical relationship between the basic constructs of the
//! parametrized Boolean networks and their representation in Z3 syntax. The user can then use
//! this interface to build algorithms, such as the ones we provide for computation of fixed
//! points and trap spaces.
//!

use crate::BooleanNetwork;
use z3::{FuncDecl, Model, Solver};
use z3::ast::Bool;

mod _impl_bn_solver;
mod _impl_bn_solver_context;
mod _impl_bn_solver_model;

/// A helper object that tracks the mapping between Boolean network entities and variables
/// or uninterpreted functions in Z3.
pub struct BnSolverContext<'z3> {
    network: BooleanNetwork,
    z3: &'z3 z3::Context,
    variable_constructors: Vec<FuncDecl<'z3>>,
    variable_constants: Vec<Bool<'z3>>,
    explicit_parameter_constructors: Vec<FuncDecl<'z3>>,
    implicit_parameter_constructors: Vec<Option<FuncDecl<'z3>>>,
}

/// A helper object that encapsulates Z3 `Solver` with API that is more friendly when used for
/// Boolean networks.
pub struct BnSolver<'z3> {
    context: &'z3 BnSolverContext<'z3>,
    solver: Solver<'z3>,
}

/// A helper object that encapsulates Z3 `Model` with API that is more friendly when used for
/// Boolean networks.
pub struct BnSolverModel<'z3> {
    context: &'z3 BnSolverContext<'z3>,
    model: Model<'z3>,
}