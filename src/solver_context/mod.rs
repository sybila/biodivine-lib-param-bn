//! Solver context provides a way of interfacing between `lib-param-bn` and the Z3 SMT prover.
//!
//! In particular, it provides a canonical relationship between the basic constructs of the
//! parametrized Boolean networks and their representation in Z3 syntax. The user can then use
//! this interface to build algorithms, such as the ones we provide for computation of fixed
//! points and trap spaces.
//!

use crate::BooleanNetwork;
use std::rc::Rc;
use z3::ast::Bool;
use z3::{FuncDecl, Model, Solver};

mod _impl_bn_solver;
mod _impl_bn_solver_context;
mod _impl_bn_solver_model;
mod _impl_raw_bn_model_iterator;

/// A helper object that tracks the mapping between Boolean network entities and variables
/// or uninterpreted functions in Z3.
#[derive(Clone)]
pub struct BnSolverContext {
    data: Rc<BnSolverContextData>,
}

/// Internal structure which actually contains all the data managed by [`BnSolverContext`].
struct BnSolverContextData {
    network: BooleanNetwork,
    z3: z3::Context, // This is no longer needed, only keeping it for compatibility reasons.
    variable_constructors: Vec<FuncDecl>,
    variable_constants: Vec<Bool>,
    explicit_parameter_constructors: Vec<FuncDecl>,
    implicit_parameter_constructors: Vec<Option<FuncDecl>>,
}

/// A helper object that encapsulates Z3 `Solver` with an API that is more friendly when used
/// for analysis of Boolean networks.
///
/// At the moment, it mostly contains utility methods for translating static regulation
/// constraints to solver constraints, such that the space of admissible interpretations
/// is captured correctly.
pub struct BnSolver {
    context: BnSolverContext,
    solver: Solver,
}

/// A helper object that encapsulates Z3 `Model` with API that is more friendly when used for
/// Boolean networks.
///
/// In particular, it allows us to read the current state and parameter interpretations
/// of the model. Right now, these can mostly be only read in a BDD form, as we don't have
/// adequate APIs in place to represents individual interpretations of update functions
/// in any other way.
///
/// As such, the process of extracting the results in a type-safe manner is not particularly fast,
/// and requires that you still use the symbolic representation as an intermediate step. However,
/// we hope to improve this in the future significantly.
///
/// TODO:
///     It appears that `z3-sys` actually has some representation for the returned functions,
///     but it is not exported to `z3`. It would be nice to add support for it, and then add
///     some kind of wrapper in this crate so that it can safely interact with Boolean network
///     and similar objects.
pub struct BnSolverModel {
    context: BnSolverContext,
    model: Model,
}

/// An iterator which goes through `BnSolverModel` instances that satisfy a particular
/// `BnSolver`. The instances are generated based on a set of given Boolean terms.
///
/// Usually, you don't want to use this directly. Instead, you should wrap this into some
/// high-level iterator which will facilitate type-safe conversions for you.
///
/// Technically, the iterator will not go through all satisfying models, it will only enumerate
/// models which differ in the supplied set of Boolean terms. Using this list of terms, you can
/// then implement things like enumeration with projection: You only supply terms corresponding
/// to variables that you want in your result and everything else is "projected away".
///
/// At the moment, the iterator is restricted to enumeration based on Boolean terms, because
/// they are easier to work with. But in the future, we might be able to support
/// any arbitrary term.
///
/// Note that while the API technically allows access to the inner solver, the iterator will
/// extensively push/pop new assumptions to it. So if you make any changes to the solver, make
/// sure they are undone before the next item is retrieved from the iterator.
///
/// The enumeration approach is based on this more involved discussion:
/// <https://stackoverflow.com/questions/11867611/z3py-checking-all-solutions-for-equation/70656700#70656700>
pub struct RawBnModelIterator {
    solver: BnSolver,
    enumeration_terms: Vec<Bool>,
    // Stack which guides the exhaustive search.
    //  - Model is a saved copy of the model which is used for conditioning at this "layer".
    //  - First integer is the index of the first enumeration term that we consider.
    //  - Second integer is the index of the conditioning term for this iteration.
    stack: Vec<(Model, usize, usize)>,
}
