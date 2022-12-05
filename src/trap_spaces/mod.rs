//! This module has some preliminary simple ideas for computing the minimal trap spaces
//! of Boolean networks.
//!
//! At the moment, it is somewhat unique in the sense that it does not use a SAT/ASP solver
//! but performs the search directly. While this is often slower, the goal is to later extend
//! the algorithm such that it can better handle problems with large numbers of parameters,
//! where a solver might be limited by the need to enumerate all the solutions explicitly.
//! However, for now, we do not really support models with parameters/uninterpreted functions.
//!

use std::fmt::Debug;

pub mod dual_symbolic_encoding;
pub mod solver_iterator;

/// **(internal)** Basic convenience methods for extended Booleans, like logical operators
/// and display/debug traits.
mod _impl_extended_boolean;

/// **(internal)** Basic convenience methods for optional Extended Booleans, like logical
/// operators and display/debug traits.
mod _impl_optional_extended_boolean;

/// **(internal)** Basic convenience methods for working with spaces.
mod _impl_space;

/// **(internal)** Basic convenience methods for working with partial spaces.
mod _impl_partial_space;

/// **(internal)** Methods for partial evaluation of `FnUpdate` functions on `ExtendedBoolean`
/// or `OptExtBoolean`.
mod _impl_fn_update_partial_evaluation;

/// **(internal)** Implements the actual branching search algorithm for identifying trap spaces.
mod _impl_search_algorithm;

/// An enum representing the possible state of each variable when describing a hypercube.
#[derive(Copy, Clone, Eq, PartialEq, Hash)]
pub enum ExtendedBoolean {
    Zero,
    One,
    Any,
}

/// `Space` represents a hypercube (multi-dimensional rectangle) in the Boolean state space.
///
/// Keep in mind that there is no way of representing an empty hypercube at the moment. So any API
/// that can take/return an empty set has to use `Option<Space>` or something similar.
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct Space(Vec<ExtendedBoolean>);

/// An enum representing an *optional* extended Boolean. This is only used during the
/// trap space search to represent whether a value of a particular variable is already
/// "locked in" or not.
#[derive(Copy, Clone, Eq, PartialEq, Hash)]
pub enum OptionalExtendedBoolean {
    Zero,
    One,
    Any,
    Unknown,
}

/// A version of the `Space` that uses `OptExtBoolean` instead of `ExtendedBoolean`.
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct PartialSpace(Vec<OptionalExtendedBoolean>);
