//! This module provides methods and structures for representing the parameter valuations
//! of `BooleanNetwork`s using `Bdd`s.
//!
//! Specifically, there is the `BddParams` struct which represents the set of valuations
//! and the `BddParameterEncoder` struct which allows creating new `Bdd` and `BddParams` that
//! correspond to situations where individual parameters have a specific value.

use crate::VariableId;
use biodivine_lib_bdd::{Bdd, BddVariable, BddVariableSet};

mod impl_bdd_parameter_encoder;
mod impl_bdd_params;
mod impl_fn_update;
mod impl_function_table_entry;
mod impl_static_constraints;
mod impl_witness_generator;

pub use impl_static_constraints::build_static_constraints;

/// A wrapper for the `Bdd` object that implements `Params`;
#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub struct BddParams(Bdd);

/// Handles the translation between parameters of the `BooleanNetwork` and `BddVariable`s
/// used when representing the parameter valuation sets as `Bdd`s.
///
/// There are two types of parameters in the `BooleanNetwork` - explicit and implicit.
///
/// Explicit are the named parameters that are specifically declared in the update functions.
/// Implicit are the anonymous parameters representing the missing update functions.
///
/// Every explicit and implicit `Parameter` maps to a set of `BddVariable`s that represent
/// the values in its function table. The responsibility of this struct is to create all
/// `BddVariable`s and maintain how they map to individual parameters.
#[derive(Clone)]
pub struct BddParameterEncoder {
    /// The actual `BddVariableSet` used to represent the parameters - use this for `.dot` printing etc.
    pub bdd_variables: BddVariableSet,
    /// The actual regulators of each variable - these are used when evaluating implicit parameters.
    regulators: Vec<Vec<VariableId>>,
    /// A vector of function tables indexed by explicit `ParameterId`s of the `BooleanNetwork`.
    explicit_function_tables: Vec<Vec<BddVariable>>,
    /// A vector of implicit function tables indexed by `VariableId`s of the `BooleanNetwork`.
    /// If the variable has an explicit update function, the table is empty.
    implicit_function_tables: Vec<Vec<BddVariable>>,
}

/// **(experimental)** Represents one "line" in a boolean function table.
///
/// You can query the state of input variables on this line or make a new line
/// with updated variable values.
pub struct FunctionTableEntry<'a> {
    entry_index: usize, // index into the specific table
    table: usize,       // index into the vector of tables
    regulators: &'a Vec<VariableId>,
}
