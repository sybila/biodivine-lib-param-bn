//! A library for analysis of Boolean networks. As of now, the library supports:
//!  - Regulatory graphs with monotonicity and observability constraints.
//!  - Boolean networks, possibly with partially unknown and parametrised update functions.
//!  - Full SBML-qual support for import/export as well as custom string format `.aeon`.
//!  - Fully symbolic asynchronous state-space generator using BDDs (great overall performance).
//!  - Semi-symbolic state-space generator, using BDDs used only for the network parameters
//! (allows state-level parallelism for smaller networks).
//!
//! For a quick introduction to Boolean networks and their symbolic manipulation, you can
//! check out our [tutorial module](./tutorial/index.html).
//!
#[macro_use]
extern crate lazy_static;

use regex::Regex;
use std::collections::HashMap;
use std::iter::Map;
use std::ops::Range;

pub mod async_graph;
pub mod bdd_params;
pub mod biodivine_std;
pub mod sbml;
pub mod symbolic_async_graph;
pub mod tutorial;

/// **(internal)** Implements `.aeon` parser for `BooleanNetwork` and `RegulatoryGraph` objects.
mod _aeon_parser;
/// **(internal)** Implements experimental `.bnet` parser for `BooleanNetwork`.
mod _bnet_parser;
/// **(internal)** Implements an experimental `.bnet` writer for `BooleanNetwork`.
mod _bnet_writer;
/// **(internal)** Utility methods for `BinaryOp`.
mod _impl_binary_op;
/// **(internal)** Utility methods for `BooleanNetwork`.
mod _impl_boolean_network;
/// **(internal)** `BooleanNetwork` to `.aeon` string.
mod _impl_display_boolean_network;
/// **(internal)** `RegulatoryGraph` to `.aeon` string.
mod _impl_display_regulatory_graph;
/// **(internal)** Utility methods for `FnUpdate`.
mod _impl_fn_update;
/// **(internal)** Utility methods for `Parameter`.
mod _impl_parameter;
/// **(internal)** Utility methods for `ParameterId`.
mod _impl_parameter_id;
/// **(internal)** Utility methods for `Regulation`.
mod _impl_regulation;
/// **(internal)** Utility methods for `RegulatoryGraph`.
mod _impl_regulatory_graph;
/// **(internal)** Utility methods for `Variable`.
mod _impl_variable;
/// **(internal)** Utility methods for `VariableId`.
mod _impl_variable_id;

/// **(internal)** A regex string of an identifier which we currently allow to appear
/// as a variable or parameter name.
const ID_REGEX_STR: &str = r"[a-zA-Z0-9_]+";

lazy_static! {
    /// A regular expression that matches the identifiers allowed as names of
    /// Boolean parameters or variables.
    static ref ID_REGEX: Regex = Regex::new(ID_REGEX_STR).unwrap();
}

/// A type-safe index of a `Variable` inside a `RegulatoryGraph` (or a `BooleanNetwork`).
///
/// If needed, it can be converted into `usize` for serialisation and safely read
/// again by providing the original `RegulatoryGraph` as context
/// to the `VariableId::try_from_usize`.
///
/// **Warning:** Do not mix type-safe indices between different networks/graphs!
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct VariableId(usize);

/// A type-safe index of a `Parameter` inside a `BooleanNetwork`.
///
/// If needed, it can be converted into `usize` for serialisation and safely read
/// again by providing the original `BooleanNetwork` as context
/// to the `ParameterId::try_from_usize`.
///
/// **Warning:** Do not mix type-safe indices between different networks!
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ParameterId(usize);

/// Possible monotonous effects of a `Regulation` in a `RegulatoryGraph`.
///
/// Activation means positive and inhibition means negative monotonicity.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Monotonicity {
    Activation,
    Inhibition,
}

/// A Boolean variable of a `RegulatoryGraph` (or a `BooleanNetwork`) with a given `name`.
///
/// `Variable` can be only created by and borrowed from a `RegulatoryGraph`.
/// It has no public constructor.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Variable {
    name: String,
}

/// An explicit parameter of a `BooleanNetwork`; an uninterpreted Boolean function with a given
/// `name` and `arity`.
///
/// `Parameter` can be only created by and borrowed form the `BooleanNetwork` itself.
/// It has no public constructor.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct Parameter {
    name: String,
    arity: u32,
}

/// Describes an interaction between two `Variables` in a `RegulatoryGraph`
/// (or a `BooleanNetwork`).
///
/// Every regulation can be *monotonous*, and can be set as *observable*:
///
///  - Monotonicity is either *positive* or *negative* and signifies that the influence of the
/// `regulator` on the `target` has to *increase* or *decrease* the `target` value respectively.
///  - If observability is set to `true`, the `regulator` *must* have influence on the outcome
///  of the `target` update function in *some* context. If set to false, this is not enforced
///  (i.e. the `regulator` *can* have an influence on the `target`, but it is not required).
///
/// Regulations can be represented as strings in the
/// form `"regulator_name 'relationship' target_name"`. The 'relationship' starts with `-`, which
/// is followed by `>` for activation (positive monotonicity), `|` for inhibition (negative
/// monotonicity) or `?` for unspecified monotonicity. Finally, an additional `?` at the end
/// of 'relationship' signifies a non-observable regulation. Together, this gives the
/// following options:  `->, ->?, -|, -|?, -?, -??`.
///
/// Regulations cannot be created directly, they are only borrowed from a `RegulatoryGraph`
/// or a `BooleanNetwork`.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct Regulation {
    regulator: VariableId,
    target: VariableId,
    observable: bool,
    monotonicity: Option<Monotonicity>,
}

/// A directed graph representing relationships between a collection of Boolean variables
/// using `Regulations`.
///
/// It can be explored using `regulators`, `targets`, `transitive_regulators`, or
/// `transitive_targets` (for example to determine if two variables depend on each other).
/// We can also compute the SCCs of this graph.
///
/// A regulatory graph can be described using a custom string format. In this format,
/// each line represents a regulation or a comment (starting with `#`).
///
/// Regulations can be represented as strings in the form of
/// `"regulator_name 'relationship' target_name"`. The 'relationship' is one of the arrow strings
/// `->, ->?, -|, -|?, -?, -??`. Here, `>` means activation, `|` is inhibition and `?` is
/// unspecified monotonicity. The last question mark signifies observability — if it is present,
/// the regulation is not necessarily observable. See `Regulation` and tutorial module for a more
/// detailed explanation.
///
/// Example of a `RegulatoryGraph`:
///
/// ```rg
///  # Regulators of a
///  a ->? a
///  b -|? a
///
///  # Regulators of b
///  a -> b
///  b -| b
/// ```
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct RegulatoryGraph {
    variables: Vec<Variable>,
    regulations: Vec<Regulation>,
    variable_to_index: HashMap<String, VariableId>,
}

/// Possible binary Boolean operators that can appear in `FnUpdate`.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum BinaryOp {
    And,
    Or,
    Xor,
    Iff,
    Imp,
}

/// A Boolean update function formula which references
/// `Variables` and `Parameters` of a `BooleanNetwork`.
///
/// An update function specifies the evolution rules for one specific `Variable` of a
/// `BooleanNetwork`. The arguments used in the function must be the same as specified
/// by the `RegulatoryGraph` of the network.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub enum FnUpdate {
    /// A true/false constant.
    Const(bool),
    /// References a network variable.
    Var(VariableId),
    /// References a network parameter (uninterpreted function).
    ///
    /// The variable list are the arguments of the function invocation.
    Param(ParameterId, Vec<VariableId>),
    /// Negation.
    Not(Box<FnUpdate>),
    /// Binary boolean operation.
    Binary(BinaryOp, Box<FnUpdate>, Box<FnUpdate>),
}

/// A Boolean network, possibly parametrised with uninterpreted Boolean functions.
///
/// The structure of the network is based on an underlying `RegulatoryGraph`. However,
/// compared to a `RegulatoryGraph`, `BooleanNetwork` can have a specific update function
/// given for each variable.
///
/// If the function is not specified (so called *implicit parametrisation*), all admissible
/// Boolean functions are considered in its place. A function can be also only partially
/// specified by using declared *explicit parameters*. These are uninterpreted but named Boolean
/// functions, such that, again, all admissible instantiations of these functions are considered.
/// See crate tutorial to learn more.
///
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct BooleanNetwork {
    graph: RegulatoryGraph,
    parameters: Vec<Parameter>,
    update_functions: Vec<Option<FnUpdate>>,
    parameter_to_index: HashMap<String, ParameterId>,
}

/// An iterator over all `VariableIds` of a `RegulatoryGraph` (or a `BooleanNetwork`).
pub type VariableIdIterator = Map<Range<usize>, fn(usize) -> VariableId>;

/// An iterator over all `ParameterIds` of a `BooleanNetwork`.
pub type ParameterIdIterator = Map<Range<usize>, fn(usize) -> ParameterId>;

/// An iterator over all `Regulations` of a `RegulatoryGraph`.
pub type RegulationIterator<'a> = std::slice::Iter<'a, Regulation>;
