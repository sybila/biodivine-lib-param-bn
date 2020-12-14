use std::collections::HashMap;
use std::iter::Map;
use std::ops::Range;

pub mod async_graph;
pub mod bdd_params;
mod display_boolean_network;
mod display_regulatory_graph;
mod impl_binary_op;
mod impl_boolean_network;
mod impl_fn_update;
mod impl_parameter;
mod impl_regulation;
mod impl_regulatory_graph;
mod impl_variable;
mod impl_variable_id;
mod parser;
pub mod sbml;
pub mod symbolic_async_graph;

// TODO: Getters for properties of Variables, Parameters, Regulations, ...

/// A type-safe index of a `Variable` inside a `BooleanNetwork` (or a `RegulatoryGraph`).
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct VariableId(usize);

/// A type-safe index of a `Parameter` inside a `BooleanNetwork`.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ParameterId(usize);

/// Possible monotonous effects of a `Regulation` in a `BooleanNetwork`.
///
/// Activation means increasing monotonicity and inhibition means decreasing
/// monotonicity.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Monotonicity {
    Activation,
    Inhibition,
}

/// A variable of a `BooleanNetwork`.
///
/// Variable has a `name` and can have value either true or zero.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Variable {
    name: String,
}

/// A parameter of a `BooleanNetwork`.
///
/// Parameter is an uninterpreted boolean function with a fixed cardinality.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct Parameter {
    name: String,
    arity: u32,
}

/// Describes an interaction relationship between two `Variable`s in a `BooleanNetwork`
/// (or a `RegulatoryGraph`).
///
/// Every regulation can be monotonous and can be marked as `observable`.
/// Observability means that the regulation must manifest itself somewhere in the
/// corresponding update function (i.e. there is a context in which changing just
/// the value of `regulator` changes the value of `target`).
///
/// Regulations can be represented as strings in the
/// form `"regulator_name 'relationship' target_name"`. The 'relationship' is one of the arrows:
/// `->, ->?, -|, -|?, -?, -??`. Here,`>` means activation, `|` is inhibition and `?` is
/// not monotonous. The last question mark signifies observability — if it is present, the
/// regulation is not necessarily observable.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct Regulation {
    regulator: VariableId,
    target: VariableId,
    observable: bool,
    monotonicity: Option<Monotonicity>,
}

/// A partial representation of a `BooleanNetwork`, `RegulatoryGraph` contains information
/// about the general structure of the network but lacks the concrete update functions
/// of individual variables.
///
/// Incidentally, regulatory graph corresponds to the part of the network that can be
/// drawn as a graph of variables and regulations.
///
/// A regulatory graph can be described using a custom string format. In this format,
/// each line represents a regulation or a comment (starting with `#`).
///
/// Regulations can be represented as strings in the
/// form `"regulator_name 'relationship' target_name"`. The 'relationship' is one of the arrows:
/// `->, ->?, -|, -|?, -?, -??`. Here,`>` means activation, `|` is inhibition and `?` is
/// not monotonous. The last question mark signifies observability — if it is present, the
/// regulation is not necessarily observable.
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

/// Possible binary boolean operators that can appear in `FnUpdate`.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum BinaryOp {
    And,
    Or,
    Xor,
    Iff,
    Imp,
}

/// A boolean formula which references `Variable`s and `Parameter`s of the associated
/// `BooleanNetwork`.
///
/// An update function specifies the evolution rules for one specific `Variable` of a
/// `BooleanNetwork`. The cardinality of the function must be the same as specified
/// by the `RegulatoryGraph` if the network.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub enum FnUpdate {
    Const(bool),
    // Variable references an actual variable of the network.
    Var(VariableId),
    // Parameter references a parameter of the network together with variables that are
    // be used as arguments to the parameter function.
    Param(ParameterId, Vec<VariableId>),
    Not(Box<FnUpdate>),
    Binary(BinaryOp, Box<FnUpdate>, Box<FnUpdate>),
}

/// A boolean network parametrised with uninterpreted boolean functions.
///
/// If an update function for a specific variable is not set, we assume the whole
/// function is an implicit parameter (cardinality of which is inferred from the
/// regulatory graph).
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct BooleanNetwork {
    graph: RegulatoryGraph,
    parameters: Vec<Parameter>,
    update_functions: Vec<Option<FnUpdate>>,
    parameter_to_index: HashMap<String, ParameterId>,
}

/// An iterator over all `VariableId`s of a `RegulatoryGraph`.
pub type VariableIdIterator = Map<Range<usize>, fn(usize) -> VariableId>;

/// An iterator over all `ParameterId`s of a `BooleanNetwork`.
pub type ParameterIdIterator = Map<Range<usize>, fn(usize) -> ParameterId>;
