use crate::{BinaryOp, Monotonicity};

/// **(internal)** Convert `FnUpdateTemp` back to boolean expression.
mod _display_fn_update_temp;
/// **(internal)** `BooleanNetwork` parsing.
mod _from_string_for_boolean_network;
/// **(internal)** `FnUpdateTemp` parsing.
mod _from_string_for_fn_update_temp;
/// **(internal)** `RegulatoryGraph` parsing.
mod _from_string_for_regulation_temp;
/// **(internal)** Parsing utility methods for the `BooleanNetwork`.
mod _impl_boolean_network;
/// **(internal)** Implementation of `FnUpdateTemp`.
mod _impl_fn_update_temp;
/// **(internal)** Parsing utility methods for the `RegulatoryGraph`.
mod _impl_regulatory_graph;

/// **(internal)** A helper struct for representing parsed `Regulation`s that have not been
/// integrated into a `RegulatoryGraph` yet.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
struct RegulationTemp {
    regulator: String,
    target: String,
    observable: bool,
    monotonicity: Option<Monotonicity>,
}

/// **(internal)** A helper enum for representing parsed `FnUpdate`s that have not been
/// integrated into a `BooleanNetwork` yet.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub(super) enum FnUpdateTemp {
    Const(bool),
    Var(String),
    Param(String, Vec<String>),
    Not(Box<FnUpdateTemp>),
    Binary(BinaryOp, Box<FnUpdateTemp>, Box<FnUpdateTemp>),
}
