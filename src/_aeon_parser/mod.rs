use crate::{BinaryOp, Monotonicity};

/// **(internal)** Convert `FnUpdateTemp` back to Boolean expression string.
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

// Re-export ExpressionSyntax for use in BooleanNet parsing
pub(crate) use _from_string_for_fn_update_temp::ExpressionSyntax;

/// **(internal)** A helper struct for representing a parsed `Regulation` that has not been
/// integrated into a `RegulatoryGraph` yet.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub(crate) struct RegulationTemp {
    regulator: String,
    target: String,
    observable: bool,
    monotonicity: Option<Monotonicity>,
}

/// **(internal)** A helper enum for representing a parsed `FnUpdate` that has not been
/// integrated into a `BooleanNetwork` yet.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub(crate) enum FnUpdateTemp {
    Const(bool),
    Var(String),
    Param(String, Vec<FnUpdateTemp>),
    Not(Box<FnUpdateTemp>),
    Binary(BinaryOp, Box<FnUpdateTemp>, Box<FnUpdateTemp>),
}
