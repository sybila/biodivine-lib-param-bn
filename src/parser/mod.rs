use crate::{BinaryOp, Monotonicity};

mod display_fn_update_temp;
mod from_string_boolean_network;
mod from_string_fn_update_temp;
mod from_string_regulation_temp;
mod impl_boolean_network;
mod impl_fn_update_temp;
mod impl_regulatory_graph;

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
enum FnUpdateTemp {
    Var(String),
    Param(String, Vec<String>),
    Not(Box<FnUpdateTemp>),
    Binary(BinaryOp, Box<FnUpdateTemp>, Box<FnUpdateTemp>),
}
