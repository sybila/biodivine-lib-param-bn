use crate::Monotonicity;

mod from_string_regulation_temp;
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
