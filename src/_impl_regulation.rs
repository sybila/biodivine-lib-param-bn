use crate::{Monotonicity, Regulation, RegulatoryGraph, VariableId, ID_REGEX_STR};
use regex::Regex;

/// **(internal)** Regex which matches the regulation arrow string with `monotonicity`
/// and `observable` groups.
const REGULATION_ARROW_REGEX_STR: &str = r"-(?P<monotonicity>[|>?])(?P<observable>\??)";

lazy_static! {
    /// **(internal)** A regex which reads one line specifying a regulation.
    static ref REGULATION_REGEX: Regex = Regex::new(
        format!(
            // regulator ID, whitespace?, arrow string, whitespace?, target ID
            r"^(?P<regulator>{ID_REGEX_STR})\s*{REGULATION_ARROW_REGEX_STR}\s*(?P<target>{ID_REGEX_STR})$",
        ).as_str()
    ).unwrap();
}

/// Basic getters.
impl Regulation {
    /// Check if the regulation is marked as observable.
    pub fn is_observable(&self) -> bool {
        self.observable
    }

    /// Return monotonicity of the regulation (if specified).
    pub fn get_monotonicity(&self) -> Option<Monotonicity> {
        self.monotonicity
    }

    /// Get the `VariableId` if the regulator.
    pub fn get_regulator(&self) -> VariableId {
        self.regulator
    }

    /// Get the `VariableId` of the target.
    pub fn get_target(&self) -> VariableId {
        self.target
    }
}

/// Serialization utility methods.
impl Regulation {
    /// Try to read all available information about a regulation from a given string
    /// in the standard format.
    ///
    /// The returned data correspond to the items as they appear in the string, i.e. `regulator`,
    /// `monotonicity`, `observability` and `target`. If the string is not valid, returns `None`.
    pub fn try_from_string(
        regulation: &str,
    ) -> Option<(String, Option<Monotonicity>, bool, String)> {
        REGULATION_REGEX
            .captures(regulation.trim())
            .map(|captures| {
                let monotonicity = match &captures["monotonicity"] {
                    "?" => None,
                    "|" => Some(Monotonicity::Inhibition),
                    ">" => Some(Monotonicity::Activation),
                    _ => unreachable!("Nothing else matches this group."),
                };
                let observable = captures["observable"].is_empty();
                (
                    captures["regulator"].to_string(),
                    monotonicity,
                    observable,
                    captures["target"].to_string(),
                )
            })
    }

    /// Convert to standard string format using variable names provided by a `RegulatoryGraph`.
    pub fn to_string(&self, context: &RegulatoryGraph) -> String {
        let monotonicity = match self.get_monotonicity() {
            None => "?",
            Some(Monotonicity::Activation) => ">",
            Some(Monotonicity::Inhibition) => "|",
        };
        let observability = if self.is_observable() { "" } else { "?" };
        format!(
            "{} -{}{} {}",
            context.get_variable_name(self.regulator),
            monotonicity,
            observability,
            context.get_variable_name(self.target)
        )
    }
}

#[cfg(test)]
mod tests {
    use crate::{BooleanNetwork, Regulation};
    use std::convert::TryFrom;

    #[test]
    fn regulation_conversion() {
        let bn = BooleanNetwork::try_from(
            r"
            a -?? b
            b -? c
            c ->? d
            d -> e
            e -|? f
            f -| g
        ",
        )
        .unwrap();

        for regulation in bn.graph.regulations() {
            let (r, m, o, t) =
                Regulation::try_from_string(&regulation.to_string(bn.as_graph())).unwrap();
            assert_eq!(&r, bn.get_variable_name(regulation.get_regulator()));
            assert_eq!(&t, bn.get_variable_name(regulation.get_target()));
            assert_eq!(m, regulation.get_monotonicity());
            assert_eq!(o, regulation.is_observable());
        }

        assert_eq!(None, Regulation::try_from_string("a --> b"));
    }
}
