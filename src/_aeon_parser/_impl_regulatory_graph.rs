use crate::_aeon_parser::RegulationTemp;
use crate::RegulatoryGraph;
use std::collections::HashSet;
use std::convert::TryFrom;

/// Methods for parsing `RegulatoryGraph`s from string representations.
impl RegulatoryGraph {
    /// Create a `RegulatoryGraph` from a collection of regulation strings.
    ///
    /// The variables of the `RegulatoryGraph` are determined from the regulations
    /// and are ordered alphabetically. Otherwise, this is equivalent to iteratively
    /// calling `add_string_regulation`.
    pub fn try_from_string_regulations(
        regulations: Vec<String>,
    ) -> Result<RegulatoryGraph, String> {
        let mut templates = Vec::new();
        let mut variables = HashSet::new();
        for string in regulations {
            let template = RegulationTemp::try_from(string.as_str())?;
            variables.insert(template.regulator.clone());
            variables.insert(template.target.clone());
            templates.push(template);
        }

        let mut variables: Vec<String> = variables.into_iter().collect();
        variables.sort();

        let mut rg = RegulatoryGraph::new(variables);

        for template in templates {
            rg.add_temp_regulation(template)?;
        }

        Ok(rg)
    }

    /// Add a new `Regulation` to this `RegulatoryGraph` where the regulation is
    /// given in its string representation (e.g. "v1 ->? v2").
    ///
    /// The `regulation` parameter must be a valid string representation of a regulation,
    /// plus all conditions of `add_regulation` must be satisfied as well.
    pub fn add_string_regulation(&mut self, regulation: &str) -> Result<(), String> {
        let template = RegulationTemp::try_from(regulation)?;
        self.add_temp_regulation(template)
    }

    /// **(internal)** A utility method for adding regulations once they are parsed.
    pub(crate) fn add_temp_regulation(&mut self, regulation: RegulationTemp) -> Result<(), String> {
        self.add_regulation(
            &regulation.regulator,
            &regulation.target,
            regulation.observable,
            regulation.monotonicity,
        )
    }
}

impl TryFrom<&str> for RegulatoryGraph {
    type Error = String;

    fn try_from(value: &str) -> Result<Self, Self::Error> {
        let lines: Vec<String> = value
            .lines()
            .map(|l| l.trim().to_string())
            .filter(|l| !l.is_empty() && !l.starts_with('#'))
            .collect();

        RegulatoryGraph::try_from_string_regulations(lines)
    }
}

#[cfg(test)]
mod tests {
    use crate::Monotonicity::{Activation, Inhibition};
    use crate::{Regulation, RegulatoryGraph, Variable, VariableId};
    use std::collections::HashMap;
    use std::convert::TryFrom;

    fn make_rg() -> RegulatoryGraph {
        let mut map = HashMap::new();
        map.insert("abc".to_string(), VariableId(0));
        map.insert("hello".to_string(), VariableId(1));
        map.insert("numbers_123".to_string(), VariableId(2));
        RegulatoryGraph {
            variables: vec![
                Variable {
                    name: "abc".to_string(),
                },
                Variable {
                    name: "hello".to_string(),
                },
                Variable {
                    name: "numbers_123".to_string(),
                },
            ],
            regulations: vec![
                Regulation {
                    // abc -> hello
                    regulator: VariableId(0),
                    target: VariableId(1),
                    observable: true,
                    monotonicity: Some(Activation),
                },
                Regulation {
                    // hello -|? abc
                    regulator: VariableId(1),
                    target: VariableId(0),
                    observable: false,
                    monotonicity: Some(Inhibition),
                },
                Regulation {
                    // numbers_123 -?? abc
                    regulator: VariableId(2),
                    target: VariableId(0),
                    observable: false,
                    monotonicity: None,
                },
                Regulation {
                    // numbers_123 -? hello
                    regulator: VariableId(2),
                    target: VariableId(1),
                    observable: true,
                    monotonicity: None,
                },
            ],
            variable_to_index: map,
        }
    }

    #[test]
    fn test_regulatory_graph_from_string_with_comments() {
        let rg = RegulatoryGraph::try_from(
            "
            # Some comment
            abc -> hello
            hello -|? abc
            numbers_123 -?? abc

            # Another comment
            numbers_123 -? hello
        ",
        )
        .unwrap();
        assert_eq!(make_rg(), rg);
    }

    #[test]
    fn test_regulatory_graph_from_regulation_list() {
        let rg = RegulatoryGraph::try_from_string_regulations(vec![
            "abc -> hello".to_string(),
            "hello -|? abc".to_string(),
            "numbers_123 -?? abc".to_string(),
            "numbers_123 -? hello".to_string(),
        ]);
        assert_eq!(make_rg(), rg.unwrap());
    }

    #[test]
    fn test_regulatory_graph_from_individual_regulations() {
        let mut rg = RegulatoryGraph::new(vec![
            "abc".to_string(),
            "hello".to_string(),
            "numbers_123".to_string(),
        ]);
        rg.add_string_regulation("abc -> hello").unwrap();
        rg.add_string_regulation("hello -|? abc").unwrap();
        rg.add_string_regulation("numbers_123 -?? abc").unwrap();
        rg.add_string_regulation("numbers_123 -? hello").unwrap();
        assert_eq!(make_rg(), rg);
    }

    #[test]
    fn test_regulatory_graph_invalid_regulations() {
        let mut rg = RegulatoryGraph::new(vec!["a".to_string(), "b".to_string()]);

        assert!(rg.add_string_regulation(" a -> bb ").is_err());
        assert!(rg.add_string_regulation(" aa -> b ").is_err());
        rg.add_string_regulation(" a -> b ").unwrap();
        assert!(rg.add_string_regulation(" a -| b ").is_err());
    }
}
