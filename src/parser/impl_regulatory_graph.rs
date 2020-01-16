use crate::parser::RegulationTemp;
use crate::RegulatoryGraph;
use std::collections::HashSet;
use std::convert::TryFrom;

/// Methods for parsing `RegulatoryGraph`s from string representations.
impl RegulatoryGraph {
    /// Create a `RegulatoryGraph` from a collection of regulation strings.
    ///
    /// The variables of the `RegulatoryGraph` are determined from the regulations
    /// and are ordered alphabetically. Otherwise, this is equivalent to iteratively
    /// calling `add_regulation_string`.
    pub fn from_regulation_strings(regulations: Vec<String>) -> Result<RegulatoryGraph, String> {
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
            rg.add_regulation(
                &template.regulator,
                &template.target,
                template.observable,
                template.monotonicity,
            )?;
        }

        return Ok(rg);
    }

    /// Add a new `Regulation` to this `RegulatoryGraph` where the regulation is
    /// given in its string representation (e.g. "v1 ->? v2").
    ///
    /// The `regulation` parameter must be a valid string representation of a regulation,
    /// plus all conditions of `add_regulation` must be satisfied as well.
    pub fn add_regulation_string(&mut self, regulation: &str) -> Result<(), String> {
        let template = RegulationTemp::try_from(regulation)?;
        return self.add_regulation(
            &template.regulator,
            &template.target,
            template.observable,
            template.monotonicity,
        );
    }
}

impl TryFrom<&str> for RegulatoryGraph {
    type Error = String;

    fn try_from(value: &str) -> Result<Self, Self::Error> {
        let lines: Vec<String> = value
            .lines()
            .map(|l| l.trim().to_string())
            .filter(|l| !l.is_empty() && l.chars().next() != Some('#'))
            .collect();

        return RegulatoryGraph::from_regulation_strings(lines);
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
        return RegulatoryGraph {
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
        };
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
        let rg = RegulatoryGraph::from_regulation_strings(vec![
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
        rg.add_regulation_string("abc -> hello").unwrap();
        rg.add_regulation_string("hello -|? abc").unwrap();
        rg.add_regulation_string("numbers_123 -?? abc").unwrap();
        rg.add_regulation_string("numbers_123 -? hello").unwrap();
        assert_eq!(make_rg(), rg);
    }

    #[test]
    fn test_regulatory_graph_invalid_regulations() {
        let mut rg = RegulatoryGraph::new(vec!["a".to_string(), "b".to_string()]);

        assert!(rg.add_regulation_string(" a -> bb ").is_err());
        assert!(rg.add_regulation_string(" aa -> b ").is_err());
        rg.add_regulation_string(" a -> b ").unwrap();
        assert!(rg.add_regulation_string(" a -| b ").is_err());
    }
}
