use crate::parser::{FnUpdateTemp, RegulationTemp};
use crate::{BooleanNetwork, Parameter, RegulatoryGraph};
use regex::Regex;
use std::collections::HashSet;
use std::convert::TryFrom;

impl TryFrom<&str> for BooleanNetwork {
    type Error = String;

    fn try_from(value: &str) -> Result<Self, Self::Error> {
        // trim lines and remove comments
        let lines = value.lines().filter_map(|l| {
            let line = l.trim();
            if line.is_empty() || line.chars().next() == Some('#') {
                None
            } else {
                Some(line)
            }
        });

        let mut update_functions = Vec::new();
        let mut regulations = Vec::new();

        // Regex that matches lines which define an update function.
        let function_re =
            Regex::new(r"^\$\s*(?P<name>[a-zA-Z0-9_]+)\s*:\s*(?P<function>.+)$").unwrap();

        // Split lines between update functions and regulations
        for line in lines {
            if let Some(captures) = function_re.captures(line.trim()) {
                update_functions.push((
                    captures["name"].to_string(),
                    FnUpdateTemp::try_from(&captures["function"])?,
                ));
            } else {
                regulations.push(RegulationTemp::try_from(line)?);
            }
        }

        // Build a RegulatoryGraph

        let mut variable_names = HashSet::new();
        for reg in &regulations {
            variable_names.insert(reg.regulator.clone());
            variable_names.insert(reg.target.clone());
        }
        let mut variable_names: Vec<String> = variable_names.into_iter().collect();
        variable_names.sort();

        let mut rg = RegulatoryGraph::new(variable_names);

        for reg in regulations {
            rg.add_regulation_temp(reg)?;
        }

        // Replace unknown variables with parameters
        let update_functions: Vec<(String, FnUpdateTemp)> = update_functions
            .into_iter()
            .map(|(name, fun)| (name, *fun.unknown_variables_to_parameters(&rg)))
            .collect();

        // Build a BooleanNetwork

        let mut bn = BooleanNetwork::new(rg);

        // Isolate all parameters in the network
        let mut parameters = HashSet::new();
        for (_, fun) in &update_functions {
            fun.dump_parameters(&mut parameters);
        }
        let mut parameters: Vec<Parameter> = parameters.into_iter().collect();
        parameters.sort_by_key(|p| p.name.clone());

        // Add the parameters (if there is a cardinality clash, here it will be thrown).
        for parameter in &parameters {
            bn.add_parameter(&parameter.name, parameter.arity)?;
        }

        // Actually build and add the functions
        for (name, function) in update_functions {
            bn.add_update_function_template(&name, function)?;
        }

        return Ok(bn);
    }
}

#[cfg(test)]
mod tests {
    use crate::BinaryOp::{And, Iff, Imp, Or, Xor};
    use crate::{BooleanNetwork, FnUpdate, Parameter, ParameterId, RegulatoryGraph, VariableId};
    use biodivine_lib_std::util::build_index_map;
    use std::convert::TryFrom;

    #[test]
    fn test_boolean_network_parser() {
        let bn_string = "
            a -> b
            a -?? a
            b -|? c
            a ->? c
            # Also some comments are allowed
            c -? a
            c -| d
            $a: a & (p(c) => (c | c))
            $b: p(a) <=> q(a, a)
            # Notice that a regulates c but does not appear in the function!
            $c: q(b, b) => !(b ^ k)
        ";

        let f1 = FnUpdate::Binary(
            And,
            Box::new(FnUpdate::Var(VariableId(0))),
            Box::new(FnUpdate::Binary(
                Imp,
                Box::new(FnUpdate::Param(ParameterId(1), vec![VariableId(2)])),
                Box::new(FnUpdate::Binary(
                    Or,
                    Box::new(FnUpdate::Var(VariableId(2))),
                    Box::new(FnUpdate::Var(VariableId(2))),
                )),
            )),
        );

        let f2 = FnUpdate::Binary(
            Iff,
            Box::new(FnUpdate::Param(ParameterId(1), vec![VariableId(0)])),
            Box::new(FnUpdate::Param(
                ParameterId(2),
                vec![VariableId(0), VariableId(0)],
            )),
        );

        let f3 = FnUpdate::Binary(
            Imp,
            Box::new(FnUpdate::Param(
                ParameterId(2),
                vec![VariableId(1), VariableId(1)],
            )),
            Box::new(FnUpdate::Not(Box::new(FnUpdate::Binary(
                Xor,
                Box::new(FnUpdate::Var(VariableId(1))),
                Box::new(FnUpdate::Param(ParameterId(0), Vec::new())),
            )))),
        );

        let mut rg = RegulatoryGraph::new(vec![
            "a".to_string(),
            "b".to_string(),
            "c".to_string(),
            "d".to_string(),
        ]);
        rg.add_regulation_string("a -> b").unwrap();
        rg.add_regulation_string("a -?? a").unwrap();
        rg.add_regulation_string("b -|? c").unwrap();
        rg.add_regulation_string("a ->? c").unwrap();
        rg.add_regulation_string("c -? a").unwrap();
        rg.add_regulation_string("c -| d").unwrap();

        let parameters = vec![
            Parameter {
                name: "k".to_string(),
                arity: 0,
            },
            Parameter {
                name: "p".to_string(),
                arity: 1,
            },
            Parameter {
                name: "q".to_string(),
                arity: 2,
            },
        ];

        let bn = BooleanNetwork {
            graph: rg,
            parameter_to_index: build_index_map(
                &parameters.iter().map(|p| p.name.clone()).collect(),
                |_, i| ParameterId(i),
            ),
            parameters,
            update_functions: vec![Some(f1), Some(f2), Some(f3), None],
        };

        assert_eq!(bn, BooleanNetwork::try_from(bn_string).unwrap());
    }

    #[test]
    fn test_bn_from_and_to_string() {
        let bn_string = "a -> b
a -?? a
b -|? c
c -? a
c -> d
$a: (a & (p(c) => (c | c)))
$b: (p(a) <=> q(a, a))
$c: (q(b, b) => !(b ^ k))
";

        assert_eq!(
            bn_string,
            BooleanNetwork::try_from(bn_string).unwrap().to_string()
        );
    }
}
