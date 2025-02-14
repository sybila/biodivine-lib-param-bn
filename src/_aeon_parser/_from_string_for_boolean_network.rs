use crate::_aeon_parser::{FnUpdateTemp, RegulationTemp};
use crate::{BooleanNetwork, ModelAnnotation, Parameter, RegulatoryGraph};
use regex::Regex;
use std::collections::{HashMap, HashSet};
use std::convert::TryFrom;

impl TryFrom<&str> for BooleanNetwork {
    type Error = String;

    fn try_from(value: &str) -> Result<Self, Self::Error> {
        // This parsing should never fail, so it should be safe to do this...
        let annotations = ModelAnnotation::from_model_string(value);

        // If the model is requesting a declaration check, we should perform it. Otherwise,
        // declarations are only informative.
        let check_declarations = annotations
            .get_child(&["check_declarations"])
            .and_then(|it| it.value())
            .map(|it| it.as_str() == "true")
            .unwrap_or(false);

        // Read declared variables. Variable is declared either as a string name in the "variable"
        // annotation, or by a corresponding child annotation.
        let expected_variables = if let Some(decl) = annotations.get_child(&["variable"]) {
            let mut data = decl.read_multiline_value();
            for (child, _) in decl.children() {
                data.push(child.clone());
            }
            data
        } else {
            Vec::new()
        };

        // Try to read parameter declarations from the model annotation data. A parameter is
        // declared if it is present as a name inside "function" annotation, or if it is present
        // as one of its children. If arity is not present, it is zero.
        let expected_parameters = if let Some(decl) = annotations.get_child(&["function"]) {
            let all_names = decl.read_multiline_value();
            let mut expected = HashMap::new();
            for name in all_names {
                let arity = decl
                    .get_value(&[name.as_str(), "arity"])
                    .cloned()
                    .unwrap_or_else(|| "0".to_string());
                expected.insert(name, arity);
            }
            for (child, data) in decl.children() {
                if !expected.contains_key(child) {
                    let arity = data
                        .get_value(&["arity"])
                        .cloned()
                        .unwrap_or_else(|| "0".to_string());
                    expected.insert(child.clone(), arity);
                }
            }
            expected
        } else {
            HashMap::new()
        };

        if (!expected_variables.is_empty() || !expected_parameters.is_empty())
            && !check_declarations
        {
            eprintln!("WARNING: Network contains variable or function declarations, but integrity checking is turned off.");
        }

        // trim lines and remove comments
        let lines = value.lines().filter_map(|l| {
            let line = l.trim();
            if line.is_empty() || line.starts_with('#') {
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
        for (name, _) in &update_functions {
            variable_names.insert(name.clone());
        }
        let mut variable_names: Vec<String> = variable_names.into_iter().collect();
        variable_names.sort();

        // If a variable is declared, but not present in the graph, we can still create it.
        // But if it is present yet not declared, that's a problem.
        if check_declarations {
            for var in &variable_names {
                if !expected_variables.contains(var) {
                    return Err(format!(
                        "Variable `{}` used, but not declared in annotations.",
                        var
                    ));
                }
            }
            for var in &expected_variables {
                if !variable_names.contains(var) {
                    variable_names.push(var.clone());
                }
            }
            variable_names.sort();
        }

        let mut rg = RegulatoryGraph::new(variable_names);

        for reg in regulations {
            rg.add_temp_regulation(reg)?;
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
            if check_declarations {
                if let Some(expected_arity) = expected_parameters.get(&parameter.name) {
                    if &format!("{}", parameter.arity) != expected_arity {
                        return Err(format!(
                            "Parameter `{}` is declared with arity `{}`, but used with arity `{}`.",
                            parameter.name, expected_arity, parameter.arity
                        ));
                    }
                } else {
                    return Err(format!(
                        "Network has parameter `{}` that is not declared in annotations.",
                        parameter.name
                    ));
                }
            }
            bn.add_parameter(&parameter.name, parameter.arity)?;
        }

        if check_declarations {
            for param_name in expected_parameters.keys() {
                if bn.find_parameter(param_name).is_none() {
                    return Err(format!(
                        "Parameter `{}` declared in annotations, but not found in the network.",
                        param_name
                    ));
                }
            }
        }

        // Actually build and add the functions
        for (name, function) in update_functions {
            bn.add_template_update_function(&name, function)?;
        }

        Ok(bn)
    }
}

#[cfg(test)]
mod tests {
    use crate::biodivine_std::structs::build_index_map;
    use crate::BinaryOp::{And, Iff, Imp, Or, Xor};
    use crate::{BooleanNetwork, FnUpdate, Parameter, ParameterId, RegulatoryGraph, VariableId};
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
                Box::new(FnUpdate::Param(
                    ParameterId(1),
                    vec![FnUpdate::Var(VariableId(2))],
                )),
                Box::new(FnUpdate::Binary(
                    Or,
                    Box::new(FnUpdate::Var(VariableId(2))),
                    Box::new(FnUpdate::Var(VariableId(2))),
                )),
            )),
        );

        let f2 = FnUpdate::Binary(
            Iff,
            Box::new(FnUpdate::Param(
                ParameterId(1),
                vec![FnUpdate::Var(VariableId(0))],
            )),
            Box::new(FnUpdate::Param(
                ParameterId(2),
                vec![FnUpdate::Var(VariableId(0)), FnUpdate::Var(VariableId(0))],
            )),
        );

        let f3 = FnUpdate::Binary(
            Imp,
            Box::new(FnUpdate::Param(
                ParameterId(2),
                vec![FnUpdate::Var(VariableId(1)), FnUpdate::Var(VariableId(1))],
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
        rg.add_string_regulation("a -> b").unwrap();
        rg.add_string_regulation("a -?? a").unwrap();
        rg.add_string_regulation("b -|? c").unwrap();
        rg.add_string_regulation("a ->? c").unwrap();
        rg.add_string_regulation("c -? a").unwrap();
        rg.add_string_regulation("c -| d").unwrap();

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
                &parameters
                    .iter()
                    .map(|p| p.name.clone())
                    .collect::<Vec<_>>(),
                |_, i| ParameterId(i),
            ),
            parameters,
            update_functions: vec![Some(f1), Some(f2), Some(f3), None],
        };

        assert_eq!(bn, BooleanNetwork::try_from(bn_string).unwrap());
    }

    #[test]
    fn test_bn_from_and_to_string() {
        // Without parameters:
        let bn_string = format!(
            "#!check_declarations:true
#!variable:a
#!variable:b
#!variable:c
#!variable:d
#!version:lib_param_bn:{}

a -> b
a -?? a
b -|? c
c -? a
c -> d
$a: a & !c
$b: a
$c: !b
",
            env!("CARGO_PKG_VERSION")
        );

        assert_eq!(
            bn_string,
            BooleanNetwork::try_from(bn_string.as_str())
                .unwrap()
                .to_string()
        );

        // With parameters:
        let bn_string = format!(
            "#!check_declarations:true
#!function:k:arity:0
#!function:p:arity:1
#!function:q:arity:2
#!variable:a
#!variable:b
#!variable:c
#!variable:d
#!version:lib_param_bn:{}

a -> b
a -?? a
b -|? c
c -? a
c -> d
$a: a & (p(c) => (c | c))
$b: p(a) <=> q(a, a)
$c: q(b, b) => !(b ^ k)
",
            env!("CARGO_PKG_VERSION")
        );

        assert_eq!(
            bn_string,
            BooleanNetwork::try_from(bn_string.as_str())
                .unwrap()
                .to_string()
        );
    }

    #[test]
    fn test_bn_with_parameter_declarations() {
        let bn_string = r"
        #! check_declarations:true
        #! function: f: arity: 2
        #! variable: a
        #! variable: b
        #! variable: x
        
        a -> x
        b -> x
        $x: f(a, b)
        ";
        assert!(BooleanNetwork::try_from(bn_string).is_ok());

        // Wrong arity
        let bn_string = r"
        #! check_declarations:true
        #! function: f: arity: 1
        #! variable: a
        #! variable: b
        #! variable: x
        
        a -> x
        b -> x
        $x: f(a, b)
        ";
        assert!(BooleanNetwork::try_from(bn_string).is_err());

        // Unused declaration
        let bn_string = r"
        #! check_declarations:true
        #! function: f: arity: 2
        #! function: g: arity: 1
        #! variable: a
        #! variable: b
        #! variable: x
        
        a -> x
        b -> x
        $x: f(a, b)
        ";
        assert!(BooleanNetwork::try_from(bn_string).is_err());

        // Parameter not declared
        let bn_string = r"
        #! check_declarations:true
        #! function: f: arity: 2
        #! variable: a
        #! variable: b
        #! variable: x
        
        a -> x
        b -> x
        $x: g(a, b)
        ";
        assert!(BooleanNetwork::try_from(bn_string).is_err());
    }
}
