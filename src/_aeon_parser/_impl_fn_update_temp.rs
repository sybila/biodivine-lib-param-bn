use crate::_aeon_parser::FnUpdateTemp;
use crate::_aeon_parser::FnUpdateTemp::*;
use crate::{BooleanNetwork, FnUpdate, Parameter, ParameterId, RegulatoryGraph, VariableId};
use std::collections::HashSet;
use std::convert::TryFrom;

impl FnUpdateTemp {
    /// Replace all variables that are not valid in the given `RegulatoryGraph` with
    /// unary parameters.
    pub fn unknown_variables_to_parameters(self, rg: &RegulatoryGraph) -> Box<FnUpdateTemp> {
        Box::new(match self {
            Const(value) => Const(value),
            Binary(op, l, r) => Binary(
                op,
                l.unknown_variables_to_parameters(rg),
                r.unknown_variables_to_parameters(rg),
            ),
            Not(inner) => Not(inner.unknown_variables_to_parameters(rg)),
            Param(name, args) => {
                let args: Vec<FnUpdateTemp> = args
                    .into_iter()
                    .map(|it| *it.unknown_variables_to_parameters(rg))
                    .collect();

                Param(name, args)
            }
            Var(name) => {
                if rg.find_variable(&name).is_some() {
                    Var(name)
                } else {
                    Param(name, Vec::new())
                }
            }
        })
    }

    /// Write all parameters that appear in this function into a given set.
    ///
    /// Note that if there are parameters with the same name but different cardinality,
    /// both will appear in the set because the instances are not equivalent.
    pub fn dump_parameters(&self, result: &mut HashSet<Parameter>) {
        match self {
            Binary(_, l, r) => {
                l.dump_parameters(result);
                r.dump_parameters(result)
            }
            Not(inner) => inner.dump_parameters(result),
            Var(_) => {}
            Const(_) => {}
            Param(name, args) => {
                let arity = u32::try_from(args.len()).unwrap();
                result.insert(Parameter::new(name, arity));

                for arg in args {
                    arg.dump_parameters(result);
                }
            }
        }
    }

    /// Write all variables that appear in the function to the given set.
    pub fn dump_variables(&self, result: &mut HashSet<String>) {
        match self {
            Binary(_, l, r) => {
                l.dump_variables(result);
                r.dump_variables(result)
            }
            Not(inner) => inner.dump_variables(result),
            Var(name) => {
                result.insert(name.clone());
            }
            Const(_) => {}
            Param(_, args) => {
                for arg in args {
                    arg.dump_variables(result);
                }
            }
        }
    }

    /// Safely build an actual update function using the information from the given `BooleanNetwork`.
    ///
    /// Fail if some variable or parameter is used inconsistently with the way they appear in
    /// the network.
    pub fn into_fn_update(self, bn: &BooleanNetwork) -> Result<Box<FnUpdate>, String> {
        Ok(Box::new(match self {
            Const(value) => FnUpdate::Const(value),
            Var(name) => {
                let var = Self::get_variable(bn, &name);
                match var {
                    Ok(var) => FnUpdate::Var(var),
                    Err(e) => {
                        let param = Self::get_parameter(bn, &name);
                        if let Ok(param) = param {
                            let param_object = bn.get_parameter(param);
                            if param_object.arity > 0 {
                                return Err(format!(
                                    "Parameter `{}` has arity {}, but used with arity 0 arguments.",
                                    param_object.name, param_object.arity
                                ));
                            } else {
                                FnUpdate::Param(param, Vec::new())
                            }
                        } else {
                            return Err(e);
                        }
                    }
                }
            }
            Not(inner) => FnUpdate::Not(inner.into_fn_update(bn)?),
            Binary(op, l, r) => FnUpdate::Binary(op, l.into_fn_update(bn)?, r.into_fn_update(bn)?),
            Param(name, args) => {
                let parameter_id = Self::get_parameter(bn, &name)?;
                Self::check_parameter_arity(&bn[parameter_id], &args)?;
                let mut arguments = Vec::with_capacity(args.len());
                for arg in args {
                    arguments.push(*arg.into_fn_update(bn)?);
                }
                FnUpdate::Param(parameter_id, arguments)
            }
        }))
    }

    /// **(internal)** Utility method to safely obtain a variable id from a
    /// network with an appropriate error.
    fn get_variable(bn: &BooleanNetwork, name: &str) -> Result<VariableId, String> {
        bn.graph
            .find_variable(name)
            .ok_or_else(|| format!("Invalid update function. Unknown variable `{name}`."))
    }

    /// **(internal)** Utility method to safely obtain a parameter id from a
    /// network with an appropriate error.
    fn get_parameter(bn: &BooleanNetwork, name: &str) -> Result<ParameterId, String> {
        bn.find_parameter(name)
            .ok_or_else(|| format!("Invalid update function. Unknown parameter `{name}`."))
    }

    /// **(internal)** Generate an error message if the given `parameter` does not have
    /// arity matching the given `args` list.
    fn check_parameter_arity(parameter: &Parameter, args: &[FnUpdateTemp]) -> Result<(), String> {
        if parameter.get_arity() != u32::try_from(args.len()).unwrap() {
            Err(format!(
                "`{}` has arity {}, but is used with {} arguments.",
                parameter.get_name(),
                parameter.get_arity(),
                args.len()
            ))
        } else {
            Ok(())
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::_aeon_parser::FnUpdateTemp;
    use crate::{BooleanNetwork, Parameter, RegulatoryGraph};
    use std::collections::HashSet;
    use std::convert::TryFrom;

    #[test]
    fn test_unknown_variables_to_parameters() {
        let rg = RegulatoryGraph::new(vec![
            "abc".to_string(),
            "as123".to_string(),
            "hello".to_string(),
        ]);
        let function = FnUpdateTemp::try_from("f & (!abc | as123_param => p(abc, hello))").unwrap();
        let expected =
            FnUpdateTemp::try_from("f() & (!abc | as123_param() => p(abc, hello))").unwrap();

        assert_eq!(expected, *function.unknown_variables_to_parameters(&rg));
    }

    #[test]
    fn test_dump_parameters() {
        let function =
            FnUpdateTemp::try_from("f() & !var1 => ((par(a, b, c) | g) <=> q(a))").unwrap();
        let mut params = HashSet::new();
        function.dump_parameters(&mut params);
        let mut expected = HashSet::new();
        expected.insert(Parameter {
            name: "f".to_string(),
            arity: 0,
        });
        expected.insert(Parameter {
            name: "par".to_string(),
            arity: 3,
        });
        expected.insert(Parameter {
            name: "q".to_string(),
            arity: 1,
        });

        assert_eq!(expected, params);
    }

    #[test]
    fn translation_with_zero_arity() {
        let function =
            FnUpdateTemp::try_from("f & !var1 => ((par(a, b, c) | g) <=> q(a))").unwrap();
        let rg = RegulatoryGraph::new(vec![
            "b".to_string(),
            "c".to_string(),
            "g".to_string(),
            "var1".to_string(),
        ]);
        let mut bn = BooleanNetwork::new(rg);
        bn.add_parameter("f", 0).unwrap();
        bn.add_parameter("a", 0).unwrap();
        bn.add_parameter("par", 3).unwrap();
        bn.add_parameter("q", 1).unwrap();

        assert!(function.into_fn_update(&bn).is_ok());

        let function2 = FnUpdateTemp::try_from("f & !var1 => ((par | g) <=> q(a))").unwrap();

        assert!(function2.into_fn_update(&bn).is_err());

        let function3 =
            FnUpdateTemp::try_from("f2 & !var1 => ((par(a, b, c) | g) <=> q(a))").unwrap();

        assert!(function3.into_fn_update(&bn).is_err());
    }
}
