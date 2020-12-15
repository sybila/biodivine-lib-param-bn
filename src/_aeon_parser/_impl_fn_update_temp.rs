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
            Param(name, args) => Param(name, args),
            Var(name) => {
                if rg.find_variable(&name) != None {
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
                result.insert(Parameter {
                    name: name.clone(),
                    arity: u32::try_from(args.len()).unwrap(),
                });
            }
        }
    }

    /// Safely build an actual update function using the information from the given `BooleanNetwork`.
    ///
    /// Fail if some variable or parameter is used inconsistently with the way they appear in
    /// the network.
    pub fn into_fn_update(self, bn: &BooleanNetwork) -> Result<Box<FnUpdate>, String> {
        return Ok(Box::new(match self {
            Const(value) => FnUpdate::Const(value),
            Var(name) => FnUpdate::Var(Self::get_variable(bn, &name)?),
            Not(inner) => FnUpdate::Not(inner.into_fn_update(bn)?),
            Binary(op, l, r) => FnUpdate::Binary(op, l.into_fn_update(bn)?, r.into_fn_update(bn)?),
            Param(name, args) => {
                let parameter_id = Self::get_parameter(bn, &name)?;
                let parameter = bn.get_parameter(parameter_id);
                if parameter.arity != u32::try_from(args.len()).unwrap() {
                    return Err(format!(
                        "'{}' has cardinality {} but is used with {} arguments.",
                        name,
                        parameter.arity,
                        args.len()
                    ));
                }
                let mut arguments = Vec::with_capacity(args.len());
                for arg in args {
                    arguments.push(Self::get_variable(bn, &arg)?);
                }
                FnUpdate::Param(parameter_id, arguments)
            }
        }));
    }

    /// **(internal)** Utility method to safely obtain a variable id from a
    /// network with an appropriate error.
    fn get_variable(bn: &BooleanNetwork, name: &str) -> Result<VariableId, String> {
        if let Some(var) = bn.graph.find_variable(name) {
            Ok(var)
        } else {
            Err(format!(
                "Can't create update function. Unknown variable '{}'.",
                name
            ))
        }
    }

    fn get_parameter(bn: &BooleanNetwork, name: &str) -> Result<ParameterId, String> {
        if let Some(par) = bn.find_parameter(name) {
            Ok(par)
        } else {
            Err(format!(
                "Can't create update function. Unknown parameter '{}'.",
                name
            ))
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::_aeon_parser::FnUpdateTemp;
    use crate::{Parameter, RegulatoryGraph};
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
}
