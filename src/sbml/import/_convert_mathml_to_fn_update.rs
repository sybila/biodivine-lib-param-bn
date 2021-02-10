use crate::sbml::import::_read_mathml::MathML;
use crate::sbml::import::_read_transitions::SBMLTransition;
use crate::{BinaryOp, BooleanNetwork, FnUpdate};
use std::collections::HashMap;

/// Convert a transition into an update function.
///
/// This is basically "best effort" conversion, since a lot of this is just very vaguely
/// defined.
pub fn sbml_transition_to_update_function(
    network: &BooleanNetwork,
    transition: &SBMLTransition,
    id_to_var: &HashMap<String, String>,
) -> Result<FnUpdate, String> {
    // Recursive procedure to convert a MathML object to FnUpdate.
    fn math_to_update(
        math: &MathML,
        network: &BooleanNetwork,
        transition: &SBMLTransition,
        id_to_var: &HashMap<String, String>,
    ) -> Result<FnUpdate, String> {
        match math {
            MathML::Integer(i) => {
                if *i == 0 {
                    Ok(FnUpdate::Const(false))
                } else if *i == 1 {
                    Ok(FnUpdate::Const(true))
                } else {
                    Err(format!("Cannot convert integer `{}` to Boolean.", i))
                }
            }
            MathML::Identifier(name) => {
                let input = transition
                    .inputs
                    .iter()
                    .find(|i| i.id.as_ref().map(|id| id == name).unwrap_or(false))
                    .map(|i| i.qual_species.clone())
                    .or_else(|| id_to_var.get(name).cloned())
                    .and_then(|name| network.graph.find_variable(&name));

                if let Some(var) = input {
                    Ok(FnUpdate::Var(var))
                } else {
                    Err(format!(
                        "Identifier `{}` in transition `{}` is not an input nor a species.",
                        name, transition.id
                    ))
                }
            }
            MathML::SymbolApply(p_name, args) => {
                let mut variables = Vec::new();
                for arg in args {
                    let update = math_to_update(arg, network, transition, id_to_var)?;
                    if let FnUpdate::Var(v) = update {
                        variables.push(v);
                    } else {
                        return Err(format!("(Transition `{}`) Uninterpreted functions can have only variables as arguments.", transition.id));
                    }
                }

                // This should already be created by parent function.
                let param = network.find_parameter(p_name).unwrap();

                Ok(FnUpdate::Param(param, variables))
            }
            MathML::Apply(op, args) => {
                match op.as_str() {
                    "not" => {
                        if args.len() != 1 {
                            Err(format!(
                                "Negation operator needs exactly one argument, {} given.",
                                args.len()
                            ))
                        } else {
                            let arg = math_to_update(&args[0], network, transition, id_to_var)?;
                            Ok(FnUpdate::Not(Box::new(arg)))
                        }
                    }
                    "eq" | "neq" | "geq" | "leq" | "lt" | "gt" => {
                        // These are strictly binary.
                        if args.len() != 2 {
                            Err(format!(
                                "Operation `{}` requires exactly 2 arguments, {} given.",
                                op,
                                args.len()
                            ))
                        } else {
                            let left = math_to_update(&args[0], network, transition, id_to_var)?;
                            let right = math_to_update(&args[1], network, transition, id_to_var)?;
                            Ok(transform_comparison(op, left, right))
                        }
                    }
                    "implies" | "xor" => {
                        // These are also strictly binary, bu don't have special handling
                        if args.len() != 2 {
                            Err(format!(
                                "Operation `{}` requires exactly 2 arguments, {} given.",
                                op,
                                args.len()
                            ))
                        } else {
                            let left = math_to_update(&args[0], network, transition, id_to_var)?;
                            let right = math_to_update(&args[1], network, transition, id_to_var)?;
                            Ok(FnUpdate::Binary(
                                if op == "implies" {
                                    BinaryOp::Imp
                                } else {
                                    BinaryOp::Xor
                                },
                                Box::new(left),
                                Box::new(right),
                            ))
                        }
                    }
                    "and" | "or" => {
                        // And/Or support variable arguments because some CNF/DNF editors will output like this
                        let is_and = op == "and";
                        let op = if is_and { BinaryOp::And } else { BinaryOp::Or };
                        if args.is_empty() {
                            Ok(FnUpdate::Const(!is_and))
                        } else if args.len() == 1 {
                            math_to_update(&args[0], network, transition, id_to_var)
                        } else {
                            let mut fns = Vec::new();
                            for arg in args {
                                fns.push(math_to_update(arg, network, transition, id_to_var)?);
                            }
                            let fst = fns[0].clone();
                            Ok(fns
                                .into_iter()
                                .skip(1)
                                .fold(fst, |l, r| FnUpdate::Binary(op, Box::new(l), Box::new(r))))
                        }
                    }
                    _ => Err(format!("Unknown MathML operator `{}`.", op)),
                }
            }
        }
    }

    if transition.default_term.is_none() {
        panic!("Converting an unspecified transition to FnUpdate.");
    }

    return if transition.function_terms.is_empty() {
        if transition.default_term.as_ref().unwrap().result_level == 0 {
            Ok(FnUpdate::Const(false))
        } else if transition.default_term.as_ref().unwrap().result_level == 1 {
            Ok(FnUpdate::Const(true))
        } else {
            Err(format!(
                "Cannot convert result level {} to Boolean.",
                transition.default_term.as_ref().unwrap().result_level
            ))
        }
    } else if transition.function_terms.len() > 1 {
        Err("More than one function term is not supported at the moment.".to_string())
    } else if transition.default_term.as_ref().unwrap().result_level != 0 {
        Err("Function terms are only supported with default level 0.".to_string())
    } else {
        let term = &transition.function_terms[0];
        if term.result_level != 1 {
            Err("Function terms are only supported with result level 1.".to_string())
        } else if term.math.is_none() {
            Err("Function term has no math formula.".to_string())
        } else {
            math_to_update(term.math.as_ref().unwrap(), network, transition, id_to_var)
        }
    };
}

/// Utility function for turning comparisons into valid `FnUpdate` functions.
///
/// Allowed `op` values are `eq`, `neq`, `geq`, `leq`, `lt`, `gt`.
fn transform_comparison(op: &str, left: FnUpdate, right: FnUpdate) -> FnUpdate {
    match op {
        "gt" => transform_comparison("lt", right, left), // A > B === B < A
        "geq" => transform_comparison("leq", right, left), // A >= B === B <= A
        "neq" => {
            // A != B === !(A == B)
            let eq = transform_comparison("eq", left, right);
            // A == B might be simplified, so try to add as little bloat as possible
            if let FnUpdate::Not(inner) = eq {
                *inner
            } else if let FnUpdate::Const(b) = eq {
                FnUpdate::Const(!b)
            } else {
                FnUpdate::Not(Box::new(eq.clone()))
            }
        }
        "eq" => {
            if matches!(right, FnUpdate::Const(_)) && !matches!(left, FnUpdate::Const(_)) {
                // Push constant to left if possible
                transform_comparison("eq", right, left)
            } else if left == right {
                left
            } else if let FnUpdate::Const(true) = left {
                // 1 == A === A
                right
            } else if let FnUpdate::Const(false) = left {
                // 0 == A === !A
                FnUpdate::Not(Box::new(right))
            } else {
                FnUpdate::Binary(BinaryOp::Iff, Box::new(left), Box::new(right))
            }
        }
        "lt" => {
            // A < B === !A && B
            if let FnUpdate::Const(b) = left {
                if b {
                    // !true && B === false && B === false
                    FnUpdate::Const(false)
                } else {
                    // !false && B === true && B === B
                    right
                }
            } else if let FnUpdate::Const(b) = right {
                if b {
                    // !A && true === !A
                    FnUpdate::Not(Box::new(left))
                } else {
                    // !A && false === false
                    FnUpdate::Const(false)
                }
            } else {
                FnUpdate::Binary(
                    BinaryOp::And,
                    Box::new(FnUpdate::Not(Box::new(left))),
                    Box::new(right),
                )
            }
        }
        "leq" => {
            // A <= B === !A || B
            if let FnUpdate::Const(b) = left {
                if b {
                    // !true || B === false || B === B
                    right
                } else {
                    // !false || B === true || B === true
                    FnUpdate::Const(true)
                }
            } else if let FnUpdate::Const(b) = right {
                if b {
                    // !A || true === true
                    FnUpdate::Const(true)
                } else {
                    // !A || false == !A
                    FnUpdate::Not(Box::new(left))
                }
            } else {
                // !A || B === A implies B
                FnUpdate::Binary(BinaryOp::Imp, Box::new(left), Box::new(right))
            }
        }
        _ => panic!("Unsupported comparison {}.", op),
    }
}
