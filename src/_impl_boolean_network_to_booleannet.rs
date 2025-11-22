use crate::BinaryOp::{And, Iff, Imp, Or, Xor};
use crate::FnUpdate::*;
use crate::{BooleanNetwork, FnUpdate};

impl BooleanNetwork {
    /// Convert the `BooleanNetwork` into a `booleannet` format string.
    ///
    /// This will try to use `and`, `or`, `not` operators. Other operators (`xor`, `iff`, `imp`)
    /// are expanded into equivalent expressions using `and`/`or`/`not`.
    pub fn to_booleannet(&self) -> String {
        let mut output = String::new();

        // Write initialization (optional but good for explicitly listing variables)
        // We can write variables as True/False/Random if we knew their state, but here we define structure.
        // booleannet requires initialization for variables?
        // "Node initialization below, (all other nodes are set to random values in the program)"
        // If we don't initialize, they might be random.
        // However, we can just output update rules.

        // Header
        output.push_str("# Boolean network model\n");

        let mut vars: Vec<_> = self.variables().collect();
        vars.sort();

        for v in vars {
            if let Some(update_fn) = self.get_update_function(v) {
                let name = self.get_variable_name(v);
                let expression = fn_update_to_booleannet(update_fn, self);
                output.push_str(&format!("1: {}* = {}\n", name, expression));
            }
        }

        output
    }
}

fn fn_update_to_booleannet(func: &FnUpdate, bn: &BooleanNetwork) -> String {
    match func {
        Const(value) => {
            if *value {
                "True".to_string()
            } else {
                "False".to_string()
            }
        }
        Var(id) => bn.get_variable_name(*id).clone(),
        Param(id, args) => {
            // Parameters are treated as uninterpreted functions.
            // Booleannet doesn't strictly support them as function calls in standard logic,
            // but if we want to support them, we can output them as name(args).
            // However, booleannet might not parse them.
            // Assuming we stick to standard boolean logic for now.
            let name = bn.get_parameter(*id).name.clone();
            if args.is_empty() {
                name
            } else {
                let args_str: Vec<String> = args
                    .iter()
                    .map(|arg| fn_update_to_booleannet(arg, bn))
                    .collect();
                format!("{}({})", name, args_str.join(", "))
            }
        }
        Not(inner) => {
            format!("not {}", fn_update_to_booleannet(inner, bn)) // Parentheses might be needed?
            // "not A" is fine. "not (A and B)" is needed.
            // Let's be safe and use parentheses for inner unless it's a var or const.
        }
        Binary(op, l, r) => {
            match op {
                And => {
                    let l_str = fn_update_to_booleannet_paren(l, bn);
                    let r_str = fn_update_to_booleannet_paren(r, bn);
                    format!("{} and {}", l_str, r_str)
                }
                Or => {
                    let l_str = fn_update_to_booleannet_paren(l, bn);
                    let r_str = fn_update_to_booleannet_paren(r, bn);
                    format!("{} or {}", l_str, r_str)
                }
                Imp => {
                    // A => B  ==  not A or B
                    let l_str = fn_update_to_booleannet_paren(l, bn);
                    let r_str = fn_update_to_booleannet_paren(r, bn);
                    format!("(not {}) or {}", l_str, r_str)
                }
                Iff => {
                    // A <=> B == (A and B) or (not A and not B)
                    // Or (A and B) or not (A or B)
                    // Let's use equality if booleannet supports it? No.
                    let l_str = fn_update_to_booleannet_paren(l, bn);
                    let r_str = fn_update_to_booleannet_paren(r, bn);
                    format!(
                        "({} and {}) or (not {} and not {})",
                        l_str, r_str, l_str, r_str
                    )
                }
                Xor => {
                    // A ^ B == (A and not B) or (not A and B)
                    let l_str = fn_update_to_booleannet_paren(l, bn);
                    let r_str = fn_update_to_booleannet_paren(r, bn);
                    format!(
                        "({} and not {}) or (not {} and {})",
                        l_str, r_str, l_str, r_str
                    )
                }
            }
        }
    }
}

fn fn_update_to_booleannet_paren(func: &FnUpdate, bn: &BooleanNetwork) -> String {
    match func {
        Const(_) | Var(_) | Param(_, _) => fn_update_to_booleannet(func, bn),
        _ => format!("({})", fn_update_to_booleannet(func, bn)),
    }
}

#[cfg(test)]
mod tests {
    use crate::BooleanNetwork;

    #[test]
    fn test_to_booleannet() {
        let model = r#"
        1: A* = B and C
        1: B* = not A
        "#;
        // We parse it first (assuming try_from_booleannet works from previous step)
        let bn = BooleanNetwork::try_from_booleannet(model).unwrap();
        let output = bn.to_booleannet();

        assert!(output.contains("A* = B and C") || output.contains("A* = (B) and (C)"));
        assert!(output.contains("B* = not A") || output.contains("B* = not (A)"));
    }
}
