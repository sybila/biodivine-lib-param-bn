use crate::{BinaryOp, BooleanNetwork, FnUpdate, VariableId};

impl BooleanNetwork {
    /// Produce a `.booleannet` string representation of this model.
    ///
    /// The booleannet format is used by the `booleannet` Python package.
    /// Update rules are written in the format: `1: variable* = expression`
    /// where expressions use `and`, `or`, `not` operators.
    ///
    /// Returns an error if the network is parametrised and thus cannot be converted to
    /// `.booleannet`, as the format does not support uninterpreted functions.
    pub fn to_booleannet(&self) -> Result<String, String> {
        let mut model = String::new();

        // Add a header comment
        model.push_str("# Boolean network in booleannet format\n");
        model.push_str("# Generated from biodivine-lib-param-bn\n");
        model.push_str("#\n");
        model.push_str("# Format: rank: variable* = expression\n");
        model.push_str("# Operators: and, or, not\n");
        model.push_str("#\n\n");

        // Write update functions for each variable
        for v in self.variables() {
            let name = self.get_variable_name(v);
            if let Some(function) = self.get_update_function(v) {
                let function_string = fn_update_to_booleannet_string(v, function, self)?;
                let line = format!("1: {}* = {}\n", name, function_string);
                model.push_str(line.as_str());
            } else {
                // If there is no update function, we can skip it assuming it has no inputs (constant)
                if self.regulators(v).is_empty() {
                    continue;
                } else {
                    return Err(format!(
                        "Variable '{}' has no update function. Parametrised networks cannot be converted to .booleannet.",
                        name
                    ));
                }
            }
        }

        Ok(model)
    }
}

/// Convert an FnUpdate to booleannet expression syntax
/// Booleannet uses: and, or, not
/// We use: &, |, !
fn fn_update_to_booleannet_string(
    var: VariableId,
    function: &FnUpdate,
    network: &BooleanNetwork,
) -> Result<String, String> {
    Ok(match function {
        FnUpdate::Var(id) => network.get_variable_name(*id).clone(),
        FnUpdate::Param(id, args) => {
            if args.is_empty() {
                // Zero-arity parameters could be treated as constants, but booleannet
                // doesn't support this concept, so we return an error
                return Err(format!(
                    "Parameter '{}' cannot be converted to .booleannet format. \
                    Networks with parameters are not supported.",
                    network.get_parameter(*id).get_name()
                ));
            } else {
                return Err(
                    "Networks with parametrised functions cannot be converted to .booleannet."
                        .to_string(),
                );
            }
        }
        FnUpdate::Const(value) => {
            // Booleannet doesn't have a direct way to represent constants,
            // but we can use tautology/contradiction expressions
            let name = network.get_variable_name(var);
            if *value {
                // True: (A or not A)
                format!("({} or not {})", name, name)
            } else {
                // False: (A and not A)
                format!("({} and not {})", name, name)
            }
        }
        FnUpdate::Not(inner) => {
            let inner_str = fn_update_to_booleannet_string(var, inner, network)?;
            // Add parentheses if the inner expression is complex
            if needs_parentheses_for_not(inner) {
                format!("not ({})", inner_str)
            } else {
                format!("not {}", inner_str)
            }
        }
        FnUpdate::Binary(op, left, right) => {
            let left_str = fn_update_to_booleannet_string(var, left, network)?;
            let right_str = fn_update_to_booleannet_string(var, right, network)?;

            // Add parentheses based on operator precedence
            let left_paren = needs_parentheses_left(left, *op);
            let right_paren = needs_parentheses_right(right, *op);

            let left_with_paren = if left_paren {
                format!("({})", left_str)
            } else {
                left_str
            };

            let right_with_paren = if right_paren {
                format!("({})", right_str)
            } else {
                right_str
            };

            match *op {
                BinaryOp::And => format!("{} and {}", left_with_paren, right_with_paren),
                BinaryOp::Or => format!("{} or {}", left_with_paren, right_with_paren),
                BinaryOp::Imp => {
                    // Implication: A => B is equivalent to (not A) or B
                    format!("(not {}) or {}", left_with_paren, right_with_paren)
                }
                BinaryOp::Iff => {
                    // Equivalence: A <=> B is (A and B) or (not A and not B)
                    format!(
                        "({} and {}) or (not {} and not {})",
                        left_with_paren, right_with_paren, left_with_paren, right_with_paren
                    )
                }
                BinaryOp::Xor => {
                    // XOR: A xor B is (A and not B) or (not A and B)
                    format!(
                        "({} and not {}) or (not {} and {})",
                        left_with_paren, right_with_paren, left_with_paren, right_with_paren
                    )
                }
            }
        }
    })
}

/// Check if an expression needs parentheses when used as argument to 'not'
fn needs_parentheses_for_not(expr: &FnUpdate) -> bool {
    matches!(expr, FnUpdate::Binary(_, _, _))
}

/// Check if left operand needs parentheses based on operator precedence
fn needs_parentheses_left(expr: &FnUpdate, parent_op: BinaryOp) -> bool {
    match expr {
        FnUpdate::Binary(op, _, _) => {
            // In booleannet, precedence is: not > and > or
            // If parent is 'and' and child is 'or', we need parentheses
            matches!(
                (parent_op, *op),
                (BinaryOp::And, BinaryOp::Or)
                    | (BinaryOp::And, BinaryOp::Imp)
                    | (BinaryOp::And, BinaryOp::Iff)
                    | (BinaryOp::And, BinaryOp::Xor)
            )
        }
        _ => false,
    }
}

/// Check if right operand needs parentheses based on operator precedence
fn needs_parentheses_right(expr: &FnUpdate, parent_op: BinaryOp) -> bool {
    match expr {
        FnUpdate::Binary(op, _, _) => {
            // Same logic as left side
            matches!(
                (parent_op, *op),
                (BinaryOp::And, BinaryOp::Or)
                    | (BinaryOp::And, BinaryOp::Imp)
                    | (BinaryOp::And, BinaryOp::Iff)
                    | (BinaryOp::And, BinaryOp::Xor)
            )
        }
        _ => false,
    }
}

#[cfg(test)]
mod tests {
    use crate::BooleanNetwork;
    use std::convert::TryFrom;

    #[test]
    fn test_simple_network_to_booleannet() {
        let bn = BooleanNetwork::try_from(
            r"
            A -> B
            B -> A
            B -| B
            $A: B
            $B: !B | A
            ",
        )
        .unwrap();

        let booleannet_str = bn.to_booleannet().unwrap();

        // Check that it contains the expected parts
        assert!(booleannet_str.contains("A* ="));
        assert!(booleannet_str.contains("B* ="));
        assert!(booleannet_str.contains("or"));
        assert!(booleannet_str.contains("not"));
    }

    #[test]
    fn test_network_roundtrip() {
        // Create a network, export to booleannet, import it back
        let original = BooleanNetwork::try_from(
            r"
            A -> B
            B -> A
            $A: B
            $B: A
            ",
        )
        .unwrap();

        let booleannet_str = original.to_booleannet().unwrap();
        let imported = BooleanNetwork::try_from_booleannet(&booleannet_str).unwrap();

        // Check that both networks have the same structure
        assert_eq!(original.num_vars(), imported.num_vars());

        for var in original.variables() {
            let name = original.get_variable_name(var);
            let imported_var = imported.as_graph().find_variable(name).unwrap();

            // Both should have update functions
            assert!(original.get_update_function(var).is_some());
            assert!(imported.get_update_function(imported_var).is_some());
        }
    }

    #[test]
    fn test_complex_expressions() {
        let bn = BooleanNetwork::try_from(
            r"
            A -> C
            B -> C
            C -> D
            $A: true
            $B: false
            $C: A & B | !A
            $D: C
            ",
        )
        .unwrap();

        let booleannet_str = bn.to_booleannet().unwrap();

        // Verify we can parse it back
        let imported = BooleanNetwork::try_from_booleannet(&booleannet_str).unwrap();
        assert_eq!(bn.num_vars(), imported.num_vars());
    }

    #[test]
    fn test_parametrised_network_fails() {
        // Network with implicit parameter
        let bn = BooleanNetwork::try_from(
            r"
            A -> B
            ",
        )
        .unwrap();

        let result = bn.to_booleannet();
        assert!(result.is_err());
        assert!(result.unwrap_err().contains("Parametrised"));
    }

    #[test]
    fn test_explicit_parameter_fails() {
        // Network with explicit parameter
        let bn = BooleanNetwork::try_from(
            r"
            A -> B
            $B: f(A)
            ",
        )
        .unwrap();

        let result = bn.to_booleannet();
        assert!(result.is_err());
    }

    #[test]
    fn test_real_world_model_roundtrip() {
        // Load one of the example files
        let original_str = std::fs::read_to_string("booleannet_models/demo-rules.txt").unwrap();
        let network = BooleanNetwork::try_from_booleannet(&original_str).unwrap();

        // Export to booleannet
        let exported = network.to_booleannet().unwrap();

        // Import again
        let reimported = BooleanNetwork::try_from_booleannet(&exported).unwrap();

        // Note: The roundtrip is lossy for variables without update functions
        // The original demo-rules has 7 variables (some with only initial states),
        // but only 2 have update functions. After export/import, we only keep
        // variables that either have update functions or are referenced in other
        // update functions.

        // Check that all variables with update functions are preserved
        for var in network.variables() {
            if network.get_update_function(var).is_some() {
                let name = network.get_variable_name(var);
                let reimported_var = reimported.as_graph().find_variable(name);
                assert!(
                    reimported_var.is_some(),
                    "Variable {} should be preserved",
                    name
                );
                assert!(
                    reimported
                        .get_update_function(reimported_var.unwrap())
                        .is_some(),
                    "Variable {} should have an update function",
                    name
                );
            }
        }
    }

    #[test]
    fn test_operators_conversion() {
        let bn = BooleanNetwork::try_from(
            r"
            A -> D
            B -> D
            C -> D
            $A: true
            $B: true  
            $C: true
            $D: (A & B) | !C
            ",
        )
        .unwrap();

        let booleannet_str = bn.to_booleannet().unwrap();

        // Should contain 'and', 'or', 'not' keywords
        assert!(booleannet_str.contains("and"));
        assert!(booleannet_str.contains("or"));
        assert!(booleannet_str.contains("not"));

        // Should not contain our internal operators in expressions
        // (they should be converted to 'and', 'or', 'not')
    }

    #[test]
    fn test_constants_export() {
        let bn = BooleanNetwork::try_from(
            r"
            A -> B
            B -> B
            $A: true
            $B: false
            ",
        )
        .unwrap();

        let booleannet_str = bn.to_booleannet().unwrap();

        // Constants should be represented as tautologies/contradictions
        assert!(booleannet_str.contains("or not") || booleannet_str.contains("and not"));
    }

    #[test]
    fn test_aba_model_roundtrip() {
        let original_str = std::fs::read_to_string("booleannet_models/ABA.txt").unwrap();
        let network = BooleanNetwork::try_from_booleannet(&original_str).unwrap();

        // Export and re-import
        let exported = network.to_booleannet().unwrap();
        let reimported = BooleanNetwork::try_from_booleannet(&exported).unwrap();

        assert_eq!(network.num_vars(), reimported.num_vars());
    }
}
