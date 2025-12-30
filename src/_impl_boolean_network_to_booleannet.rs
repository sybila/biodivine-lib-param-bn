use crate::{BinaryOp, BooleanNetwork, FnUpdate};
use std::collections::HashMap;

/// Placeholder for the `__plus__` escape sequence.
const PLUS_ESCAPE: &str = "__plus__";
/// Placeholder for the `__minus__` escape sequence.
const MINUS_ESCAPE: &str = "__minus__";

impl BooleanNetwork {
    /// Produce a BooleanNet format string representation of this model.
    ///
    /// BooleanNet format uses keyword-based operators (`and`, `or`, `not`) and capitalized
    /// literals (`True`, `False`). Update rules are written as `VAR* = expression`.
    ///
    /// **Important notes:**
    /// - Returns an error if the network contains explicit parameters (uninterpreted functions),
    ///   as BooleanNet does not support parametrized networks.
    /// - Implicit parameters (missing update functions) also cause an error.
    ///
    /// **Variable name handling:**
    /// If `original_names` is provided (typically from [`BooleanNetwork::try_from_booleannet`]),
    /// the names will be restored to their original BooleanNet form (e.g., `Ca2__plus__c` -> `Ca2+c`).
    /// If not provided, the function will attempt to reverse the sanitization heuristically
    /// by replacing `__plus__` with `+` and `__minus__` with `-`.
    ///
    /// # Arguments
    /// * `original_names` - Optional mapping from sanitized names to original BooleanNet names.
    ///
    /// # Returns
    /// A string containing the BooleanNet representation of the network.
    pub fn to_booleannet(
        &self,
        original_names: Option<&HashMap<String, String>>,
    ) -> Result<String, String> {
        // Check that the network is fully specified (no parameters, all functions defined)
        if self.num_parameters() > 0 {
            return Err(
                "Parametrised network cannot be converted to BooleanNet format.".to_string(),
            );
        }

        for var in self.variables() {
            if self.get_update_function(var).is_none() {
                let name = self.get_variable_name(var);
                return Err(format!(
                    "Variable '{}' has no update function. BooleanNet format requires all variables to have update functions.",
                    name
                ));
            }
        }

        let mut output = String::new();

        // Write update rules
        for var in self.variables() {
            let internal_name = self.get_variable_name(var);
            let display_name = restore_name(internal_name, original_names);

            if let Some(function) = self.get_update_function(var) {
                let function_str = fn_update_to_booleannet_string(function, self, original_names)?;
                output.push_str(&format!("{}* = {}\n", display_name, function_str));
            }
        }

        Ok(output)
    }
}

/// Convert an FnUpdate to a BooleanNet-style expression string.
fn fn_update_to_booleannet_string(
    function: &FnUpdate,
    network: &BooleanNetwork,
    original_names: Option<&HashMap<String, String>>,
) -> Result<String, String> {
    Ok(match function {
        FnUpdate::Var(id) => {
            let internal_name = network.get_variable_name(*id);
            restore_name(internal_name, original_names)
        }
        FnUpdate::Param(id, args) => {
            return if args.is_empty() {
                // Zero-arity parameter - treat as a named constant, but BooleanNet doesn't support this
                let param_name = network.get_parameter(*id).get_name();
                Err(format!(
                    "Cannot convert parameter '{}' to BooleanNet format. BooleanNet does not support parameters.",
                    param_name
                ))
            } else {
                Err(
                    "Networks with uninterpreted functions cannot be converted to BooleanNet format.".to_string(),
                )
            };
        }
        FnUpdate::Const(value) => {
            if *value {
                "True".to_string()
            } else {
                "False".to_string()
            }
        }
        FnUpdate::Not(inner) => {
            let inner_str = fn_update_to_booleannet_string(inner, network, original_names)?;
            // Add parentheses if the inner is a binary operation since `not` binds tightly
            let inner_str = parenthesize_if_binary(&inner_str, inner);
            format!("not {}", inner_str)
        }
        FnUpdate::Binary(op, left, right) => {
            let left_str = fn_update_to_booleannet_string(left, network, original_names)?;
            let right_str = fn_update_to_booleannet_string(right, network, original_names)?;

            // Wrap operands in parentheses if they are binary operations with lower precedence
            let left_str_precedence = maybe_parenthesize(&left_str, left, *op);
            let right_str_precedence = maybe_parenthesize(&right_str, right, *op);

            match *op {
                BinaryOp::And => format!("{} and {}", left_str_precedence, right_str_precedence),
                BinaryOp::Or => format!("{} or {}", left_str_precedence, right_str_precedence),
                // BooleanNet doesn't have Xor, Imp, Iff - we need to expand them.
                // For these expansions, we need to parenthesize operands appropriately:
                // - When appearing after `not`: parenthesize if binary (not with the highest precedence)
                // - When appearing in `and` context: parenthesize if lower precedence than and
                BinaryOp::Xor => {
                    // `a XOR b` = `(a and not b) or (not a and b)`
                    let left_for_and = maybe_parenthesize(&left_str, left, BinaryOp::And);
                    let right_for_and = maybe_parenthesize(&right_str, right, BinaryOp::And);
                    let left_for_not = parenthesize_if_binary(&left_str, left);
                    let right_for_not = parenthesize_if_binary(&right_str, right);
                    format!(
                        "({} and not {}) or (not {} and {})",
                        left_for_and, right_for_not, left_for_not, right_for_and
                    )
                }
                BinaryOp::Imp => {
                    // `a => b` = `not a or b`
                    let left_for_not = parenthesize_if_binary(&left_str, left);
                    format!("(not {}) or {}", left_for_not, right_str)
                }
                BinaryOp::Iff => {
                    // `a <=> b` = `(a and b) or (not a and not b)`
                    let left_for_and = maybe_parenthesize(&left_str, left, BinaryOp::And);
                    let right_for_and = maybe_parenthesize(&right_str, right, BinaryOp::And);
                    let left_for_not = parenthesize_if_binary(&left_str, left);
                    let right_for_not = parenthesize_if_binary(&right_str, right);
                    format!(
                        "({} and {}) or (not {} and not {})",
                        left_for_and, right_for_and, left_for_not, right_for_not
                    )
                }
            }
        }
    })
}

/// Wrap expression in parentheses if it's a binary operation.
/// Used when the expression will appear after `not` in an expanded operator.
fn parenthesize_if_binary(expr_str: &str, expr: &FnUpdate) -> String {
    if matches!(expr, FnUpdate::Binary(_, _, _)) {
        format!("({})", expr_str)
    } else {
        expr_str.to_string()
    }
}

/// Add parentheses around the expression string if needed based on operator precedence.
/// BooleanNet precedence: not > and > or
fn maybe_parenthesize(expr_str: &str, expr: &FnUpdate, parent_op: BinaryOp) -> String {
    if let FnUpdate::Binary(child_op, _, _) = expr {
        // Need parentheses if a child has lower precedence than a parent
        let needs_parens = match (parent_op, child_op) {
            // And has higher precedence than Or, so Or needs parentheses inside And
            (BinaryOp::And, BinaryOp::Or) => true,
            // Xor, Imp, Iff are expanded, so we need to handle them carefully
            (BinaryOp::And, BinaryOp::Xor)
            | (BinaryOp::And, BinaryOp::Imp)
            | (BinaryOp::And, BinaryOp::Iff) => true,
            _ => false,
        };
        if needs_parens {
            return format!("({})", expr_str);
        }
    }
    expr_str.to_string()
}

/// Restore a sanitized variable name to its original BooleanNet form.
///
/// If `original_names` is provided and contains the name, use the mapped value.
/// Otherwise, heuristically reverse the sanitization.
fn restore_name(sanitized: &str, original_names: Option<&HashMap<String, String>>) -> String {
    if let Some(mapping) = original_names
        && let Some(original) = mapping.get(sanitized)
    {
        return original.clone();
    }

    // Heuristic restoration
    sanitized
        .replace(PLUS_ESCAPE, "+")
        .replace(MINUS_ESCAPE, "-")
}

#[cfg(test)]
mod tests {
    use crate::BooleanNetwork;

    #[test]
    fn test_to_booleannet_simple() {
        let (network, mapping) = BooleanNetwork::try_from_booleannet(
            r#"
A* = B and C
B* = not A
C* = A or B
"#,
        )
        .unwrap();

        let output = network.to_booleannet(Some(&mapping)).unwrap();
        assert!(output.contains("A* ="));
        assert!(output.contains("B* ="));
        assert!(output.contains("C* ="));
        assert!(output.contains("and"));
        assert!(output.contains("or"));
        assert!(output.contains("not"));
    }

    #[test]
    fn test_to_booleannet_constants() {
        let (network, mapping) = BooleanNetwork::try_from_booleannet(
            r#"
A* = True
B* = False
"#,
        )
        .unwrap();

        let output = network.to_booleannet(Some(&mapping)).unwrap();
        assert!(output.contains("True"));
        assert!(output.contains("False"));
    }

    #[test]
    fn test_to_booleannet_special_chars() {
        let (network, mapping) = BooleanNetwork::try_from_booleannet(
            r#"
Ca2+c* = H+ATPase
H+ATPase* = not IL-2
IL-2* = Ca2+c and H+ATPase
"#,
        )
        .unwrap();

        let output = network.to_booleannet(Some(&mapping)).unwrap();
        assert!(output.contains("Ca2+c"));
        assert!(output.contains("H+ATPase"));
        assert!(output.contains("IL-2"));
    }

    #[test]
    fn test_to_booleannet_round_trip() {
        let original = r#"A* = B and C
B* = not A
C* = A or B
"#;
        let (network, mapping) = BooleanNetwork::try_from_booleannet(original).unwrap();
        let output = network.to_booleannet(Some(&mapping)).unwrap();

        // Parse the output again
        let (network2, _) = BooleanNetwork::try_from_booleannet(&output).unwrap();

        // Check that we have the same variables and regulators
        assert_eq!(network.num_vars(), network2.num_vars());
        for v1 in network.variables() {
            let name = network.get_variable_name(v1);
            let v2 = network2.as_graph().find_variable(name).unwrap();
            assert_eq!(
                network.as_graph().regulators(v1).len(),
                network2.as_graph().regulators(v2).len()
            );
        }
    }

    #[test]
    fn test_to_booleannet_heuristic_restoration() {
        // Test that heuristic restoration works without the mapping
        let (network, _) = BooleanNetwork::try_from_booleannet(
            r#"
Ca2+c* = H+ATPase
H+ATPase* = Ca2+c
"#,
        )
        .unwrap();

        // Use None for mapping - should use heuristic restoration
        let output = network.to_booleannet(None).unwrap();
        assert!(output.contains("Ca2+c"));
        assert!(output.contains("H+ATPase"));
    }

    #[test]
    fn test_reject_parametrised_network() {
        use std::convert::TryFrom;

        // Network with explicit parameter
        let network = BooleanNetwork::try_from(
            r#"
A -> B
$B: f(A)
"#,
        )
        .unwrap();

        let result = network.to_booleannet(None);
        assert!(result.is_err());
    }

    #[test]
    fn test_reject_implicit_parameter() {
        use std::convert::TryFrom;

        // Network with a missing update function
        let network = BooleanNetwork::try_from(
            r#"
A -> B
B -> A
$A: B
"#,
        )
        .unwrap();

        let result = network.to_booleannet(None);
        assert!(result.is_err());
        assert!(result.unwrap_err().contains("no update function"));
    }

    #[test]
    fn test_round_trip_with_special_chars() {
        let original = r#"Ca2+c* = H+ATPase and not IL-2
H+ATPase* = Ca2+c or IL-2
IL-2* = not Ca2+c
"#;
        let (network, mapping) = BooleanNetwork::try_from_booleannet(original).unwrap();
        let output = network.to_booleannet(Some(&mapping)).unwrap();

        // Parse again
        let (network2, mapping2) = BooleanNetwork::try_from_booleannet(&output).unwrap();

        // Verify the structure is preserved
        assert_eq!(network.num_vars(), network2.num_vars());

        // Export again and compare
        let output2 = network2.to_booleannet(Some(&mapping2)).unwrap();

        // The outputs should be functionally equivalent
        let (network3, _) = BooleanNetwork::try_from_booleannet(&output2).unwrap();
        assert_eq!(network2.num_vars(), network3.num_vars());
    }

    #[test]
    fn test_complex_expression() {
        let (network, mapping) = BooleanNetwork::try_from_booleannet(
            r#"
A* = (B or C) and not D
B* = not (A and C)
C* = A and B and D
D* = A or B or C
"#,
        )
        .unwrap();

        let output = network.to_booleannet(Some(&mapping)).unwrap();

        // Should round-trip successfully
        let (network2, _) = BooleanNetwork::try_from_booleannet(&output).unwrap();
        assert_eq!(network.num_vars(), network2.num_vars());
    }

    #[test]
    fn test_formatting_with_operator_translation() {
        let bn = BooleanNetwork::try_from(
            r"
            A -> B
            B -> B
            $A: true
            $B: (A & B) => A
            ",
        )
        .unwrap();

        let booleannet_str = bn.to_booleannet(None).unwrap();
        // This is the expected *correct* translation for implication.
        // BooleanNet format uses `and` keyword, not `&`.
        // `(A & B) => A` expands to `not (A & B) or A` which in BooleanNet is:
        assert!(
            booleannet_str.contains("(not (A and B)) or A"),
            "Expected '(not (A and B)) or A' but got: {}",
            booleannet_str
        );
    }

    #[test]
    fn test_or_inside_xor_expansion() {
        // (A | B) ^ C should expand to ((A or B) and not C) or (not (A or B) and C)
        // The key is that (A or B) needs parentheses in the `and` context
        use std::convert::TryFrom;
        let bn = BooleanNetwork::try_from(
            r"
            A -> X
            B -> X
            C -> X
            $A: true
            $B: true
            $C: true
            $X: (A | B) ^ C
            ",
        )
        .unwrap();

        let booleannet_str = bn.to_booleannet(None).unwrap();
        // Should have "(A or B) and" somewhere (parenthesized Or in And context)
        assert!(
            booleannet_str.contains("((A or B) and not C) or (not (A or B) and C)"),
            "XOR with Or operand not correctly parenthesized: {}",
            booleannet_str
        );
    }

    #[test]
    fn test_or_inside_iff_expansion() {
        // (A | B) <=> C should expand to ((A or B) and C) or (not (A or B) and not C)
        // The key is that (A or B) needs parentheses in the `and` context
        use std::convert::TryFrom;
        let bn = BooleanNetwork::try_from(
            r"
            A -> X
            B -> X
            C -> X
            $A: true
            $B: true
            $C: true
            $X: (A | B) <=> C
            ",
        )
        .unwrap();

        let booleannet_str = bn.to_booleannet(None).unwrap();
        // Should have proper parentheses around (A or B) in and context
        assert!(
            booleannet_str.contains("((A or B) and C) or (not (A or B) and not C)"),
            "IFF with Or operand not correctly parenthesized: {}",
            booleannet_str
        );
    }

    #[test]
    fn test_imp_inside_iff_expansion() {
        // (A => B) <=> C - the Imp expands to "(not A) or B" which then appears in and context
        use std::convert::TryFrom;
        let bn = BooleanNetwork::try_from(
            r"
            A -> X
            B -> X
            C -> X
            $A: true
            $B: true
            $C: true
            $X: (A => B) <=> C
            ",
        )
        .unwrap();

        let booleannet_str = bn.to_booleannet(None).unwrap();
        // The Imp expansion "(not A) or B" needs parentheses when used in and context
        // Full expansion: (((not A) or B) and C) or (not ((not A) or B) and not C)
        assert!(
            booleannet_str.contains("(((not A) or B) and C) or (not ((not A) or B) and not C)"),
            "IFF with Imp operand not correctly parenthesized: {}",
            booleannet_str
        );
    }

    #[test]
    fn test_or_on_right_side_of_xor() {
        // A ^ (B | C) - Or on the right side of Xor
        use std::convert::TryFrom;
        let bn = BooleanNetwork::try_from(
            r"
            A -> X
            B -> X
            C -> X
            $A: true
            $B: true
            $C: true
            $X: A ^ (B | C)
            ",
        )
        .unwrap();

        let booleannet_str = bn.to_booleannet(None).unwrap();
        // Should have proper parentheses: (A and not (B or C)) or (not A and (B or C))
        assert!(
            booleannet_str.contains("(A and not (B or C)) or (not A and (B or C))"),
            "XOR with Or on right not correctly parenthesized: {}",
            booleannet_str
        );
    }

    #[test]
    fn test_xor_inside_xor() {
        // (A ^ B) ^ C - nested XOR
        use std::convert::TryFrom;
        let bn = BooleanNetwork::try_from(
            r"
            A -> X
            B -> X
            C -> X
            $A: true
            $B: true
            $C: true
            $X: (A ^ B) ^ C
            ",
        )
        .unwrap();

        let booleannet_str = bn.to_booleannet(None).unwrap();
        // Inner XOR expands to "(A and not B) or (not A and B)"
        // Outer XOR uses this in and context, so it needs parentheses
        // Result should have something like `(((A and not B) or (not A and B)) and not C)`
        assert!(
            booleannet_str.contains("(((A and not B) or (not A and B)) and not C) or (not ((A and not B) or (not A and B)) and C)"),
            "Nested XOR not correctly parenthesized: {}",
            booleannet_str
        );
    }

    #[test]
    fn test_imp_inside_xor() {
        // (A => B) ^ C - Imp inside Xor
        use std::convert::TryFrom;
        let bn = BooleanNetwork::try_from(
            r"
            A -> X
            B -> X
            C -> X
            $A: true
            $B: true
            $C: true
            $X: (A => B) ^ C
            ",
        )
        .unwrap();

        let booleannet_str = bn.to_booleannet(None).unwrap();
        // Imp expands to "(not A) or B", which appears in and context in Xor expansion
        // Result: `((((not A) or B) and not C) or (not ((not A) or B) and C))`
        assert!(
            booleannet_str.contains("(((not A) or B) and not C) or (not ((not A) or B) and C)"),
            "Imp inside Xor not correctly parenthesized: {}",
            booleannet_str
        );
    }

    #[test]
    fn test_xor_inside_imp() {
        // (A ^ B) => C - Xor inside Imp (after not)
        use std::convert::TryFrom;
        let bn = BooleanNetwork::try_from(
            r"
            A -> X
            B -> X
            C -> X
            $A: true
            $B: true
            $C: true
            $X: (A ^ B) => C
            ",
        )
        .unwrap();

        let booleannet_str = bn.to_booleannet(None).unwrap();
        // Xor expands to "(A and not B) or (not A and B)"
        // This appears after not in Imp expansion: not ((A and not B) or (not A and B)) or C
        assert!(
            booleannet_str.contains("(not ((A and not B) or (not A and B))) or C"),
            "Xor inside Imp not correctly parenthesized: {}",
            booleannet_str
        );
    }

    #[test]
    fn test_or_inside_imp_left() {
        // (A | B) => C - Or on the left side of Imp (appears after not)
        use std::convert::TryFrom;
        let bn = BooleanNetwork::try_from(
            r"
            A -> X
            B -> X
            C -> X
            $A: true
            $B: true
            $C: true
            $X: (A | B) => C
            ",
        )
        .unwrap();

        let booleannet_str = bn.to_booleannet(None).unwrap();
        // (A | B) => C expands to (not (A or B)) or C
        assert!(
            booleannet_str.contains("(not (A or B)) or C"),
            "Or on left of Imp not correctly parenthesized: {}",
            booleannet_str
        );
    }

    #[test]
    fn test_or_inside_imp_right() {
        // A => (B | C) - Or on the right side of Imp
        use std::convert::TryFrom;
        let bn = BooleanNetwork::try_from(
            r"
            A -> X
            B -> X
            C -> X
            $A: true
            $B: true
            $C: true
            $X: A => (B | C)
            ",
        )
        .unwrap();

        let booleannet_str = bn.to_booleannet(None).unwrap();
        // A => (B | C) expands to (not A) or B or C (or is associative)
        assert!(
            booleannet_str.contains("(not A) or B or C"),
            "Or on right of Imp not correctly handled: {}",
            booleannet_str
        );
    }

    #[test]
    fn test_nested_imp_left() {
        // (A => B) => C - nested implication on the left
        use std::convert::TryFrom;
        let bn = BooleanNetwork::try_from(
            r"
            A -> X
            B -> X
            C -> X
            $A: true
            $B: true
            $C: true
            $X: (A => B) => C
            ",
        )
        .unwrap();

        let booleannet_str = bn.to_booleannet(None).unwrap();
        // Inner: A => B = (not A) or B
        // Outer: `((not A) or B) => C = (not ((not A) or B)) or C`
        assert!(
            booleannet_str.contains("(not ((not A) or B)) or C"),
            "Nested Imp on left not correctly parenthesized: {}",
            booleannet_str
        );
    }

    #[test]
    fn test_nested_imp_right() {
        // A => (B => C) - nested implication on the right
        use std::convert::TryFrom;
        let bn = BooleanNetwork::try_from(
            r"
            A -> X
            B -> X
            C -> X
            $A: true
            $B: true
            $C: true
            $X: A => (B => C)
            ",
        )
        .unwrap();

        let booleannet_str = bn.to_booleannet(None).unwrap();
        // Inner: B => C = (not B) or C
        // Outer: A => ((not B) or C) = (not A) or (not B) or C (or is associative)
        assert!(
            booleannet_str.contains("(not A) or (not B) or C"),
            "Nested Imp on right not correctly handled: {}",
            booleannet_str
        );
    }
}
