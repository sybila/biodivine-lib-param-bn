use crate::_aeon_parser::{ExpressionSyntax, FnUpdateTemp};
use crate::{BooleanNetwork, RegulatoryGraph};
use std::collections::{HashMap, HashSet};

/// Placeholder for the `__plus__` escape sequence.
const PLUS_ESCAPE: &str = "__plus__";
/// Placeholder for the `__minus__` escape sequence.
const MINUS_ESCAPE: &str = "__minus__";

impl BooleanNetwork {
    /// Try to load a Boolean network from a BooleanNet model string.
    ///
    /// BooleanNet format uses keyword-based operators (`and`, `or`, `not`) and capitalized
    /// literals (`True`, `False`). Update rules are specified as `VAR* = expression` or
    /// `rank: VAR* = expression`.
    ///
    /// **Important notes:**
    /// - Initialization statements (e.g., `A = True`) are ignored as they relate to simulation,
    ///   not network structure.
    /// - Rank labels are ignored as they relate to simulation order.
    /// - The `Random` literal is not supported and will result in an error.
    /// - PLDE tuple syntax is not supported.
    ///
    /// **Variable name handling:**
    /// BooleanNet allows `+` and `-` in variable names (e.g., `Ca2+c`, `H+ATPase`, `IL-2`),
    /// but this library's internal representation does not. These characters are automatically
    /// replaced with `__plus__` and `__minus__` respectively. The returned `HashMap` maps
    /// the sanitized names to their original BooleanNet names, enabling round-trip fidelity
    /// when using [`BooleanNetwork::to_booleannet`].
    ///
    /// # Returns
    /// A tuple of `(BooleanNetwork, HashMap<String, String>)` where the map contains
    /// `sanitized_name -> original_name` for any names that were modified.
    pub fn try_from_booleannet(
        model_string: &str,
    ) -> Result<(BooleanNetwork, HashMap<String, String>), String> {
        // Store parsed and sanitized update functions
        let mut update_functions: HashMap<String, FnUpdateTemp> = HashMap::new();
        let mut variables = HashSet::new();
        let mut name_mapping: HashMap<String, String> = HashMap::new();

        // Closure to sanitize a name and update the mapping
        let sanitize = |name: &str, mapping: &mut HashMap<String, String>| -> String {
            if name.contains('+') || name.contains('-') {
                let sanitized = name.replace('+', PLUS_ESCAPE).replace('-', MINUS_ESCAPE);
                if sanitized != name {
                    mapping.insert(sanitized.clone(), name.to_string());
                }
                sanitized
            } else {
                name.to_string()
            }
        };

        for (line_num, line) in model_string.lines().enumerate() {
            let line = line.trim();

            // Skip comments and empty lines
            if line.is_empty() || line.starts_with('#') {
                continue;
            }

            // Check for update rules (contain *= or * =)
            if let Some(rule) = parse_update_rule(line)? {
                let (var_name, expression) = rule;

                // Check for unsupported features before parsing
                if expression.contains("Random") {
                    return Err(format!(
                        "Line {}: 'Random' literal is not supported.",
                        line_num + 1
                    ));
                }

                // Parse the expression using BooleanNet syntax (supports + and - in identifiers)
                let function_template =
                    FnUpdateTemp::try_from_str(&expression, ExpressionSyntax::BooleanNet)
                        .map_err(|e| format!("Line {}: {}", line_num + 1, e))?;

                // Now sanitize the variable name
                let sanitized_var = sanitize(&var_name, &mut name_mapping);

                if update_functions.contains_key(&sanitized_var) {
                    return Err(format!(
                        "Line {}: Duplicate update rule for variable '{}'.",
                        line_num + 1,
                        var_name
                    ));
                }

                // Sanitize variable names in the parsed expression
                let sanitized_function = function_template
                    .rename_variables(&mut |name| sanitize(name, &mut name_mapping));

                variables.insert(sanitized_var.clone());
                sanitized_function.dump_variables(&mut variables);

                update_functions.insert(sanitized_var, *sanitized_function);
            }
            // Skip initialization statements (lines with = but no *)
            // These are identified by having = but not *= or * =
        }

        if update_functions.is_empty() {
            return Err("No update rules found in BooleanNet model.".to_string());
        }

        // Sort variables for deterministic ordering
        let mut variables: Vec<String> = variables.into_iter().collect();
        variables.sort();

        // Add self-regulation rules for input variables (those referenced but without update rules)
        // In BooleanNet, these are typically initialized via `A = True` and stay constant,
        // which is equivalent to a self-regulation `A* = A`
        for var in &variables {
            if !update_functions.contains_key(var) {
                update_functions.insert(var.clone(), FnUpdateTemp::Var(var.clone()));
            }
        }

        // Build the regulatory graph
        let mut graph = RegulatoryGraph::new(variables.clone());

        for variable in &variables {
            if let Some(function) = update_functions.get(variable) {
                let mut regulators = HashSet::new();
                function.dump_variables(&mut regulators);
                let mut regulators: Vec<&String> = regulators.iter().collect();
                regulators.sort();
                for regulator in regulators {
                    graph.add_regulation(regulator.as_str(), variable.as_str(), true, None)?;
                }
            }
        }

        // Create the Boolean network
        let mut network = BooleanNetwork::new(graph);

        // Add update functions (already parsed and sanitized)
        for (variable, function_template) in update_functions {
            network.add_template_update_function(variable.as_str(), function_template)?;
        }

        Ok((network, name_mapping))
    }
}

/// Parse a line to check if it's an update rule and extract variable name and expression.
///
/// Returns `None` if the line is not an update rule (e.g., initialization statement).
/// Returns `Some((variable_name, expression))` if it is an update rule.
fn parse_update_rule(line: &str) -> Result<Option<(String, String)>, String> {
    // Update rules have one of these forms:
    // - VAR *= expression
    // - VAR* = expression
    // - rank: VAR *= expression
    // - rank: VAR* = expression

    let line = line.trim();

    // Skip if it doesn't look like an update rule
    if !line.contains('*') {
        return Ok(None);
    }

    // Check for rank prefix (digits followed by colon)
    let line = if let Some(idx) = line.find(':') {
        let prefix = &line[..idx];
        if prefix.trim().chars().all(|c| c.is_ascii_digit()) {
            line[idx + 1..].trim()
        } else {
            line
        }
    } else {
        line
    };

    // Now parse the update rule
    // Look for *= or * =
    if let Some(idx) = line.find("*=") {
        let var_name = line[..idx].trim().to_string();
        let expression = strip_inline_comment(&line[idx + 2..]);
        if var_name.is_empty() {
            return Err(format!("Empty variable name in update rule: {}", line));
        }
        Ok(Some((var_name, expression)))
    } else if let Some(idx) = line.find('*') {
        // Check for "* =" pattern
        let rest = line[idx + 1..].trim();
        if let Some(expression) = rest.strip_prefix('=') {
            let var_name = line[..idx].trim().to_string();
            let expression = strip_inline_comment(expression);
            if var_name.is_empty() {
                return Err(format!("Empty variable name in update rule: {}", line));
            }
            Ok(Some((var_name, expression)))
        } else {
            // Has * but not in update rule syntax - might be multiplication or something else
            // BooleanNet doesn't support multiplication, so this is likely an error
            Ok(None)
        }
    } else {
        Ok(None)
    }
}

/// Strip inline comments from an expression.
/// BooleanNet files can have comments at the end of lines like: `A and B #comment`
fn strip_inline_comment(expr: &str) -> String {
    // Find the first # that is not inside parentheses
    let mut paren_depth: i32 = 0;
    for (i, c) in expr.char_indices() {
        match c {
            '(' => paren_depth += 1,
            ')' => paren_depth = paren_depth.saturating_sub(1),
            '#' if paren_depth == 0 => {
                return expr[..i].trim().to_string();
            }
            _ => {}
        }
    }
    expr.trim().to_string()
}

#[cfg(test)]
mod tests {
    use crate::BooleanNetwork;
    use crate::symbolic_async_graph::SymbolicAsyncGraph;

    /// Helper function to verify that two networks are semantically equivalent.
    /// Uses BDDs to compare update functions (BDDs are canonical representations).
    fn assert_networks_semantically_equal(net1: &BooleanNetwork, net2: &BooleanNetwork) {
        assert_eq!(
            net1.num_vars(),
            net2.num_vars(),
            "Networks have different number of variables"
        );

        // Create symbolic graphs for both networks
        let stg1 = SymbolicAsyncGraph::new(net1).expect("Failed to create graph for net1");
        let stg2 = SymbolicAsyncGraph::new(net2).expect("Failed to create graph for net2");

        // Compare update functions for each variable
        for var1 in net1.variables() {
            let name = net1.get_variable_name(var1);
            let var2 = net2
                .as_graph()
                .find_variable(name)
                .expect(&format!("Variable {} not found in net2", name));

            let bdd1 = stg1.get_symbolic_fn_update(var1);
            let bdd2 = stg2.get_symbolic_fn_update(var2);

            assert_eq!(
                bdd1, bdd2,
                "Update functions for variable {} are not semantically equal",
                name
            );
        }
    }

    #[test]
    fn test_parse_simple_booleannet() {
        let model = r#"
# Simple test model
A = True
B = False

A* = not B
B* = A and B
"#;
        let (network, mapping) = BooleanNetwork::try_from_booleannet(model).unwrap();
        assert_eq!(network.num_vars(), 2);
        assert!(mapping.is_empty()); // No special characters in names
    }

    #[test]
    fn test_parse_booleannet_with_ranks() {
        let model = r#"
# Model with ranks (ranks should be ignored)
A = True
B = False

1: A* = not B
10: B* = A or B
"#;
        let (network, _) = BooleanNetwork::try_from_booleannet(model).unwrap();
        assert_eq!(network.num_vars(), 2);
    }

    #[test]
    fn test_parse_booleannet_alternative_syntax() {
        // Test *= vs * = syntax
        let model = r#"
A* = True
B *= False
C *  =   False
D*= False
E*=False
"#;
        let (network, _) = BooleanNetwork::try_from_booleannet(model).unwrap();
        assert_eq!(network.num_vars(), 5);
    }

    #[test]
    fn test_parse_booleannet_complex_expression() {
        let model = r#"
A = B = C = True

A* = (B or C) and not A
B* = A and (not B or C)
C* = not (A and B)
"#;
        let (network, _) = BooleanNetwork::try_from_booleannet(model).unwrap();
        assert_eq!(network.num_vars(), 3);

        // Check that all variables have update functions
        for v in network.variables() {
            assert!(network.get_update_function(v).is_some());
        }
    }

    #[test]
    fn test_parse_booleannet_special_chars_in_names() {
        let model = r#"
Ca2+c = True
H+ATPase = True
IL-2 = False

Ca2+c* = H+ATPase and not IL-2
H+ATPase* = Ca2+c
IL-2* = not Ca2+c or H+ATPase
"#;
        let (network, mapping) = BooleanNetwork::try_from_booleannet(model).unwrap();
        assert_eq!(network.num_vars(), 3);

        // Check that names were sanitized
        assert!(network.as_graph().find_variable("Ca2__plus__c").is_some());
        assert!(
            network
                .as_graph()
                .find_variable("H__plus__ATPase")
                .is_some()
        );
        assert!(network.as_graph().find_variable("IL__minus__2").is_some());

        // Check mapping
        assert_eq!(mapping.get("Ca2__plus__c"), Some(&"Ca2+c".to_string()));
        assert_eq!(
            mapping.get("H__plus__ATPase"),
            Some(&"H+ATPase".to_string())
        );
        assert_eq!(mapping.get("IL__minus__2"), Some(&"IL-2".to_string()));
    }

    #[test]
    fn test_parse_booleannet_self_regulation() {
        let model = r#"
A* = A or B
B* = not B
"#;
        let (network, _) = BooleanNetwork::try_from_booleannet(model).unwrap();
        assert_eq!(network.num_vars(), 2);

        let a = network.as_graph().find_variable("A").unwrap();
        let b = network.as_graph().find_variable("B").unwrap();

        // A regulates itself
        assert!(network.as_graph().find_regulation(a, a).is_some());
        // B regulates itself
        assert!(network.as_graph().find_regulation(b, b).is_some());
    }

    #[test]
    fn test_parse_booleannet_constants() {
        let model = r#"
A* = True
B* = False
"#;
        let (network, _) = BooleanNetwork::try_from_booleannet(model).unwrap();
        assert_eq!(network.num_vars(), 2);
    }

    #[test]
    fn test_reject_random_literal() {
        let model = r#"
A* = Random
"#;
        let result = BooleanNetwork::try_from_booleannet(model);
        assert!(result.is_err());
        assert!(result.unwrap_err().contains("Random"));
    }

    #[test]
    fn test_empty_model() {
        let model = r#"
# Just comments
# No update rules
"#;
        let result = BooleanNetwork::try_from_booleannet(model);
        assert!(result.is_err());
        assert!(result.unwrap_err().contains("No update rules"));
    }

    #[test]
    fn test_duplicate_update_rule() {
        let model = r#"
A* = True
A* = False
"#;
        let result = BooleanNetwork::try_from_booleannet(model);
        assert!(result.is_err());
        assert!(result.unwrap_err().contains("Duplicate"));
    }

    #[test]
    fn test_sanitized_uniqueness() {
        // This should not parse correctly because there is a duplicate variable named A_plus_
        let model = r"
1: A+ *= not A+
1: A+ *= A+ and A+
";
        assert!(BooleanNetwork::try_from_booleannet(model).is_err());
    }

    #[test]
    fn test_parse_aba_model() {
        // Parse the ABA (Abscisic Acid) signaling model from booleannet_models
        let model = std::fs::read_to_string("booleannet_models/ABA.booleannet.txt").unwrap();
        let (network, mapping) = BooleanNetwork::try_from_booleannet(&model).unwrap();

        // ABA model has many variables with special characters
        assert!(network.num_vars() > 20);

        // Check that some expected variables exist (sanitized names)
        // H+ATPase should become H__plus__ATPase
        assert!(
            network
                .as_graph()
                .find_variable("H__plus__ATPase")
                .is_some()
        );
        // Ca2+c should become Ca2__plus__c
        assert!(network.as_graph().find_variable("Ca2__plus__c").is_some());

        // Check that mapping contains these
        assert!(mapping.contains_key("H__plus__ATPase"));
        assert!(mapping.contains_key("Ca2__plus__c"));

        // All variables should have update functions
        for v in network.variables() {
            assert!(
                network.get_update_function(v).is_some(),
                "Variable {} should have an update function",
                network.get_variable_name(v)
            );
        }
    }

    #[test]
    fn test_parse_bb_model() {
        // Parse the Bb (B. bronchiseptica) model
        let model = std::fs::read_to_string("booleannet_models/Bb.booleannet.txt").unwrap();
        let (network, _) = BooleanNetwork::try_from_booleannet(&model).unwrap();

        // Bb model has many variables
        assert!(network.num_vars() > 20);

        // All variables should have update functions
        for v in network.variables() {
            assert!(
                network.get_update_function(v).is_some(),
                "Variable {} should have an update function",
                network.get_variable_name(v)
            );
        }
    }

    #[test]
    fn test_parse_lgl_model() {
        // Parse the LGL (T-cell large granular lymphocyte leukemia) model
        let model = std::fs::read_to_string("booleannet_models/LGL.booleannet.txt").unwrap();
        let (network, mapping) = BooleanNetwork::try_from_booleannet(&model).unwrap();

        // LGL model has many variables with special characters (like C-Myc)
        assert!(network.num_vars() > 30);

        // Check for variables with special characters
        // C-Myc should become C__minus__Myc
        assert!(network.as_graph().find_variable("C__minus__Myc").is_some());
        assert!(mapping.contains_key("C__minus__Myc"));

        // All variables should have update functions
        for v in network.variables() {
            assert!(
                network.get_update_function(v).is_some(),
                "Variable {} should have an update function",
                network.get_variable_name(v)
            );
        }
    }

    #[test]
    fn test_try_from_file() {
        // Test the try_from_file integration
        let network =
            BooleanNetwork::try_from_file("booleannet_models/ABA.booleannet.txt").unwrap();
        assert!(network.num_vars() > 20);
    }

    #[test]
    fn test_round_trip_aba_model() {
        // Test full round-trip: parse -> export -> parse
        let model = std::fs::read_to_string("booleannet_models/ABA.booleannet.txt").unwrap();
        let (network, mapping) = BooleanNetwork::try_from_booleannet(&model).unwrap();

        // Export to BooleanNet format
        let exported = network.to_booleannet(Some(&mapping)).unwrap();

        // Parse the exported model
        let (network2, mapping2) = BooleanNetwork::try_from_booleannet(&exported).unwrap();

        // Verify semantic equivalence using BDDs
        assert_networks_semantically_equal(&network, &network2);

        // Export again and parse again for a triple round-trip
        let exported2 = network2.to_booleannet(Some(&mapping2)).unwrap();
        let (network3, _) = BooleanNetwork::try_from_booleannet(&exported2).unwrap();

        // All three networks should be semantically equivalent
        assert_networks_semantically_equal(&network, &network3);
    }

    #[test]
    fn test_round_trip_bb_model() {
        // Test round-trip for a Bb model
        let model = std::fs::read_to_string("booleannet_models/Bb.booleannet.txt").unwrap();
        let (network, mapping) = BooleanNetwork::try_from_booleannet(&model).unwrap();

        let exported = network.to_booleannet(Some(&mapping)).unwrap();
        let (network2, _) = BooleanNetwork::try_from_booleannet(&exported).unwrap();

        assert_networks_semantically_equal(&network, &network2);
    }

    #[test]
    fn test_round_trip_lgl_model() {
        // Test round-trip for LGL model
        let model = std::fs::read_to_string("booleannet_models/LGL.booleannet.txt").unwrap();
        let (network, mapping) = BooleanNetwork::try_from_booleannet(&model).unwrap();

        let exported = network.to_booleannet(Some(&mapping)).unwrap();
        let (network2, _) = BooleanNetwork::try_from_booleannet(&exported).unwrap();

        assert_networks_semantically_equal(&network, &network2);
    }

    #[test]
    fn test_expression_parsing_correctness() {
        // Test that specific expressions are parsed correctly by comparing to AEON format
        let booleannet_model = r#"
A* = True
B* = False
C* = A and B
D* = A or B
E* = not A
F* = A and not B
G* = (A or B) and C
H* = not (A and B)
"#;
        let (bn_network, _) = BooleanNetwork::try_from_booleannet(booleannet_model).unwrap();

        // Create equivalent network in AEON format
        let aeon_model = r#"
A -?? C
B -?? C
A -?? D
B -?? D
A -?? E
A -?? F
B -?? F
A -?? G
B -?? G
C -?? G
A -?? H
B -?? H
$A: true
$B: false
$C: A & B
$D: A | B
$E: !A
$F: A & !B
$G: (A | B) & C
$H: !(A & B)
"#;
        let aeon_network = BooleanNetwork::try_from(aeon_model).unwrap();

        // Both networks should be semantically equivalent
        assert_networks_semantically_equal(&bn_network, &aeon_network);
    }

    #[test]
    fn test_complex_expression_parsing() {
        // Test more complex expressions with nested operators
        let booleannet_model = r#"
A* = True
B* = True
C* = True
X* = (A and B) or (not A and C)
Y* = not (A or B) and C
Z* = A and B and C
"#;
        let (bn_network, _) = BooleanNetwork::try_from_booleannet(booleannet_model).unwrap();

        let aeon_model = r#"
A -?? X
B -?? X
C -?? X
A -?? Y
B -?? Y
C -?? Y
A -?? Z
B -?? Z
C -?? Z
$A: true
$B: true
$C: true
$X: (A & B) | (!A & C)
$Y: !(A | B) & C
$Z: A & B & C
"#;
        let aeon_network = BooleanNetwork::try_from(aeon_model).unwrap();

        assert_networks_semantically_equal(&bn_network, &aeon_network);
    }
}
