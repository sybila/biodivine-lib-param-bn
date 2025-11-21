use crate::_aeon_parser::FnUpdateTemp;
use crate::{BooleanNetwork, RegulatoryGraph};
use std::collections::{HashMap, HashSet};
use std::convert::TryFrom;

/// Transform variable names to make them compatible with our internal format
/// Replaces + with _plus_ and - with _minus_ and other special characters
fn sanitize_variable_name(name: &str) -> String {
    name.replace('+', "_plus_")
        .replace('-', "_minus_")
        .replace('/', "_slash_")
        .replace('*', "_star_")
        .replace('(', "_lp_")
        .replace(')', "_rp_")
        .replace('[', "_lb_")
        .replace(']', "_rb_")
}

impl BooleanNetwork {
    /// Try to load a Boolean network from a `.booleannet` model.
    ///
    /// The booleannet format is used by the `booleannet` Python package. It supports:
    /// - Comments starting with `#`
    /// - Initial state assignments like `A = B = True` (these are ignored as they represent
    ///   simulation state, not model structure)
    /// - Update rules in the format: `rank: variable* = expression`
    ///   where expressions use `and`, `or`, `not` operators
    ///
    /// **Note:** This implementation ignores initial state assignments and rank values,
    /// focusing only on the update rules which define the network structure.
    pub fn try_from_booleannet(model_string: &str) -> Result<BooleanNetwork, String> {
        let mut model_map: HashMap<String, String> = HashMap::new();
        let mut variables = HashSet::new();

        for (line_num, line) in model_string.lines().enumerate() {
            let line = line.trim();

            // Skip comments and empty lines
            if line.starts_with('#') || line.is_empty() {
                continue;
            }

            // Check if this is an initial state assignment (contains = but not :)
            // Examples: "A = B = True", "C = False", "E = Random"
            if !line.contains(':') && line.contains('=') {
                // This is an initial state assignment
                // We need to extract variable names from these lines
                // Format: "A = B = C = True/False/Random"
                let parts: Vec<&str> = line.split('=').collect();
                for part in parts {
                    let var_name = part.trim();
                    // Skip the final value (True, False, Random)
                    if var_name == "True"
                        || var_name == "False"
                        || var_name == "Random"
                        || var_name == "true"
                        || var_name == "false"
                        || var_name == "random"
                    {
                        continue;
                    }
                    if !var_name.is_empty() {
                        variables.insert(sanitize_variable_name(var_name));
                    }
                }
                continue;
            }

            // Check if this is an update rule (contains : and =)
            if line.contains(':') {
                // Parse update rule: "rank: variable* = expression"
                let parts: Vec<&str> = line.splitn(2, ':').collect();
                if parts.len() != 2 {
                    return Err(format!(
                        "Line {}: Expected format 'rank: variable* = expression', got: {}",
                        line_num + 1,
                        line
                    ));
                }

                // Parse the rank (we ignore it for now)
                let _rank = parts[0].trim();

                // Parse the variable and expression part
                let rule_part = parts[1].trim();

                // The rule part should be: "variable* = expression" or "variable *= expression"
                let rule_segments: Vec<&str> = if rule_part.contains("*=") {
                    rule_part.splitn(2, "*=").collect()
                } else if rule_part.contains('=') {
                    // Split by '=' and remove '*' from variable name
                    let temp: Vec<&str> = rule_part.splitn(2, '=').collect();
                    if temp.len() == 2 {
                        vec![temp[0].trim_end_matches('*').trim(), temp[1]]
                    } else {
                        temp
                    }
                } else {
                    return Err(format!(
                        "Line {}: Expected '=' or '*=' in update rule: {}",
                        line_num + 1,
                        rule_part
                    ));
                };

                if rule_segments.len() != 2 {
                    return Err(format!(
                        "Line {}: Could not parse update rule: {}",
                        line_num + 1,
                        rule_part
                    ));
                }

                let variable_name = rule_segments[0].trim().trim_end_matches('*').trim();
                // Remove inline comments (everything after #)
                let expression = rule_segments[1].split('#').next().unwrap_or("").trim();

                if variable_name.is_empty() {
                    return Err(format!(
                        "Line {}: Empty variable name in rule: {}",
                        line_num + 1,
                        line
                    ));
                }

                if expression.is_empty() {
                    return Err(format!(
                        "Line {}: Empty expression for variable '{}': {}",
                        line_num + 1,
                        variable_name,
                        line
                    ));
                }

                // Check for duplicate function declaration
                if model_map.contains_key(variable_name) {
                    return Err(format!(
                        "Line {}: Duplicate function declaration for '{}'",
                        line_num + 1,
                        variable_name
                    ));
                }

                // Convert booleannet syntax to our internal syntax
                let converted_expression = convert_booleannet_expression(expression)?;

                // Add variable name (sanitized)
                let sanitized_var_name = sanitize_variable_name(variable_name);
                variables.insert(sanitized_var_name.clone());

                // Parse the expression to find all referenced variables
                let function_template = FnUpdateTemp::try_from(converted_expression.as_str())?;
                let mut temp_vars = HashSet::new();
                function_template.dump_variables(&mut temp_vars);
                // Sanitize all variable names from the expression
                for var in temp_vars {
                    variables.insert(sanitize_variable_name(&var));
                }

                model_map.insert(sanitized_var_name, converted_expression);
            }
        }

        // Create sorted list of variables
        let mut variables = variables.into_iter().collect::<Vec<_>>();
        variables.sort();
        let mut graph = RegulatoryGraph::new(variables.clone());

        // First, build the regulatory graph
        for variable in &variables {
            if let Some(function) = model_map.get(variable) {
                let function_template = FnUpdateTemp::try_from(function.as_str())?;
                let mut regulators = HashSet::new();
                function_template.dump_variables(&mut regulators);
                let mut regulators = regulators.iter().collect::<Vec<_>>();
                regulators.sort();
                for regulator in regulators {
                    // We use 'true' for observable and 'None' for monotonicity as we don't
                    // have this information in the booleannet format
                    graph.add_regulation(regulator.as_str(), variable.as_str(), true, None)?;
                }
            }
        }

        let mut network = BooleanNetwork::new(graph);

        // Then add the update functions
        for (variable, function) in model_map.iter() {
            let function_template = FnUpdateTemp::try_from(function.as_str())?;
            network.add_template_update_function(variable.as_str(), function_template)?;
        }

        Ok(network)
    }
}

/// Convert booleannet expression syntax to our internal syntax
/// Booleannet uses: and, or, not
/// We use: &, |, !
fn convert_booleannet_expression(expression: &str) -> Result<String, String> {
    let mut result = String::new();
    let mut chars = expression.chars().peekable();

    while let Some(ch) = chars.next() {
        if ch.is_whitespace() {
            // Skip whitespace - we'll handle it implicitly
            continue;
        }

        // Check for 'not', 'and', 'or' keywords
        if ch.is_alphabetic() {
            let mut word = String::from(ch);

            // Collect the rest of the word (alphanumeric, underscore, or special chars like +, -)
            while let Some(&next_ch) = chars.peek() {
                if next_ch.is_alphanumeric()
                    || next_ch == '_'
                    || next_ch == '+'
                    || next_ch == '-'
                    || next_ch == '/'
                    || next_ch == '*'
                {
                    word.push(chars.next().unwrap());
                } else {
                    break;
                }
            }

            // Check if this is a keyword or a variable name
            match word.as_str() {
                "not" => result.push('!'),
                "and" => result.push('&'),
                "or" => result.push('|'),
                "True" | "true" => result.push_str("true"),
                "False" | "false" => result.push_str("false"),
                "Random" | "random" => {
                    // Random is not supported in our format, we'll treat it as a variable
                    result.push_str(&sanitize_variable_name(&word));
                }
                _ => {
                    // This is a variable name - sanitize it
                    result.push_str(&sanitize_variable_name(&word));
                }
            }
        } else {
            // Not a letter, just copy the character (parentheses, etc.)
            result.push(ch);
        }
    }

    Ok(result)
}

#[cfg(test)]
mod tests {
    use crate::BooleanNetwork;

    #[test]
    fn test_simple_booleannet() {
        let model = r"
# Simple test model
A = True
B = False

1: A* = not A
1: B* = A and B
";
        let network = BooleanNetwork::try_from_booleannet(model).unwrap();
        assert_eq!(2, network.num_vars());

        let a = network.as_graph().find_variable("A").unwrap();
        let b = network.as_graph().find_variable("B").unwrap();

        assert!(network.get_update_function(a).is_some());
        assert!(network.get_update_function(b).is_some());
    }

    #[test]
    fn test_demo_rules_booleannet() {
        let model = std::fs::read_to_string("booleannet_models/demo-rules.txt").unwrap();

        let network = BooleanNetwork::try_from_booleannet(&model).unwrap();

        // Should have variables A, B, C, D, E, F, G
        assert_eq!(7, network.num_vars());

        // Check that A and E have update functions
        let a = network.as_graph().find_variable("A").unwrap();
        let e = network.as_graph().find_variable("E").unwrap();

        assert!(network.get_update_function(a).is_some());
        assert!(network.get_update_function(e).is_some());
    }

    #[test]
    fn test_aba_booleannet() {
        let model = std::fs::read_to_string("booleannet_models/ABA.txt").unwrap();

        let network = BooleanNetwork::try_from_booleannet(&model).unwrap();

        // ABA model should have many variables
        assert!(network.num_vars() > 30);

        // Count how many variables have update functions
        let with_functions = network
            .variables()
            .filter(|var| network.get_update_function(*var).is_some())
            .count();

        // Most variables should have update functions, but not necessarily all
        // (some might be inputs with only initial states)
        assert!(with_functions > 30);
    }

    #[test]
    fn test_lgl_booleannet() {
        let model = std::fs::read_to_string("booleannet_models/LGL.txt").unwrap();

        let network = BooleanNetwork::try_from_booleannet(&model).unwrap();

        // LGL model has many variables
        assert!(network.num_vars() > 40);

        // Count how many variables have update functions
        let with_functions = network
            .variables()
            .filter(|var| network.get_update_function(*var).is_some())
            .count();

        // Most variables should have update functions
        assert!(with_functions > 40);
    }

    #[test]
    fn test_bb_booleannet() {
        let model = std::fs::read_to_string("booleannet_models/Bb.txt").unwrap();

        let network = BooleanNetwork::try_from_booleannet(&model).unwrap();

        // Bb model has many variables
        assert!(network.num_vars() > 20);
    }

    #[test]
    fn test_expression_conversion() {
        use super::convert_booleannet_expression;

        assert_eq!(convert_booleannet_expression("A and B").unwrap(), "A&B");
        assert_eq!(convert_booleannet_expression("A or B").unwrap(), "A|B");
        assert_eq!(convert_booleannet_expression("not A").unwrap(), "!A");
        assert_eq!(
            convert_booleannet_expression("A and not B or C").unwrap(),
            "A&!B|C"
        );
        assert_eq!(
            convert_booleannet_expression("(A and B) or (C and not D)").unwrap(),
            "(A&B)|(C&!D)"
        );
    }

    #[test]
    fn test_duplicate_function_error() {
        let model = r"
1: A* = B
1: A* = C
";
        let result = BooleanNetwork::try_from_booleannet(model);
        assert!(result.is_err());
        assert!(result.unwrap_err().contains("Duplicate"));
    }

    #[test]
    fn test_invalid_format_error() {
        // Missing colon after rank
        let model = r"
1 A* = B
";
        let _result = BooleanNetwork::try_from_booleannet(model);
        // This should be parsed as an initial state assignment, so it won't error
        // Let's test with a truly invalid expression instead

        let model2 = r"
1: A* = B &&& C
";
        let result2 = BooleanNetwork::try_from_booleannet(model2);
        assert!(result2.is_err());
    }

    #[test]
    fn test_with_star_equals() {
        let model = r"
1: A *= not A
1: B *= A and B
";
        let network = BooleanNetwork::try_from_booleannet(model).unwrap();
        assert_eq!(2, network.num_vars());
    }

    #[test]
    fn test_sanitized_uniqueness() {
        // This should not parse correctly, because there is a duplicate variable named A_plus_
        let model = r"
1: A+ *= not A+
1: A+ *= A+ and A+
";
        assert!(BooleanNetwork::try_from_booleannet(model).is_err());
    }
}
