use crate::_aeon_parser::FnUpdateTemp;
use crate::{BooleanNetwork, RegulatoryGraph};
use regex::Regex;
use std::collections::{HashMap, HashSet};
use std::convert::TryFrom;

impl BooleanNetwork {
    /// Try to load a Boolean network from a `booleannet` model.
    ///
    /// The format typically consists of lines like:
    /// `Rank: Target* = Expression`
    /// And initialization lines like:
    /// `Target = True`
    ///
    /// We ignore initialization lines for the structure of the network, but we use them to identify variables.
    pub fn try_from_booleannet(model_string: &str) -> Result<BooleanNetwork, String> {
        let mut model_map: HashMap<String, String> = HashMap::new();
        let mut variables: HashSet<String> = HashSet::new();

        // Regex for replacing operators.
        // We need to compile them once ideally, but for now inside function is fine or use lazy_static if overhead is high.
        // Given this is IO, overhead is negligible.
        let re_and = Regex::new(r"\band\b").unwrap();
        let re_or = Regex::new(r"\bor\b").unwrap();
        let re_not = Regex::new(r"\bnot\b").unwrap();

        for line in model_string.lines() {
            let line = line.trim();
            if line.is_empty() || line.starts_with('#') {
                continue;
            }

            // Check for update rule
            if let Some((_rank, rest)) = line.split_once(':')
                && let Some((target_part, expression_part)) = rest.split_once('=')
            {
                let target_part = target_part.trim();
                if let Some(stripped) = target_part.strip_suffix('*') {
                    let var_name = stripped.trim().to_string();
                    let expression = expression_part.trim();

                    if expression.eq_ignore_ascii_case("random") {
                        // If update is random, we treat it as an input (no update function).
                        variables.insert(var_name);
                        continue;
                    }

                    // Sanitize expression
                    let expression = re_and.replace_all(expression, "&");
                    let expression = re_or.replace_all(&expression, "|");
                    let expression = re_not.replace_all(&expression, "!");

                    if model_map.contains_key(&var_name) {
                        return Err(format!("Duplicate function for {}", var_name));
                    }
                    model_map.insert(var_name.clone(), expression.to_string());
                    variables.insert(var_name);
                    continue;
                }
            }

            // If not update rule, check for initialization to find more variables
            // e.g., A = B = True
            // We assume initialization lines do not contain ':' (which is used for rank in update rules)
            if line.contains('=') && !line.contains(':') {
                let parts: Vec<&str> = line.split('=').map(|s| s.trim()).collect();
                // The last part is the value, previous parts are variables.
                if parts.len() >= 2 {
                    for part in &parts[..parts.len() - 1] {
                        if !part.is_empty() {
                            // We assume these are variables.
                            // However, check if they are valid names?
                            variables.insert(part.to_string());
                        }
                    }
                }
            }
        }

        // Check for variables appearing in expressions that were not declared
        for expression in model_map.values() {
            if let Ok(function_template) = FnUpdateTemp::try_from(expression.as_str()) {
                function_template.dump_variables(&mut variables);
            } else {
                return Err(format!("Failed to parse expression: {}", expression));
            }
        }

        let mut variables = variables.into_iter().collect::<Vec<_>>();
        variables.sort();
        let mut graph = RegulatoryGraph::new(variables.clone());

        // Build graph
        for variable in &variables {
            if let Some(function) = model_map.get(variable) {
                let function_template = FnUpdateTemp::try_from(function.as_str())?;
                let mut regulators = HashSet::new();
                function_template.dump_variables(&mut regulators);
                let mut regulators = regulators.iter().collect::<Vec<_>>();
                regulators.sort();
                for regulator in regulators {
                    graph.add_regulation(regulator.as_str(), variable.as_str(), true, None)?;
                }
            }
        }

        let mut network = BooleanNetwork::new(graph);

        // Add functions
        for (variable, function) in model_map.iter() {
            let function_template = FnUpdateTemp::try_from(function.as_str())?;
            network.add_template_update_function(variable.as_str(), function_template)?;
        }

        Ok(network)
    }
}

#[cfg(test)]
mod tests {
    use crate::BooleanNetwork;

    #[test]
    fn test_booleannet_basic() {
        let model = r#"
        # Comments
        A = True
        1: B* = A or (not C)
        1: C* = B and A
        "#;
        let bn = BooleanNetwork::try_from_booleannet(model).unwrap();
        assert_eq!(bn.num_vars(), 3);
        assert!(bn.as_graph().find_variable("A").is_some());
        assert!(bn.as_graph().find_variable("B").is_some());
        assert!(bn.as_graph().find_variable("C").is_some());

        // A is input
        assert!(
            bn.get_update_function(bn.as_graph().find_variable("A").unwrap())
                .is_none()
        );
        // B and C have functions
        assert!(
            bn.get_update_function(bn.as_graph().find_variable("B").unwrap())
                .is_some()
        );
        assert!(
            bn.get_update_function(bn.as_graph().find_variable("C").unwrap())
                .is_some()
        );
    }

    #[test]
    fn test_booleannet_random() {
        let model = r#"
        G = Random
        1: E* = G
        "#;
        let bn = BooleanNetwork::try_from_booleannet(model).unwrap();
        assert_eq!(bn.num_vars(), 2);
        let g = bn.as_graph().find_variable("G").unwrap();
        assert!(bn.get_update_function(g).is_none());
    }
}
