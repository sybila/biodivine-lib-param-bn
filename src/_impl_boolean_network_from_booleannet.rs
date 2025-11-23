use crate::_aeon_parser::FnUpdateTemp;
use crate::{BooleanNetwork, RegulatoryGraph, VariableId};
use std::collections::{HashMap, HashSet};
use std::convert::TryFrom;

impl BooleanNetwork {
    /// Try to load a Boolean network from a `booleannet` model.
    pub fn try_from_booleannet(model_string: &str) -> Result<BooleanNetwork, String> {
        let mut name_map = NameMap::new();
        let mut rules = Vec::new();
        let mut declared_targets = HashSet::new();

        for (index, raw_line) in model_string.lines().enumerate() {
            let line_number = index + 1;
            let line = strip_comment(raw_line);
            if line.is_empty() {
                continue;
            }

            if let Some(rule) = ParsedRule::parse(line, line_number, &mut name_map)? {
                if !declared_targets.insert(rule.original_target.clone()) {
                    return Err(format!(
                        "Duplicate function declaration for `{}` on line {}.",
                        rule.original_target, line_number
                    ));
                }
                rules.push(rule);
            } else if line.contains('=') {
                register_initialization(line, line_number, &mut name_map)?;
            } else {
                return Err(format!("Unexpected line {}: `{}`", line_number, line));
            }
        }

        if name_map.is_empty() {
            return Err("Booleannet model does not contain any variables.".to_string());
        }

        let sanitized_names = name_map.sanitized_names();
        let mut graph = RegulatoryGraph::new(sanitized_names);

        for rule in &rules {
            let mut regulators = HashSet::new();
            rule.template.dump_variables(&mut regulators);
            let mut regulators = regulators.into_iter().collect::<Vec<_>>();
            regulators.sort();
            for regulator in regulators {
                graph.add_regulation(
                    regulator.as_str(),
                    rule.sanitized_target.as_str(),
                    true,
                    None,
                )?;
            }
        }

        let mut network = BooleanNetwork::new(graph);
        for rule in rules {
            network.add_template_update_function(rule.sanitized_target.as_str(), rule.template)?;
        }

        name_map.rename_network(&mut network)?;

        Ok(network)
    }
}

struct ParsedRule {
    original_target: String,
    sanitized_target: String,
    template: FnUpdateTemp,
}

impl ParsedRule {
    fn parse(
        line: &str,
        line_number: usize,
        names: &mut NameMap,
    ) -> Result<Option<ParsedRule>, String> {
        if let Some((rank_part, rest)) = line.split_once(':') {
            Self::parse_ranked_line(rank_part, rest, line_number, names)
        } else if line.contains('*') && line.contains('=') {
            Self::parse_simple_line(line, line_number, names)
        } else {
            Ok(None)
        }
    }

    fn parse_ranked_line(
        rank_part: &str,
        rest: &str,
        line_number: usize,
        names: &mut NameMap,
    ) -> Result<Option<ParsedRule>, String> {
        let rank = rank_part.trim();
        if rank.is_empty() {
            return Err(format!(
                "Invalid rule on line {}: missing rank.",
                line_number
            ));
        }
        rank.parse::<u32>().map_err(|_| {
            format!(
                "Invalid rule on line {}: `{}` is not a valid rank.",
                line_number, rank
            )
        })?;
        Self::parse_target_and_expression(rest.trim(), line_number, names).map(Some)
    }

    fn parse_simple_line(
        line: &str,
        line_number: usize,
        names: &mut NameMap,
    ) -> Result<Option<ParsedRule>, String> {
        Self::parse_target_and_expression(line, line_number, names).map(Some)
    }

    fn parse_target_and_expression(
        body: &str,
        line_number: usize,
        names: &mut NameMap,
    ) -> Result<ParsedRule, String> {
        let star_index = body.find('*').ok_or_else(|| {
            format!(
                "Invalid rule on line {}: `{}` does not contain `*`.",
                line_number, body
            )
        })?;
        let target = body[..star_index].trim();
        if target.is_empty() {
            return Err(format!(
                "Invalid rule on line {}: missing target variable.",
                line_number
            ));
        }

        let remainder = body[star_index + 1..].trim_start();
        if !remainder.starts_with('=') {
            return Err(format!(
                "Invalid rule on line {}: missing `=` after `*`.",
                line_number
            ));
        }
        let expression = remainder[1..].trim();
        if expression.is_empty() {
            return Err(format!(
                "Invalid rule on line {}: missing right-hand side.",
                line_number
            ));
        }

        let sanitized_target = names.declare(target);
        let translated = translate_expression(expression, names).map_err(|e| {
            format!(
                "Invalid expression for `{}` on line {}: {}",
                target, line_number, e
            )
        })?;
        let template = FnUpdateTemp::try_from(translated.as_str()).map_err(|e| {
            format!(
                "Failed to parse expression for `{}` on line {}: {}",
                target, line_number, e
            )
        })?;

        Ok(ParsedRule {
            original_target: target.to_string(),
            sanitized_target,
            template,
        })
    }
}

struct NameMap {
    declared_order: Vec<String>,
    reference_order: Vec<String>,
    declared_set: HashSet<String>,
    reference_set: HashSet<String>,
    original_to_clean: HashMap<String, String>,
    clean_in_use: HashSet<String>,
}

impl NameMap {
    fn new() -> NameMap {
        NameMap {
            declared_order: Vec::new(),
            reference_order: Vec::new(),
            declared_set: HashSet::new(),
            reference_set: HashSet::new(),
            original_to_clean: HashMap::new(),
            clean_in_use: HashSet::new(),
        }
    }

    fn is_empty(&self) -> bool {
        self.declared_order.is_empty() && self.reference_order.is_empty()
    }

    fn declare(&mut self, original: &str) -> String {
        let clean = self.ensure_mapping(original);
        if self.declared_set.insert(original.to_string()) {
            self.declared_order.push(original.to_string());
        }
        clean
    }

    fn reference(&mut self, original: &str) -> String {
        let clean = self.ensure_mapping(original);
        if !self.declared_set.contains(original) && self.reference_set.insert(original.to_string())
        {
            self.reference_order.push(original.to_string());
        }
        clean
    }

    fn ensure_mapping(&mut self, original: &str) -> String {
        if let Some(existing) = self.original_to_clean.get(original) {
            return existing.clone();
        }

        let mut base = sanitize_name(original);
        if base.is_empty() {
            base.push('_');
        }
        if base
            .chars()
            .next()
            .map(|c| c.is_ascii_digit())
            .unwrap_or(false)
        {
            base = format!("_{}", base);
        }

        let mut candidate = base.clone();
        let mut suffix = 1;
        while self.clean_in_use.contains(&candidate) {
            suffix += 1;
            candidate = format!("{}_{}", base, suffix);
        }

        self.clean_in_use.insert(candidate.clone());
        self.original_to_clean
            .insert(original.to_string(), candidate.clone());
        candidate
    }

    fn ordered_names(&self) -> Vec<String> {
        let mut order = self.declared_order.clone();
        for name in &self.reference_order {
            if !self.declared_set.contains(name) {
                order.push(name.clone());
            }
        }
        order
    }

    fn sanitized_names(&self) -> Vec<String> {
        self.ordered_names()
            .iter()
            .map(|name| self.original_to_clean.get(name).unwrap().clone())
            .collect()
    }

    fn rename_network(&self, network: &mut BooleanNetwork) -> Result<(), String> {
        for (index, original) in self.ordered_names().iter().enumerate() {
            let id = VariableId(index);
            if network.get_variable_name(id) == original {
                continue;
            }
            network
                .as_graph_mut()
                .set_variable_name(id, original)
                .map_err(|e| format!("Failed to rename `{}`: {}", original, e))?;
        }
        Ok(())
    }
}

fn strip_comment(line: &str) -> &str {
    let without_comment = if let Some(index) = line.find('#') {
        &line[..index]
    } else {
        line
    };
    without_comment.trim()
}

fn register_initialization(
    line: &str,
    line_number: usize,
    names: &mut NameMap,
) -> Result<(), String> {
    let tokens: Vec<&str> = line
        .split('=')
        .map(|part| part.trim())
        .filter(|part| !part.is_empty())
        .collect();
    if tokens.len() < 2 {
        return Err(format!(
            "Invalid initialization on line {}: `{}`",
            line_number, line
        ));
    }

    let last_is_literal = is_literal(tokens.last().unwrap());
    let end = if last_is_literal {
        tokens.len() - 1
    } else {
        tokens.len()
    };
    if end == 0 {
        return Err(format!(
            "Invalid initialization on line {}: `{}`",
            line_number, line
        ));
    }

    for token in &tokens[..end] {
        names.declare(token);
    }

    Ok(())
}

fn is_literal(token: &str) -> bool {
    matches!(
        token.to_ascii_lowercase().as_str(),
        "true" | "false" | "random"
    )
}

fn translate_expression(expr: &str, names: &mut NameMap) -> Result<String, String> {
    let mut result = String::new();
    let mut needs_space = false;
    let mut chars = expr.chars().peekable();

    while let Some(ch) = chars.peek().cloned() {
        if ch.is_whitespace() {
            chars.next();
            continue;
        }
        if ch == '(' {
            if needs_space {
                result.push(' ');
            }
            result.push('(');
            chars.next();
            needs_space = false;
            continue;
        }
        if ch == ')' {
            result.push(')');
            chars.next();
            needs_space = true;
            continue;
        }

        let mut token = String::new();
        while let Some(&inner) = chars.peek() {
            if inner.is_whitespace() || inner == '(' || inner == ')' {
                break;
            }
            token.push(inner);
            chars.next();
        }
        if token.is_empty() {
            continue;
        }

        let lower = token.to_ascii_lowercase();
        match lower.as_str() {
            "and" => {
                result.push_str(" & ");
                needs_space = false;
            }
            "or" => {
                result.push_str(" | ");
                needs_space = false;
            }
            "not" => {
                if needs_space {
                    result.push(' ');
                }
                result.push('!');
                needs_space = false;
            }
            "true" => {
                if needs_space {
                    result.push(' ');
                }
                result.push_str("true");
                needs_space = true;
            }
            "false" => {
                if needs_space {
                    result.push(' ');
                }
                result.push_str("false");
                needs_space = true;
            }
            "random" => {
                return Err("`Random` is not supported inside update rules.".to_string());
            }
            _ => {
                let sanitized = names.reference(token.as_str());
                if needs_space {
                    result.push(' ');
                }
                result.push_str(sanitized.as_str());
                needs_space = true;
            }
        }
    }

    Ok(result)
}

fn sanitize_name(name: &str) -> String {
    name.chars()
        .map(|ch| {
            if ch.is_ascii_alphanumeric() || ch == '_' {
                ch
            } else {
                '_'
            }
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use crate::BooleanNetwork;

    #[test]
    fn read_booleannet_demo_model() {
        let model =
            std::fs::read_to_string("booleannet_models/demo-rules.txt").expect("demo model");
        let network = BooleanNetwork::try_from_booleannet(model.as_str()).unwrap();

        assert_eq!(7, network.num_vars());
        let graph = network.as_graph();
        let a = graph.find_variable("A").unwrap();
        let e = graph.find_variable("E").unwrap();
        let b = graph.find_variable("B").unwrap();

        assert!(network.get_update_function(a).is_some());
        assert!(network.get_update_function(e).is_some());
        assert!(network.get_update_function(b).is_none());
    }

    #[test]
    fn read_booleannet_aba_model() {
        let model = std::fs::read_to_string("booleannet_models/ABA.txt").expect("ABA model");
        let network = BooleanNetwork::try_from_booleannet(model.as_str()).unwrap();

        let graph = network.as_graph();
        let closure = graph.find_variable("Closure").unwrap();
        let calcium = graph.find_variable("Ca2+c").unwrap();
        let pump = graph.find_variable("H+ATPase").unwrap();

        assert!(network.get_update_function(closure).is_some());
        assert!(network.get_update_function(calcium).is_some());
        assert!(network.get_update_function(pump).is_some());
    }
}
