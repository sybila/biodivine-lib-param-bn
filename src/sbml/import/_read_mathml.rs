use crate::sbml::import::MATHML;
use roxmltree::{ExpandedName, Node};
use std::option::Option::Some;

const APPLY_TAG: (&str, &str) = (MATHML, "apply");
const NUMBER_TAG: (&str, &str) = (MATHML, "cn");
const IDENTIFIER_TAG: (&str, &str) = (MATHML, "ci");
const SYMBOL_TAG: (&str, &str) = (MATHML, "csymbol");

pub enum MathMl {
    Integer(i64),
    Identifier(String),
    Apply(String, Vec<MathMl>),
    SymbolApply(String, Vec<MathMl>),
}

pub fn read_mathml(math: Node) -> Result<MathMl, String> {
    let child_count = math.children().filter(|c| c.is_element()).count();
    if child_count == 0 {
        return Err("Tag <math> has no children.".to_string());
    }
    if child_count > 1 {
        return Err("More than one child in a <math> tag.".to_string());
    }

    read_expression(math.first_element_child().unwrap())
}

fn read_expression(math: Node) -> Result<MathMl, String> {
    if math.tag_name() == ExpandedName::from(IDENTIFIER_TAG) {
        let id = math
            .text()
            .map(|s| s.trim().to_string())
            .unwrap_or_default();
        if id.is_empty() {
            return Err("Empty math identifier.".to_string());
        }
        return Ok(MathMl::Identifier(id));
    }

    if math.tag_name() == ExpandedName::from(NUMBER_TAG) {
        let value = math
            .text()
            .map(|s| s.trim().to_string())
            .unwrap_or_default();
        let num_type = math.attribute((MATHML, "type"));
        if num_type.is_some() && num_type.unwrap() != "integer" {
            return Err(format!(
                "Non-integer numeric types ({}) are not supported.",
                num_type.unwrap()
            ));
        }
        return if let Ok(parsed) = value.parse::<i64>() {
            Ok(MathMl::Integer(parsed))
        } else {
            Err(format!("Invalid integer constant: `{}`.", value))
        };
    }
    if math.tag_name() == ExpandedName::from(APPLY_TAG) {
        let op_tag = math.first_element_child();
        return if let Some(op_tag) = op_tag {
            let mut args = Vec::new();
            let mut arg = op_tag.next_sibling_element();
            while let Some(inner) = arg {
                args.push(read_expression(inner)?);
                arg = inner.next_sibling_element();
            }
            if op_tag.tag_name() == ExpandedName::from(SYMBOL_TAG) {
                let symbol = op_tag
                    .text()
                    .map(|s| s.trim().to_string())
                    .unwrap_or_default();
                if symbol.is_empty() {
                    Err("Empty <csymbol> in MathML.".to_string())
                } else {
                    Ok(MathMl::SymbolApply(symbol, args))
                }
            } else {
                Ok(MathMl::Apply(op_tag.tag_name().name().to_string(), args))
            }
        } else {
            Err("MathML <apply> with no child elements.".to_string())
        };
    }

    Err(format!(
        "Unexpected MathML tag `{}`.",
        math.tag_name().name()
    ))
}

/// Some utility methods for working with MathML trees.
impl MathMl {
    /// Returns true if the function contains given identifier (function symbols do not count).
    pub fn contains_identifier(&self, id: &str) -> bool {
        match self {
            MathMl::Integer(_) => false,
            MathMl::Identifier(value) => value == id,
            MathMl::SymbolApply(_, args) => args.iter().any(|a| a.contains_identifier(id)),
            MathMl::Apply(_, args) => args.iter().any(|a| a.contains_identifier(id)),
        }
    }
}
