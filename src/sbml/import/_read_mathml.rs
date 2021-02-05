use crate::sbml::import::MATHML;
use roxmltree::{ExpandedName, Node};
use std::option::Option::Some;

const APPLY_TAG: (&'static str, &'static str) = (MATHML, "apply");
const NUMBER_TAG: (&'static str, &'static str) = (MATHML, "cn");
const IDENTIFIER_TAG: (&'static str, &'static str) = (MATHML, "ci");
const SYMBOL_TAG: (&'static str, &'static str) = (MATHML, "csymbol");

pub enum MathML {
    Integer(i64),
    Identifier(String),
    Apply(String, Vec<MathML>),
    SymbolApply(String, Vec<MathML>),
}

pub fn read_mathml(math: Node) -> Result<MathML, String> {
    let child_count = math.children().filter(|c| c.is_element()).count();
    if child_count == 0 {
        return Err(format!("Tag <math> has no children."));
    }
    if child_count > 1 {
        return Err(format!("More than one child in a <math> tag."));
    }

    Ok(read_expression(math.first_element_child().unwrap())?)
}

fn read_expression(math: Node) -> Result<MathML, String> {
    if math.tag_name() == ExpandedName::from(IDENTIFIER_TAG) {
        let id = math
            .text()
            .map(|s| s.trim().to_string())
            .unwrap_or(String::new());
        if id.is_empty() {
            return Err(format!("Empty math identifier."));
        }
        return Ok(MathML::Identifier(id));
    }

    if math.tag_name() == ExpandedName::from(NUMBER_TAG) {
        let value = math
            .text()
            .map(|s| s.trim().to_string())
            .unwrap_or(String::new());
        let num_type = math.attribute((MATHML, "type"));
        if num_type.is_some() && num_type.unwrap() != "integer" {
            return Err(format!(
                "Non-integer numeric types ({}) are not supported.",
                num_type.unwrap()
            ));
        }
        return if let Ok(parsed) = value.parse::<i64>() {
            Ok(MathML::Integer(parsed))
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
                    .unwrap_or(String::new());
                if symbol.is_empty() {
                    Err(format!("Empty <csymbol> in MathML."))
                } else {
                    Ok(MathML::SymbolApply(symbol, args))
                }
            } else {
                Ok(MathML::Apply(op_tag.tag_name().name().to_string(), args))
            }
        } else {
            Err(format!("MathML <apply> with no child elements."))
        };
    }

    Err(format!(
        "Unexpected MathML tag `{}`.",
        math.tag_name().name()
    ))
}

/// Some utility methods for working with MathML trees.
impl MathML {
    /// Returns true if the function contains given identifier (function symbols do not count).
    pub fn contains_identifier(&self, id: &str) -> bool {
        match self {
            MathML::Integer(_) => false,
            MathML::Identifier(value) => value == id,
            MathML::SymbolApply(_, args) => args.iter().any(|a| a.contains_identifier(id)),
            MathML::Apply(_, args) => args.iter().any(|a| a.contains_identifier(id)),
        }
    }
}
