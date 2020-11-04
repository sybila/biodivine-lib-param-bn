use super::parser::FnUpdateTemp;
use super::parser::FnUpdateTemp::*;
use super::{BinaryOp, BooleanNetwork, Monotonicity, Parameter, RegulatoryGraph};
use std::collections::{HashMap, HashSet};
use xml::reader::XmlEvent;
use xml::EventReader;
use regex::Regex;

pub mod export;

impl BooleanNetwork {
    pub fn from_sbml(model_file: &str) -> Result<(BooleanNetwork, Layout), String> {
        let mut parser = EventReader::new(model_file.as_bytes());
        // First tag should be sbml - read it and verify that it has necessary properties, then read model
        while let Ok(event) = parser.next() {
            match event {
                XmlEvent::StartElement {
                    name, attributes, ..
                } => {
                    if name.local_name.as_str() == "sbml" {
                        for attr in attributes {
                            if attr.name.local_name.as_str() == "xmlns" {
                                if attr.value.as_str()
                                    != "http://www.sbml.org/sbml/level3/version1/core"
                                {
                                    return Err(format!("Expected xmlns=\"http://www.sbml.org/sbml/level3/version1/core\", found {}", attr.value));
                                }
                            }
                            if attr.name.local_name.as_str() == "qual" {
                                if attr.value.as_str()
                                    != "http://www.sbml.org/sbml/level3/version1/qual/version1"
                                {
                                    return Err(format!("Expected qual:xmlns=\"http://www.sbml.org/sbml/level3/version1/qual/version1\", found {}", attr.value));
                                }
                            }
                        }
                        return read_model(&mut parser);
                    } else {
                        return Err(format!("Expected sbml, found {}", name.local_name));
                    }
                }
                _ => {}
            }
        }
        return Err("Expected </sbml>, but found end of XML document.".to_string());
    }
}

pub type Layout = HashMap<String, (f64, f64)>;

fn resolve_specie<'a, 'b>(species: &'a Vec<(String, String)>, id: &'b str) -> &'a str {
    for (existing_id, name) in species.iter() {
        if existing_id == id {
            return name.as_str();
        }
    }
    panic!("Unknown specie: {}.", id);
}

fn rename_fn_variables(species: &Vec<(String, String)>, fun: FnUpdateTemp) -> FnUpdateTemp {
    return match fun {
        Const(_) => fun,
        Param(_, _) => fun,
        Var(name) => Var(resolve_specie(species, &name).to_string()),
        Binary(op, l, r) => Binary(
            op.clone(),
            Box::new(rename_fn_variables(species, *l)),
            Box::new(rename_fn_variables(species, *r)),
        ),
        Not(inner) => Not(Box::new(rename_fn_variables(species, *inner))),
    };
}

// Read a network and an associated layout!
fn read_model(parser: &mut EventReader<&[u8]>) -> Result<(BooleanNetwork, Layout), String> {
    let mut in_model = false;
    // species: Vec<(id,name)>
    let mut species: Vec<(String, String)> = Vec::new();
    let mut transitions: Vec<SBMLTransition> = Vec::new();
    let mut layout: HashMap<String, (f64, f64)> = HashMap::new();
    while let Ok(event) = parser.next() {
        match event {
            XmlEvent::EndElement { name } => {
                if name.local_name.as_str() == "model" {
                    species.sort_by_key(|(_, name)| name.clone());
                    // Remap transitions to use specie names instead of IDs.
                    for t in transitions.iter_mut() {
                        t.target = resolve_specie(&species, &t.target).to_string();
                        for (s, _) in t.sources.iter_mut() {
                            *s = resolve_specie(&species, s).to_string();
                        }
                    }
                    // Remap items in layout to use names, not IDs.
                    layout = layout
                        .into_iter()
                        .map(|(key, value)| (resolve_specie(&species, &key).to_string(), value))
                        .collect();
                    // Now actually build the network...

                    let mut rg = RegulatoryGraph::new(
                        species.iter().map(|(_, name)| name.clone()).collect(),
                    );
                    for t in &transitions {
                        for (s, m) in &t.sources {
                            rg.add_regulation(s, &t.target, true, *m)?;
                        }
                    }
                    let mut bn = BooleanNetwork::new(rg);
                    // Isolate all parameters in the network
                    let mut parameters = HashSet::new();
                    for t in &transitions {
                        if let Some(fun) = &t.function {
                            fun.dump_parameters(&mut parameters);
                        }
                    }
                    let mut parameters: Vec<Parameter> = parameters.into_iter().collect();
                    parameters.sort_by_key(|p| p.name.clone());

                    // Add the parameters (if there is a cardinality clash, here it will be thrown).
                    for parameter in &parameters {
                        bn.add_parameter(&parameter.name, parameter.cardinality)?;
                    }

                    // Actually build and add the functions
                    for t in transitions {
                        if let Some(fun) = t.function {
                            bn.add_update_function_template(
                                &t.target,
                                rename_fn_variables(&species, fun),
                            )?;
                        }
                    }
                    return Ok((bn, layout));
                }
            }
            XmlEvent::StartElement { name, .. } => match name.local_name.as_str() {
                "model" => {
                    in_model = true;
                }
                "listOfQualitativeSpecies" => {
                    if in_model {
                        read_species(parser, &mut species)?;
                        if species.is_empty() {
                            return Err("No species found in the model.".to_string());
                        }
                    }
                }
                "listOfTransitions" => {
                    if in_model {
                        read_transitions(parser, &mut transitions)?;
                    }
                }
                "layout" => {
                    if in_model {
                        read_layout(parser, &mut layout)?;
                    }
                }
                _ => {}
            },
            _ => {}
        }
    }
    return Err("Expected </model>, but found end of XML document.".to_string());
}

fn read_layout(
    parser: &mut EventReader<&[u8]>,
    layout: &mut HashMap<String, (f64, f64)>,
) -> Result<(), String> {
    let mut inside_glyph: Option<String> = None;
    while let Ok(event) = parser.next() {
        match event {
            XmlEvent::StartElement {
                name, attributes, ..
            } => {
                if &name.local_name == "generalGlyph" {
                    let mut reference = None;
                    for attr in attributes {
                        if &attr.name.local_name == "reference" {
                            reference = Some(attr.value);
                        }
                    }
                    if inside_glyph == None && reference.is_some() {
                        inside_glyph = reference;
                    }
                } else if &name.local_name == "position" {
                    if let Some(id) = &inside_glyph {
                        let mut x = None;
                        let mut y = None;
                        for attr in attributes {
                            if &attr.name.local_name == "x" {
                                x = Some(attr.value);
                            } else if &attr.name.local_name == "y" {
                                y = Some(attr.value);
                            }
                        }
                        match (x, y) {
                            (Some(x), Some(y)) => {
                                let x_num = x.parse::<f64>();
                                let y_num = y.parse::<f64>();
                                match (x_num, y_num) {
                                    (Ok(x), Ok(y)) => {
                                        layout.insert(id.clone(), (x, y));
                                    }
                                    // ignore errors - god knows what we can get in those attributes...
                                    _ => {}
                                }
                            }
                            _ => {}
                        }
                    }
                }
            }
            XmlEvent::EndElement { name } => {
                if &name.local_name == "layout" {
                    return Ok(());
                } else if &name.local_name == "generalGlyph" {
                    inside_glyph = None;
                }
            }
            _ => {}
        }
    }
    return Err("Expected </layout:layout>, but found end of XML document.".to_string());
}

fn normalize_name(name: String) -> String {
    let name_regex = Regex::new(r"[^a-zA-Z0-9_]").unwrap();
    let normalized = name_regex.replace_all(&name, "_").to_string();
    if normalized != name {
        println!("WARNING: Renaming `{}` to `{}`.", name, normalized);
    }
    return normalized;
}

/// Read the list of qualitative species from the XML document.
fn read_species(
    parser: &mut EventReader<&[u8]>,
    species: &mut Vec<(String, String)>,
) -> Result<(), String> {
    while let Ok(event) = parser.next() {
        match event {
            XmlEvent::StartElement {
                name, attributes, ..
            } => {
                if &name.local_name == "qualitativeSpecies" {
                    let mut id = String::new();
                    let mut name = String::new();
                    let mut is_boolean = true;
                    for attr in attributes {
                        if &attr.name.local_name == "maxLevel" {
                            is_boolean = &attr.value == "1";
                        }
                        if &attr.name.local_name == "id" {
                            id = attr.value;
                        } else if &attr.name.local_name == "name" {
                            name = normalize_name(attr.value);
                        }
                    }
                    if !is_boolean {
                        println!("WARNING: Species {} is not boolean.", name);
                    }

                    if id.is_empty() {
                        return Err("Found species with no id.".to_string());
                    } else {
                        // Name is optional, if missing default to ID.
                        if name.is_empty() {
                            name = id.clone();
                        }
                        // Check that species is unique.
                        for (existing_id, existing_name) in species.iter() {
                            if existing_name == &name || existing_id == &id {
                                return Err(format!("Duplicate species {}.", name));
                            }
                        }
                        species.push((id, name));
                    }
                }
            }
            XmlEvent::EndElement { name } => {
                if &name.local_name == "listOfQualitativeSpecies" {
                    return Ok(());
                }
            }
            _ => {}
        }
    }
    return Err(
        "Expected </qual:listOfQualitativeSpecies>, but found end of XML document.".to_string(),
    );
}

fn read_transitions(
    parser: &mut EventReader<&[u8]>,
    transitions: &mut Vec<SBMLTransition>,
) -> Result<(), String> {
    let mut in_input = false; // if listOfInputs has been read
    let mut in_output = false; // if listOfOutputs has been read
    let mut in_transtion = false; // if transition tag has been read
    let mut transition = SBMLTransition::new();
    while let Ok(event) = parser.next() {
        match event {
            XmlEvent::StartElement {
                name, attributes, ..
            } => match name.local_name.as_str() {
                "transition" => in_transtion = true,
                "listOfOutputs" => in_output = in_transtion,
                "listOfInputs" => in_input = in_transtion,
                "input" => {
                    if in_input {
                        let mut source = String::new();
                        let mut monotonicity = None;
                        for attr in attributes {
                            if &attr.name.local_name == "qualitativeSpecies" {
                                source = attr.value;
                            } else if &attr.name.local_name == "sign" {
                                if &attr.value == "positive" {
                                    monotonicity = Some(Monotonicity::Activation);
                                }
                                if &attr.value == "negative" {
                                    monotonicity = Some(Monotonicity::Inhibition);
                                }
                            }
                        }
                        if source.is_empty() {
                            return Err("Found source with no name.".to_string());
                        }
                        transition.sources.push((source, monotonicity));
                    }
                }
                "output" => {
                    if in_output {
                        if !transition.target.is_empty() {
                            return Err("Multiple targets for one transition.".to_string());
                        } else {
                            for attr in attributes {
                                if &attr.name.local_name == "qualitativeSpecies" {
                                    transition.target = attr.value;
                                }
                            }
                        }
                    }
                }
                "listOfFunctionTerms" => {
                    let update_template = read_update_function(parser)?;
                    transition.function = Some(update_template);
                }
                _ => {}
            },
            XmlEvent::EndElement { name } => {
                match name.local_name.as_str() {
                    "listOfTransitions" => return Ok(()),
                    "transition" => {
                        if transition.target.is_empty() {
                            return Err("Found transition with no target.".to_string());
                        } else {
                            transitions.push(transition.clone());
                            transition = SBMLTransition::new();
                        }
                        in_transtion = false;
                    }
                    "listOfOutputs" => in_output = false,
                    "listOfInputs" => in_input = false,
                    _ => {}
                };
            }
            _ => {}
        }
    }
    return Err("Expected </qual:listOfTransitions>, but found end of XML document.".to_string());
}

// TODO: Please please please find a nicer way to parse MathML or let the whole thing die...
fn read_update_function(parser: &mut EventReader<&[u8]>) -> Result<FnUpdateTemp, String> {
    let mut in_term = false;
    let mut in_math = false;
    let mut in_name = false; // inside ci
    let mut in_integer = false; // inside cn
    let mut in_param_name = false; // inside csymbol
                                   // (operation, arguments)
    let mut function_stack: Vec<(Op, Vec<FnUpdateTemp>)> = Vec::new();
    while let Ok(event) = parser.next() {
        match event {
            XmlEvent::StartElement {
                name, attributes, ..
            } => {
                match name.local_name.as_str() {
                    "functionTerm" => in_term = true,
                    "math" => {
                        if in_term {
                            in_math = true;
                            function_stack.push((Op::Math, Vec::new()));
                        }
                    }
                    "apply" => {
                        // if apply is found, push a new op to the stack and start reading it
                        if in_math {
                            function_stack.push((Op::None, Vec::new()));
                        }
                    }
                    // a function name is read - try to get latest apply and set it as operator
                    "and" | "or" | "xor" | "not" | "implies" | "eq" | "geq" | "leq" | "lt"
                    | "gt" => {
                        if let Some((op, _)) = function_stack.last_mut() {
                            if op != &Op::None {
                                return Err(format!("Unexpected function op {}", name.local_name));
                            } else {
                                *op = Op::Operation(name.local_name);
                            }
                        }
                    }
                    "csymbol" => {
                        if in_math {
                            in_param_name = true
                        }
                    }
                    "ci" => {
                        if in_math {
                            in_name = true
                        }
                    }
                    "cn" => {
                        if in_math {
                            let mut is_integer = false;
                            for attr in attributes {
                                if &attr.name.local_name == "type" {
                                    is_integer = attr.value.as_str() == "integer";
                                }
                            }
                            if !is_integer {
                                return Err("Found constant that is not an integer.".to_string());
                            }
                            in_integer = true
                        }
                    }
                    "true" => {
                        if in_math {
                            if let Some((_, args)) = function_stack.last_mut() {
                                args.push(FnUpdateTemp::Const(true))
                            }
                        }
                    }
                    "false" => {
                        if in_math {
                            if let Some((_, args)) = function_stack.last_mut() {
                                args.push(FnUpdateTemp::Const(false))
                            }
                        }
                    }
                    _ => {}
                }
            }
            XmlEvent::Characters(data) => {
                if in_name {
                    if let Some((_, args)) = function_stack.last_mut() {
                        args.push(FnUpdateTemp::Var(data.trim().to_string()));
                    }
                } else if in_integer {
                    if let Some((_, args)) = function_stack.last_mut() {
                        let c = data.trim().parse::<i32>();
                        if c == Ok(0) {
                            args.push(FnUpdateTemp::Const(false));
                        } else if c == Ok(1) {
                            args.push(FnUpdateTemp::Const(true));
                        } else {
                            return Err(format!(
                                "Cannot convert integer {:?} to boolean constant.",
                                c
                            ));
                        }
                    }
                } else if in_param_name {
                    if let Some((op, _)) = function_stack.last_mut() {
                        *op = Op::Parameter(data.trim().to_string());
                    }
                }
            }
            XmlEvent::EndElement { name } => {
                match name.local_name.as_str() {
                    "functionTerm" => in_term = false,
                    "math" => in_math = false,
                    "ci" => in_name = false,
                    "cn" => in_integer = false,
                    "listOfFunctionTerms" => {
                        if let Some((op, args)) = function_stack.pop() {
                            if op != Op::Math || args.len() != 1 {
                                return Err(format!(
                                    "Function parsing failed on {:?} with {:?} args.",
                                    op, args
                                ));
                            } else {
                                return Ok(args.into_iter().next().unwrap());
                            }
                        } else {
                            // if the update function is empty, it defaults to false
                            return Ok(FnUpdateTemp::Const(false));
                        }
                    }
                    "apply" => {
                        // Try to finish last apply term on stack
                        if let Some((op, args)) = function_stack.last() {
                            let fun = match op {
                                Op::None | Op::Math => {
                                    Err("Apply used without any operation or inconsistently."
                                        .to_string())
                                }
                                Op::Parameter(name) => {
                                    let valid_args: Vec<String> = args
                                        .iter()
                                        .filter_map(|f| {
                                            if let Var(name) = f {
                                                Some(name.clone())
                                            } else {
                                                None
                                            }
                                        })
                                        .collect();
                                    if valid_args.len() != args.len() {
                                        Err("Parameter function can be only called with variables as arguments".to_string())
                                    } else {
                                        Ok(Param(name.clone(), valid_args))
                                    }
                                }
                                Op::Operation(op) => {
                                    if op.is_empty() {
                                        Err("Apply used without any operation.".to_string())
                                    } else {
                                        if op.as_str() == "not" {
                                            if args.len() != 1 {
                                                Err(format!(
                                                    "Not takes exactly one argument. {} given.",
                                                    args.len()
                                                ))
                                            } else {
                                                Ok(FnUpdateTemp::Not(Box::new(args[0].clone())))
                                            }
                                        } else if op.as_str() == "eq" {
                                            if args.len() != 2 {
                                                Err(format!(
                                                    "Eq takes exactly two arguments. {} given.",
                                                    args.len()
                                                ))
                                            } else {
                                                let left = &args[0];
                                                let right = &args[1];
                                                match (left, right) {
                                                    (Const(a), Const(b)) => Ok(Const(a == b)),
                                                    (Const(true), Var(name)) => {
                                                        Ok(Var(name.clone()))
                                                    }
                                                    (Var(name), Const(true)) => {
                                                        Ok(Var(name.clone()))
                                                    }
                                                    (Const(false), Var(name)) => {
                                                        Ok(Not(Box::new(Var(name.clone()))))
                                                    }
                                                    (Var(name), Const(false)) => {
                                                        Ok(Not(Box::new(Var(name.clone()))))
                                                    }
                                                    (l, r) => Ok(Binary(
                                                        BinaryOp::Iff,
                                                        Box::new(l.clone()),
                                                        Box::new(r.clone()),
                                                    )),
                                                }
                                            }
                                        } else if op.as_str() == "geq" {
                                            // (A >= B) <=> (!B | A) <=> (B => A)
                                            if args.len() != 2 {
                                                Err(format!(
                                                    "GEQ takes exactly two arguments. {} given.",
                                                    args.len()
                                                ))
                                            } else {
                                                let left = &args[0];
                                                let right = &args[1];
                                                match (left, right) {
                                                    (Const(a), Const(b)) => Ok(Const(!b | a)),
                                                    (Const(true), Var(_)) => Ok(Const(true)),
                                                    (Var(name), Const(true)) => {
                                                        Ok(Var(name.clone()))
                                                    }
                                                    (Const(false), Var(name)) => {
                                                        Ok(Not(Box::new(Var(name.clone()))))
                                                    }
                                                    (Var(_), Const(false)) => Ok(Const(true)),
                                                    (l, r) => Ok(Binary(
                                                        BinaryOp::Imp,
                                                        Box::new(r.clone()),
                                                        Box::new(l.clone()),
                                                    )),
                                                }
                                            }
                                        } else if op.as_str() == "leq" {
                                            // (A <= B) <=> (!A | B) <=> (A => B)
                                            if args.len() != 2 {
                                                Err(format!(
                                                    "LEQ takes exactly two arguments. {} given.",
                                                    args.len()
                                                ))
                                            } else {
                                                let left = &args[0];
                                                let right = &args[1];
                                                match (left, right) {
                                                    (Const(a), Const(b)) => Ok(Const(!a | b)),
                                                    (Const(true), Var(name)) => {
                                                        Ok(Var(name.clone()))
                                                    }
                                                    (Var(_), Const(true)) => Ok(Const(true)),
                                                    (Const(false), Var(_)) => Ok(Const(true)),
                                                    (Var(name), Const(false)) => {
                                                        Ok(Not(Box::new(Var(name.clone()))))
                                                    }
                                                    (l, r) => Ok(Binary(
                                                        BinaryOp::Imp,
                                                        Box::new(l.clone()),
                                                        Box::new(r.clone()),
                                                    )),
                                                }
                                            }
                                        } else if op.as_str() == "lt" {
                                            // (A < B) <=> (!A & B)
                                            if args.len() != 2 {
                                                Err(format!(
                                                    "LT takes exactly two arguments. {} given.",
                                                    args.len()
                                                ))
                                            } else {
                                                let left = &args[0];
                                                let right = &args[1];
                                                match (left, right) {
                                                    (Const(a), Const(b)) => Ok(Const(!a & b)),
                                                    (Const(true), Var(_)) => Ok(Const(false)),
                                                    (Var(name), Const(true)) => {
                                                        Ok(Not(Box::new(Var(name.clone()))))
                                                    }
                                                    (Const(false), Var(name)) => {
                                                        Ok(Var(name.clone()))
                                                    }
                                                    (Var(_), Const(false)) => Ok(Const(false)),
                                                    (l, r) => Ok(Binary(
                                                        BinaryOp::And,
                                                        Box::new(Not(Box::new(l.clone()))),
                                                        Box::new(r.clone()),
                                                    )),
                                                }
                                            }
                                        } else if op.as_str() == "gt" {
                                            // (A > B) <=> (A & !B)
                                            if args.len() != 2 {
                                                Err(format!(
                                                    "GT takes exactly two arguments. {} given.",
                                                    args.len()
                                                ))
                                            } else {
                                                let left = &args[0];
                                                let right = &args[1];
                                                match (left, right) {
                                                    (Const(a), Const(b)) => Ok(Const(a & !b)),
                                                    (Const(true), Var(name)) => {
                                                        Ok(Not(Box::new(Var(name.clone()))))
                                                    }
                                                    (Var(_), Const(true)) => Ok(Const(false)),
                                                    (Const(false), Var(_)) => Ok(Const(false)),
                                                    (Var(name), Const(false)) => {
                                                        Ok(Var(name.clone()))
                                                    }
                                                    (l, r) => Ok(Binary(
                                                        BinaryOp::And,
                                                        Box::new(l.clone()),
                                                        Box::new(Not(Box::new(r.clone()))),
                                                    )),
                                                }
                                            }
                                        } else {
                                            // a binary op remains then...
                                            let op = match op.as_str() {
                                                "and" => Ok(BinaryOp::And),
                                                "or" => Ok(BinaryOp::Or),
                                                "xor" => Ok(BinaryOp::Xor),
                                                "implies" => Ok(BinaryOp::Imp),
                                                op => Err(format!("Unknown operator {}", op)),
                                            }?;
                                            if args.len() < 2 {
                                                Err("Function argument list must have at least two entries.".to_string())
                                            } else {
                                                let one = args[0].clone();
                                                Ok(args.iter().skip(1).fold(one, |a, b| {
                                                    Binary(op, Box::new(a), Box::new(b.clone()))
                                                }))
                                            }
                                        }
                                    }
                                }
                            }?;

                            function_stack.pop();

                            if let Some((_, args)) = function_stack.last_mut() {
                                args.push(fun);
                            } else {
                                unreachable!();
                            }
                        }
                    }
                    _ => {}
                }
            }
            _ => {}
        }
    }
    return Err("Expected </qual:listOfFunctionTerms> but found end of document.".to_string());
}

#[derive(Clone, PartialEq, Eq, Debug)]
struct SBMLTransition {
    sources: Vec<(String, Option<Monotonicity>)>,
    target: String,
    function: Option<FnUpdateTemp>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum Op {
    None,
    Math,
    Operation(String),
    Parameter(String),
}

impl SBMLTransition {
    fn new() -> SBMLTransition {
        return SBMLTransition {
            sources: Vec::new(),
            target: String::new(),
            function: None,
        };
    }
}

#[cfg(test)]
mod tests {
    use crate::BooleanNetwork;
    use std::collections::HashMap;
    use std::convert::TryFrom;

    #[test]
    fn test() {
        let model =
            std::fs::read_to_string("sbml_models/g2a.sbml").expect("Cannot open result file.");
        let (actual, layout) = BooleanNetwork::from_sbml(model.as_str()).unwrap();
        // Compared by hand...
        let mut expected_layout = HashMap::new();
        expected_layout.insert("CtrA".to_string(), (419.0, 94.0));
        expected_layout.insert("GcrA".to_string(), (325.0, 135.0));
        expected_layout.insert("DnaA".to_string(), (374.0, 224.0));
        expected_layout.insert("CcrM".to_string(), (462.0, 222.0));
        expected_layout.insert("SciP".to_string(), (506.0, 133.0));
        let expected = BooleanNetwork::try_from(
            "
            CtrA -> CtrA
            GcrA -> CtrA
            CcrM -| CtrA
            SciP -| CtrA
            CtrA -| GcrA
            DnaA -> GcrA
            CtrA -> DnaA
            GcrA -| DnaA
            DnaA -| DnaA
            CcrM -> DnaA
            CtrA -> CcrM
            CcrM -| CcrM
            SciP -| CcrM
            CtrA -> SciP
            DnaA -| SciP
            $CtrA: ((((!CtrA & GcrA) & !CcrM) & !SciP) | ((CtrA & !CcrM) & !SciP))
            $GcrA: (!CtrA & DnaA)
            $DnaA: (((CtrA & !GcrA) & !DnaA) & CcrM)
            $CcrM: ((CtrA & !CcrM) & !SciP)
            $SciP: (CtrA & !DnaA)
        ",
        )
        .unwrap();
        assert_eq!(actual, expected);
        assert_eq!(layout, expected_layout);
    }

    #[test]
    fn test_name_resolution() {
        let model =
            std::fs::read_to_string("sbml_models/g2a_with_names.sbml").expect("Cannot open result file.");
        let (actual, layout) = BooleanNetwork::from_sbml(model.as_str()).unwrap();
        // Compared by hand...
        // CtrA(+) contains three invalid characters that should be normalized to CtrA___
        let mut expected_layout = HashMap::new();
        expected_layout.insert("CtrA___".to_string(), (419.0, 94.0));
        expected_layout.insert("GcrA".to_string(), (325.0, 135.0));
        expected_layout.insert("DnaA".to_string(), (374.0, 224.0));
        expected_layout.insert("CcrM".to_string(), (462.0, 222.0));
        expected_layout.insert("SciP".to_string(), (506.0, 133.0));
        let expected = BooleanNetwork::try_from(
            "
            CtrA___ -> CtrA___
            GcrA -> CtrA___
            CcrM -| CtrA___
            SciP -| CtrA___
            CtrA___ -| GcrA
            DnaA -> GcrA
            CtrA___ -> DnaA
            GcrA -| DnaA
            DnaA -| DnaA
            CcrM -> DnaA
            CtrA___ -> CcrM
            CcrM -| CcrM
            SciP -| CcrM
            CtrA___ -> SciP
            DnaA -| SciP
            $CtrA___: ((((!CtrA___ & GcrA) & !CcrM) & !SciP) | ((CtrA___ & !CcrM) & !SciP))
            $GcrA: (!CtrA___ & DnaA)
            $DnaA: (((CtrA___ & !GcrA) & !DnaA) & CcrM)
            $CcrM: ((CtrA___ & !CcrM) & !SciP)
            $SciP: (CtrA___ & !DnaA)
        ",
        )
            .unwrap();
        assert_eq!(actual, expected);
        assert_eq!(layout, expected_layout);
    }
}
