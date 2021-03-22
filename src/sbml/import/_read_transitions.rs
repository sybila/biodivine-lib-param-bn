use crate::sbml::import::_read_mathml::{read_mathml, MathMl};
use crate::sbml::import::{child_tags, read_unique_child, MATHML, SBML_QUAL};
use roxmltree::{ExpandedName, Node};

/// Maps almost directly to the SBML transition input tag.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SbmlTransitionInput {
    pub id: Option<String>, // Note that a missing ID is not entirely according to spec, but they do appear in models people use.
    pub qual_species: String,
    pub transition_effect: Option<String>,
    pub sign: Option<String>,
}

/// Maps almost directly to the SBML transition output tag.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SbmlTransitionOutput {
    pub id: Option<String>, // Note that a missing ID is not entirely according to spec, but they do appear in models people use.
    pub qual_species: String,
    pub transition_effect: Option<String>,
}

/// Represents an SBML transition term (note that default term should not have math in it).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SbmlTransitionTerm {
    pub result_level: u32,
    pub math: Option<MathMl>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SbmlTransition {
    pub id: String,
    pub inputs: Vec<SbmlTransitionInput>,
    pub outputs: Vec<SbmlTransitionOutput>,
    pub default_term: Option<SbmlTransitionTerm>, // Is none if the whole function is unspecified
    pub function_terms: Vec<SbmlTransitionTerm>,
}

pub fn read_transitions(model: Node) -> Result<Vec<SbmlTransition>, String> {
    let mut result = Vec::new();

    let list = read_unique_child(model, (SBML_QUAL, "listOfTransitions"))?;

    let transitions = list
        .children()
        .filter(|node| node.tag_name() == ExpandedName::from((SBML_QUAL, "transition")));

    for transition in transitions {
        result.push(read_transition(transition)?)
    }

    Ok(result)
}

pub fn read_transition(transition: Node) -> Result<SbmlTransition, String> {
    let id = transition
        .attribute((SBML_QUAL, "id"))
        .ok_or_else(|| "Transition with a missing id found.".to_string())?;

    // Inputs are optional when there aren't any.
    let inputs = read_unique_child(transition, (SBML_QUAL, "listOfInputs")).ok();
    let outputs = read_unique_child(transition, (SBML_QUAL, "listOfOutputs"))?;
    // Terms are an optional element.
    let terms = read_unique_child(transition, (SBML_QUAL, "listOfFunctionTerms")).ok();

    let inputs = if let Some(inputs) = inputs {
        child_tags(inputs, (SBML_QUAL, "input"))
    } else {
        Vec::new()
    };
    let outputs = child_tags(outputs, (SBML_QUAL, "output"));

    let default_term = if let Some(terms) = terms {
        let default_term = read_unique_child(terms, (SBML_QUAL, "defaultTerm"))?;
        Some(read_transition_term(default_term, id)?)
    } else {
        None
    };

    let terms = if let Some(terms) = terms {
        child_tags(terms, (SBML_QUAL, "functionTerm"))
    } else {
        Vec::new()
    };

    let mut transition = SbmlTransition {
        id: id.to_string(),
        inputs: Vec::new(),
        outputs: Vec::new(),
        default_term,
        function_terms: Vec::new(),
    };

    if transition
        .default_term
        .as_ref()
        .map(|t| t.math.is_some())
        .unwrap_or(false)
    {
        return Err(format!("Default term in transition {} has math.", id));
    }

    for input in inputs {
        transition.inputs.push(read_transition_input(input, id)?);
    }

    for output in outputs {
        transition.outputs.push(read_transition_output(output, id)?);
    }

    for term in terms {
        transition
            .function_terms
            .push(read_transition_term(term, id)?);
    }

    Ok(transition)
}

fn read_transition_input(input: Node, transition_id: &str) -> Result<SbmlTransitionInput, String> {
    let species = input.attribute((SBML_QUAL, "qualitativeSpecies"));
    let effect = input.attribute((SBML_QUAL, "transitionEffect"));
    let sign = input.attribute((SBML_QUAL, "sign"));
    let id = input.attribute((SBML_QUAL, "id"));
    if species.is_none() {
        return Err(format!(
            "Transition {} is missing an input species.",
            transition_id
        ));
    }

    Ok(SbmlTransitionInput {
        id: id.map(|s| s.to_string()),
        qual_species: species.unwrap().to_string(),
        transition_effect: effect.map(|s| s.to_string()),
        sign: sign.map(|s| s.to_string()),
    })
}

fn read_transition_output(
    output: Node,
    transition_id: &str,
) -> Result<SbmlTransitionOutput, String> {
    let species = output.attribute((SBML_QUAL, "qualitativeSpecies"));
    let effect = output.attribute((SBML_QUAL, "transitionEffect"));
    let id = output.attribute((SBML_QUAL, "id"));
    if species.is_none() {
        return Err(format!(
            "Transition output in {} is missing an output species.",
            transition_id
        ));
    }

    Ok(SbmlTransitionOutput {
        id: id.map(|s| s.to_string()),
        qual_species: species.unwrap().to_string(),
        transition_effect: effect.map(|s| s.to_string()),
    })
}

fn read_transition_term(term: Node, transition_id: &str) -> Result<SbmlTransitionTerm, String> {
    let result_level = term.attribute((SBML_QUAL, "resultLevel"));
    if result_level.is_none() {
        return Err(format!(
            "Term result level not specified in {}.",
            transition_id
        ));
    }
    let result_level = result_level.unwrap();
    let level = result_level.parse::<u32>();
    if level.is_err() {
        return Err(format!(
            "Term result level is not a number in {}. {} given.",
            transition_id, result_level
        ));
    }

    let math = read_unique_child(term, (MATHML, "math")).ok();
    let math = Ok(math).and_then(|node| node.map(read_mathml).transpose())?;

    Ok(SbmlTransitionTerm {
        result_level: level.unwrap(),
        math,
    })
}
