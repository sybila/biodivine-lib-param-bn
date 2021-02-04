use crate::sbml::import::_convert_mathml_to_fn_update::sbml_transition_to_update_function;
use crate::sbml::import::_read_layout::read_sbml_layout;
use crate::sbml::import::_read_mathml::MathML;
use crate::sbml::import::_read_species::{read_species, SBMLSpecie};
use crate::sbml::import::_read_transitions::{read_transitions, SBMLTransition};
use crate::sbml::Layout;
use crate::{BooleanNetwork, Monotonicity, RegulatoryGraph};
use regex::Regex;
use roxmltree::{ExpandedName, Node};
use std::collections::{HashMap, HashSet};

const SBML: &'static str = "http://www.sbml.org/sbml/level3/version1/core";
const SBML_QUAL: &'static str = "http://www.sbml.org/sbml/level3/version1/qual/version1";
const SBML_LAYOUT: &'static str = "http://www.sbml.org/sbml/level3/version1/layout/version1";
const MATHML: &'static str = "http://www.w3.org/1998/Math/MathML";

mod _convert_mathml_to_fn_update;
mod _read_layout;
mod _read_mathml;
mod _read_species;
mod _read_transitions;

impl BooleanNetwork {
    pub fn from_sbml(model_file: &str) -> Result<(BooleanNetwork, Layout), String> {
        BooleanNetwork::from_sbml_strict(model_file, &mut Vec::new())
    }

    pub fn from_sbml_strict(
        model_file: &str,
        warnings: &mut Vec<String>,
    ) -> Result<(BooleanNetwork, Layout), String> {
        let document =
            roxmltree::Document::parse(model_file).map_err(|e| format!("XML Error: {:?}", e))?;
        let root = document.root();
        if root.children().count() == 0 {
            return Err(format!("Document is empty."));
        }
        if root.children().count() > 1 {
            return Err(format!(
                "Document contains multiple top-level tags. Only SBML expected."
            ));
        }
        let sbml = root.children().next().unwrap();
        if sbml.tag_name().name() != "sbml" {
            return Err(format!("Root element is not <sbml>."));
        }

        if sbml.tag_name().namespace() != Some(SBML) {
            return Err(format!(
                "The document does not use the SBML Level3 namespace."
            ));
        }

        let requires_qual = sbml.attribute((SBML_QUAL, "required"));
        if requires_qual != Some("true") {
            warnings.push(format!(
                "This model does not declare SBML-qual as a requirement."
            ));
        }

        let model = read_unique_child(sbml, (SBML, "model"))?;

        let species = read_species(model)?;
        let transitions = read_transitions(model)?;

        for specie in &species {
            if specie.max_level.is_some() && specie.max_level.unwrap() != 1 {
                return Err(format!(
                    "Specie with ID {} is not Boolean (max level {}).",
                    specie.id,
                    specie.max_level.unwrap()
                ));
            }
        }

        let specie_to_name = create_normalized_names(&species, warnings)?;
        assert_eq!(specie_to_name.len(), species.len());

        let mut names: Vec<String> = specie_to_name.values().cloned().collect();
        names.sort();
        let mut regulatory_graph = RegulatoryGraph::new(names);
        create_regulations(&mut regulatory_graph, &transitions, &specie_to_name)?;

        let mut boolean_network = BooleanNetwork::new(regulatory_graph);
        for transition in &transitions {
            if transition.default_term.is_some() {
                // Only continue if this transition has a function
                // First, create parameters used by this transition.
                for term in &transition.function_terms {
                    if let Some(math) = &term.math {
                        create_explicit_parameters(math, &mut boolean_network)?;
                    }
                }

                // At this point we know this won't fail because we already created the regulations.
                let out_var = &specie_to_name[&transition.outputs[0].qual_species];
                let out_var = boolean_network.graph.find_variable(out_var).unwrap();
                let update_function = sbml_transition_to_update_function(
                    &boolean_network,
                    transition,
                    &specie_to_name,
                )?;
                boolean_network.add_update_function(out_var, update_function)?;
            }
        }

        let layout = read_sbml_layout(model);

        // A mapping from SBML ids to layout positions (if available)
        let layout = match layout {
            Ok(l) => l.glyphs,
            Err(err) => {
                warnings.push(err);
                HashMap::new()
            }
        };

        let mut transformed_layout: HashMap<String, (f64, f64)> = HashMap::new();

        for (k, v) in &layout {
            let var_name = specie_to_name.get(k);
            if let Some(var) = var_name {
                transformed_layout.insert(var.clone(), v.clone());
            } else {
                warnings.push(format!("Unknown layout glyph `{}`.", k));
            }
        }

        Ok((boolean_network, transformed_layout))
    }
}

/// Find the given tag in a parent `Node`. Returns error if the tag does not exist or
/// is present in multiple instances.
fn read_unique_child<'a, 'input: 'a>(
    parent: Node<'a, 'input>,
    name: (&'static str, &'static str),
) -> Result<Node<'a, 'input>, String> {
    let name = ExpandedName::from(name);
    let mut tags = parent.children().filter(|node| node.tag_name() == name);
    let fst = tags.next();
    if let Some(fst) = fst {
        let snd = tags.next();
        if snd.is_none() {
            Ok(fst)
        } else {
            Err(format!(
                "Multiple {} found in {}.",
                name.name(),
                parent.tag_name().name()
            ))
        }
    } else {
        Err(format!(
            "Could not find tag {} in {}.",
            name.name(),
            parent.tag_name().name()
        ))
    }
}

/// Find all child `Nodes` that have a given name.
fn child_tags<'a, 'input: 'a>(
    parent: Node<'a, 'input>,
    name: (&'static str, &'static str),
) -> Vec<Node<'a, 'input>> {
    let name = ExpandedName::from(name);
    parent.children().filter(|n| n.tag_name() == name).collect()
}

/// Assigns every specie a biodivine-friendly name. Returns a mapping between SBML IDs and
/// valid specie names.
///
/// If the name contains an invalid character, it is replaced with `_`.
/// If there are duplicate names, they are prefixed with their IDs.
fn create_normalized_names(
    species: &[SBMLSpecie],
    warnings: &mut Vec<String>,
) -> Result<HashMap<String, String>, String> {
    let mut id_to_name = HashMap::new();
    let mut name_to_id = HashMap::new();
    let mut duplicates = HashSet::new();

    // First, eliminate invalid characters and detect duplicates simultaneously.
    let name_regex = Regex::new(r"[^a-zA-Z0-9_]").unwrap();
    for specie in species {
        let name = specie.name.clone().unwrap_or(specie.id.clone());
        let normalized = name_regex.replace_all(&name, "_").to_string();
        if normalized != name {
            warnings.push(format!(
                "Renamed `{}` to `{}`. Original name contains invalid symbols.",
                name, normalized
            ));
        }
        if id_to_name
            .insert(specie.id.clone(), normalized.clone())
            .is_some()
        {
            return Err(format!("Duplicate specie ID found: `{}`", specie.id));
        }
        if let Some(previous) = name_to_id.insert(normalized.clone(), specie.id.clone()) {
            duplicates.insert(previous);
            duplicates.insert(specie.id.clone());
        }
    }

    // Now try to rename duplicates:
    for duplicate_id in duplicates {
        let specie = species
            .iter()
            .find(|s| s.id == duplicate_id)
            .cloned()
            .unwrap();
        let current_name = &id_to_name[&specie.id];
        let concat = format!("{}_{}", specie.id, current_name);
        let mut updated_name = concat.clone();
        let mut i = 0;
        while name_to_id.contains_key(&updated_name) {
            // This really should not happen, but in case this still clashes with something.
            updated_name = format!("{}_{}", concat, i);
            i += 1;
        }
        warnings.push(format!(
            "Renamed `{}` to `{}` to avoid duplicates.",
            current_name, updated_name
        ));
        id_to_name.insert(specie.id.clone(), updated_name.clone());
    }

    Ok(id_to_name)
}

/// Add regulations to a `RegulatoryGraph` based on the collection of `SBMLTransitions`.
///
/// Monotonicity is inferred from the `sign` property of the transition. Observability is
/// added if the MathML formula in the transition contains the input variable.
fn create_regulations(
    rg: &mut RegulatoryGraph,
    transitions: &[SBMLTransition],
    id_to_var: &HashMap<String, String>,
) -> Result<(), String> {
    for transition in transitions {
        if transition.outputs.len() != 1 {
            return Err(format!(
                "Every transition can have only one output. `{}` has {}.",
                transition.id,
                transition.outputs.len()
            ));
        }

        let out_specie = &transition.outputs[0].qual_species;
        let out_variable = id_to_var.get(out_specie);
        if out_variable.is_none() {
            return Err(format!(
                "Unknown output specie `{}` used in transition `{}`.",
                out_specie, transition.id
            ));
        }

        for input in &transition.inputs {
            let in_id = &input.id;
            let in_specie = &input.qual_species;
            let in_variable = id_to_var.get(in_specie);
            if in_variable.is_none() {
                return Err(format!(
                    "Unknown input specie `{}` used in transition `{}`.",
                    in_specie, transition.id
                ));
            }

            // We enable observability for empty functions because this typically means
            // it was created as a completely unspecified free function, so it makes sense
            // the inputs are observable.
            let is_observable = transition.function_terms.iter().any(|t| {
                t.math
                    .as_ref()
                    .map(|m| m.contains_identifier(in_specie) || m.contains_identifier(in_id))
                    .unwrap_or(false)
            }) || transition.function_terms.is_empty();

            let monotonicity = input.sign.as_ref().and_then(|sign| {
                if sign == "positive" {
                    Some(Monotonicity::Activation)
                } else if sign == "negative" {
                    Some(Monotonicity::Inhibition)
                } else {
                    None
                }
            });

            rg.add_regulation(
                in_variable.unwrap(),
                out_variable.unwrap(),
                is_observable,
                monotonicity,
            )?;
        }
    }
    Ok(())
}

/// Create any explicit parameters used in the given MathML tree.
fn create_explicit_parameters(math: &MathML, network: &mut BooleanNetwork) -> Result<(), String> {
    match math {
        MathML::Integer(_) => Ok(()),
        MathML::Identifier(_) => Ok(()),
        MathML::Apply(_, args) => {
            for a in args {
                create_explicit_parameters(a, network)?;
            }
            Ok(())
        }
        MathML::SymbolApply(name, args) => {
            if let Some(p) = network.find_parameter(name) {
                let current = network.get_parameter(p).cardinality;
                if current != args.len() {
                    return Err(format!(
                        "Parameter `{}` is used with cardinality {} as well as {}",
                        name,
                        current,
                        args.len()
                    ));
                }
            } else {
                // Seems that at the moment there are no restrictions on parameter names (weird).
                network.add_parameter(name, args.len())?;
            }
            // Also run this, in case we allow complex parameter applications in the future.
            for a in args {
                create_explicit_parameters(a, network)?;
            }
            Ok(())
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::{BooleanNetwork, Monotonicity};
    use pretty_assertions::assert_eq;
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
        let model = std::fs::read_to_string("sbml_models/g2a_with_names.sbml")
            .expect("Cannot open result file.");
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

    #[test]
    fn test_cell_collective() {
        let model = std::fs::read_to_string("sbml_models/cell_collective_vut.sbml")
            .expect("Cannot open result file.");
        let (actual, layout) = BooleanNetwork::from_sbml(model.as_str()).unwrap();
        assert_eq!(actual.graph.num_vars(), 66);
        assert_eq!(actual.graph.regulations.len(), 139);
        assert_eq!(layout.len(), actual.graph.num_vars());
        // Normal variable
        assert!(actual.graph.find_variable("glucose").is_some());
        // Normalized variable
        assert!(actual.graph.find_variable("lactic_acid").is_some());
        // Some regulation
        assert_eq!(
            actual
                .graph
                .find_regulation(
                    actual.graph.find_variable("sigG").unwrap(),
                    actual.graph.find_variable("sigK").unwrap(),
                )
                .unwrap()
                .monotonicity,
            Some(Monotonicity::Activation)
        )
    }

    #[test]
    fn test_apoptosis_stable() {
        // Has colliding names/ids
        let model = std::fs::read_to_string("sbml_models/apoptosis_stable.sbml")
            .expect("Cannot open result file.");
        let (actual, layout) = BooleanNetwork::from_sbml(model.as_str()).unwrap();
        assert_eq!(layout.len(), actual.graph.num_vars());
        // Normal variable
        assert!(actual.graph.find_variable("Apoptosome_complex").is_some());
        // Normalized variable
        assert!(actual.graph.find_variable("FAS_FASL_complex").is_some());
        // Duplicate name
        assert!(actual.graph.find_variable("sa19_CASP9_Cytoplasm").is_some());
        assert!(actual.graph.find_variable("sa47_CASP9_Cytoplasm").is_some());
    }

    #[test]
    fn test_hmox_pathway() {
        // Has OR with one argument
        let model = std::fs::read_to_string("sbml_models/hmox1_pathway.sbml")
            .expect("Cannot open result file.");
        let (actual, layout) = BooleanNetwork::from_sbml(model.as_str()).unwrap();
        assert_eq!(layout.len(), actual.graph.num_vars());
    }

    #[test]
    fn test_apoptosis_network() {
        let model = std::fs::read_to_string("sbml_models/apoptosis_network.sbml")
            .expect("Cannot open result file.");
        let (actual, layout) = BooleanNetwork::from_sbml(model.as_str()).unwrap();
        assert_eq!(actual.graph.num_vars(), 41);
        assert_eq!(layout.len(), 0);
    }
}
