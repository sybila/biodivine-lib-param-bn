use crate::_aeon_parser::FnUpdateTemp;
use crate::{BooleanNetwork, RegulatoryGraph};
use std::collections::{HashMap, HashSet};
use std::convert::TryFrom;

impl BooleanNetwork {
    /// Try to load a Boolean network from a `.bnet` model.
    ///
    /// Note that this is currently only a "best effort" implementation and you may encounter
    /// unsupported `bnet` models.
    pub fn try_from_bnet(model_string: &str) -> Result<BooleanNetwork, String> {
        let mut model_map: HashMap<String, String> = HashMap::new();
        let mut variables = HashSet::new();
        for line in model_string.lines() {
            if line.trim().starts_with('#')
                || line.trim().is_empty()
                || line.trim().starts_with("targets,")
            {
                continue; // Skip comments, empty lines and header.
            } else {
                let segments = line.split(',').collect::<Vec<_>>();
                if segments.len() != 2 {
                    return Err(format!("Unexpected line: `{}`", line));
                }

                let variable_name = segments[0].trim().to_string();
                if model_map.contains_key(&variable_name) {
                    return Err(format!(
                        "Duplicate function declaration for `{}`.",
                        variable_name
                    ));
                }

                // Also scan regulators for variable names, as inputs don't need to have a function.
                variables.insert(variable_name.clone());
                let function_string = segments[1].trim().to_string();
                let function_template = FnUpdateTemp::try_from(function_string.as_str())?;
                function_template.dump_variables(&mut variables);

                model_map.insert(variable_name, function_string);
            }
        }

        let mut variables = variables.into_iter().collect::<Vec<_>>();
        variables.sort();
        let mut graph = RegulatoryGraph::new(variables.clone());

        // First, build graph.
        for variable in &variables {
            if let Some(function) = model_map.get(variable) {
                // TODO: This is quite far from correct.
                // Boolean functions in `bnet` can use other special symbols, but are "essentially"
                // the same in terms of basic logical operators. So unless the function is using
                // something special, this should work.
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

        // Then add functions.
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

    const BNET_MODEL: &str = r"# model in BoolNet format
# the header targets, factors is mandatory to be importable in the R package BoolNet

targets, factors
Apoptosis,      !DNA_damage&!ERK&p38&JNK&!MDM2 | DNA_damage&!ERK&!p38&JNK&!MDM2 | DNA_damage&!ERK&p38&JNK
DNA_damage,     DNA_damage
EGFR_stimulus,  EGFR_stimulus
ERK,            !DNA_damage&!ERK&!p38&!JNK&!PLCG&RAS | !DNA_damage&!ERK&!p38&!JNK&PLCG&!PI3K | !DNA_damage&!ERK&!p38&!JNK&PLCG&PI3K&RAS | !DNA_damage&ERK&!p38&!JNK&RAS | DNA_damage&!ERK&!p38&!JNK&!PLCG&RAS | DNA_damage&!ERK&!p38&!JNK&PLCG&!PI3K | DNA_damage&!ERK&!p38&!JNK&PLCG&PI3K&!RAS&!MDM2 | DNA_damage&!ERK&!p38&!JNK&PLCG&PI3K&RAS | DNA_damage&ERK&!p38&!JNK&RAS
FGFR3_stimulus, FGFR3_stimulus
GADD45,         !TGFBR_stimulus&!DNA_damage&p38&!MDM2 | !TGFBR_stimulus&DNA_damage&!p38&!MDM2 | !TGFBR_stimulus&DNA_damage&p38 | TGFBR_stimulus
GRB2,           !EGFR_stimulus&!FGFR3_stimulus&!TGFBR_stimulus&ERK&!GRB2&!PLCG | !EGFR_stimulus&!FGFR3_stimulus&TGFBR_stimulus | !EGFR_stimulus&FGFR3_stimulus&!TGFBR_stimulus&!GRB2&!PLCG | !EGFR_stimulus&FGFR3_stimulus&TGFBR_stimulus | EGFR_stimulus&!TGFBR_stimulus&!GRB2&!PLCG | EGFR_stimulus&TGFBR_stimulus
Growth_Arrest,  !DNA_damage&p38&!MDM2 | DNA_damage&!p38&!MDM2 | DNA_damage&p38
JNK,            !TGFBR_stimulus&!DNA_damage&!ERK&!p38&!GADD45&RAS | !TGFBR_stimulus&!DNA_damage&!ERK&!p38&GADD45 | !TGFBR_stimulus&!DNA_damage&!ERK&p38&GADD45&RAS | !TGFBR_stimulus&!DNA_damage&ERK&GADD45&RAS | !TGFBR_stimulus&DNA_damage&!ERK&!p38 | !TGFBR_stimulus&DNA_damage&!ERK&p38&!GADD45&RAS | !TGFBR_stimulus&DNA_damage&!ERK&p38&GADD45 | !TGFBR_stimulus&DNA_damage&ERK&!GADD45&RAS | !TGFBR_stimulus&DNA_damage&ERK&GADD45 | TGFBR_stimulus&!DNA_damage&!ERK&!p38 | TGFBR_stimulus&!DNA_damage&!ERK&p38&!GADD45&RAS | TGFBR_stimulus&!DNA_damage&!ERK&p38&GADD45 | TGFBR_stimulus&!DNA_damage&ERK&!GADD45&RAS | TGFBR_stimulus&!DNA_damage&ERK&GADD45 | TGFBR_stimulus&DNA_damage
MDM2,           !DNA_damage&!ERK&!p38&PI3K | DNA_damage&!ERK&!p38&!PI3K&!MDM2 | DNA_damage&!ERK&!p38&PI3K | DNA_damage&ERK&!p38&!MDM2
PI3K,           !GRB2&PI3K | GRB2
PLCG,           !EGFR_stimulus&!FGFR3_stimulus&ERK&!GRB2&!PLCG | !EGFR_stimulus&FGFR3_stimulus&!GRB2&!PLCG | EGFR_stimulus&!GRB2&!PLCG
Proliferation,  !DNA_damage&ERK&!p38&PI3K | !DNA_damage&ERK&p38&PI3K&MDM2 | DNA_damage&ERK&!p38&PI3K&MDM2
RAS,            !ERK&!GRB2&PLCG | !ERK&GRB2 | ERK&PLCG
TGFBR_stimulus, TGFBR_stimulus
p38,            !TGFBR_stimulus&!DNA_damage&!ERK&!p38&!GADD45&RAS | !TGFBR_stimulus&!DNA_damage&!ERK&!p38&GADD45 | !TGFBR_stimulus&!DNA_damage&!ERK&p38&GADD45&RAS | !TGFBR_stimulus&!DNA_damage&ERK&GADD45&RAS | !TGFBR_stimulus&DNA_damage&!ERK&!p38 | !TGFBR_stimulus&DNA_damage&!ERK&p38&!GADD45&RAS | !TGFBR_stimulus&DNA_damage&!ERK&p38&GADD45 | !TGFBR_stimulus&DNA_damage&ERK&!GADD45&RAS | !TGFBR_stimulus&DNA_damage&ERK&GADD45 | TGFBR_stimulus&!DNA_damage&!ERK&!p38 | TGFBR_stimulus&!DNA_damage&!ERK&p38&!GADD45&RAS | TGFBR_stimulus&!DNA_damage&!ERK&p38&GADD45 | TGFBR_stimulus&!DNA_damage&ERK&!GADD45&RAS | TGFBR_stimulus&!DNA_damage&ERK&GADD45 | TGFBR_stimulus&DNA_damage
";

    #[test]
    fn read_bnet() {
        let network = BooleanNetwork::try_from_bnet(BNET_MODEL).unwrap();
        assert_eq!(16, network.num_vars());
        for v in network.variables() {
            assert!(network.get_update_function(v).is_some());
        }
    }
}
