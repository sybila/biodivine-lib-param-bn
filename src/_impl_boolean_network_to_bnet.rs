use crate::{BinaryOp, BooleanNetwork, FnUpdate, VariableId};
use regex::Regex;

impl BooleanNetwork {
    /// Produce a `.bnet` string representation of this model.
    ///
    /// Returns an error if the network is parametrised and thus cannot be converted to `.bnet`.
    /// Also returns an error if the network contains names which are not supported in `.bnet`,
    /// such as starting with numbers.
    ///
    /// However, you can override this behaviour using `rename_if_necessary`. If this flag is set,
    /// all invalid names will be prefixed with `_`.
    pub fn to_bnet(&self, rename_if_necessary: bool) -> Result<String, String> {
        let mut network = self.clone();
        // A regex which only matches valid `.bnet` names.
        let name_re = Regex::new(r"^[a-zA-Z_][a-zA-Z0-9_]*$").unwrap();
        for var in network.variables() {
            let name = network.get_variable_name(var);
            if !name_re.is_match(name) {
                if rename_if_necessary {
                    let new_name = format!("_{}", name);
                    network.as_graph_mut().set_variable_name(var, &new_name)?;
                } else {
                    return Err(format!(
                        "Variable {} cannnot be exported to bnet. Please rename it first.",
                        name
                    ));
                }
            }
        }
        let mut model = "targets,factors\n".to_string();
        for v in network.variables() {
            let name = network.get_variable_name(v);
            if let Some(function) = network.get_update_function(v) {
                let function_string = fn_update_to_bnet_string(v, function, self)?;
                let line = format!("{}, {}\n", name, function_string);
                model.push_str(line.as_str());
            } else {
                // If there is no update function, we can skip it assuming it has no inputs (constant).
                if self.regulators(v).is_empty() {
                    continue;
                } else {
                    return Err("Parametrised network cannot be converted to .bnet.".to_string());
                }
            }
        }

        Ok(model)
    }
}

fn fn_update_to_bnet_string(
    var: VariableId,
    function: &FnUpdate,
    network: &BooleanNetwork,
) -> Result<String, String> {
    Ok(match function {
        FnUpdate::Var(id) => network.get_variable_name(*id).clone(),
        FnUpdate::Param(id, args) => {
            if args.is_empty() {
                network.get_parameter(*id).get_name().to_string()
            } else {
                return Err(
                    "Networks with free functions cannot be converted to .bnet.".to_string()
                );
            }
        }
        FnUpdate::Const(value) => {
            // .bnet does not have constants, but we can simulate a constant like this:
            let name = network.get_variable_name(var);
            if *value {
                format!("({} | !{})", name, name)
            } else {
                format!("({} & !{})", name, name)
            }
        }
        FnUpdate::Not(inner) => {
            format!("!{}", fn_update_to_bnet_string(var, inner, network)?)
        }
        FnUpdate::Binary(op, left, right) => {
            let left = fn_update_to_bnet_string(var, left, network)?;
            let right = fn_update_to_bnet_string(var, right, network)?;
            match *op {
                BinaryOp::And => format!("({} & {})", left, right),
                BinaryOp::Or => format!("({} | {})", left, right),
                BinaryOp::Imp => format!("(!{} | {})", left, right),
                BinaryOp::Iff => format!("(({} & {}) | (!{} & !{}))", left, right, left, right),
                BinaryOp::Xor => format!("(({} & !{}) | (!{} & {}))", left, right, left, right),
            }
        }
    })
}

#[cfg(test)]
mod tests {
    use crate::BooleanNetwork;
    use std::convert::TryFrom;

    #[test]
    fn test_network_to_bnet() {
        let model = std::fs::read_to_string("aeon_models/g2a_instantiated.aeon").unwrap();
        let network = BooleanNetwork::try_from(model.as_str()).unwrap();
        let network_after =
            BooleanNetwork::try_from_bnet(network.to_bnet(false).unwrap().as_str()).unwrap();

        assert_eq!(network.graph.num_vars(), network_after.graph.num_vars());
        for v in network.graph.variables() {
            assert_eq!(
                network.graph.get_variable(v),
                network_after.graph.get_variable(v)
            );
            assert_eq!(
                network.graph.regulators(v),
                network_after.graph.regulators(v)
            );
            assert_eq!(
                network.get_update_function(v),
                network_after.get_update_function(v)
            );

            for reg in network.graph.regulators(v) {
                // .bnet looses information about regulation properties.
                let r1 = network.graph.find_regulation(reg, v).unwrap();
                let r2 = network_after.graph.find_regulation(reg, v).unwrap();
                assert_eq!(r1.regulator, r2.regulator);
                assert_eq!(r1.target, r2.target);
            }
        }
    }

    #[test]
    fn test_network_to_bnet_invalid() {
        let bn = BooleanNetwork::try_from("A -> B \n B -> A").unwrap();
        // Parametrised network cannot be exported.
        assert!(bn.to_bnet(false).is_err());
        let bn = BooleanNetwork::try_from("3A -> B \n B -> 3A \n $B:3A \n $3A:B").unwrap();
        // Network with names starting with numbers cannot be exported.
        assert!(bn.to_bnet(false).is_err());
        assert!(bn.to_bnet(true).is_ok());
    }
}
