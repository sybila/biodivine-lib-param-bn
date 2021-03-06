use crate::{BinaryOp, BooleanNetwork, FnUpdate, VariableId};

impl BooleanNetwork {
    /// Produce a `.bnet` string representation of this model.
    ///
    /// Returns an error if the network is parametrised and thus cannot be converted to `.bnet`.
    pub fn to_bnet(&self) -> Result<String, String> {
        let mut model = "targets,factors\n".to_string();
        for v in self.variables() {
            let name = self.get_variable_name(v);
            if let Some(function) = self.get_update_function(v) {
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
        FnUpdate::Param(_, _) => {
            return Err("Parametrised network cannot be converted to .bnet.".to_string());
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
        let model = std::fs::read_to_string("aeon_models/hmox_pathway.aeon").unwrap();
        let network = BooleanNetwork::try_from(model.as_str()).unwrap();
        let network_after =
            BooleanNetwork::try_from_bnet(network.to_bnet().unwrap().as_str()).unwrap();

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
}
