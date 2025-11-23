use crate::{BinaryOp, BooleanNetwork, FnUpdate};

impl BooleanNetwork {
    /// Produce a `booleannet` string representation of this model.
    pub fn to_booleannet(&self) -> Result<String, String> {
        let mut result = String::from("# booleannet export\n");
        for var in self.variables() {
            if let Some(function) = self.get_update_function(var) {
                let rule = fn_update_to_booleannet_string(function, self)?;
                result.push_str(&format!("1: {}* = {}\n", self.get_variable_name(var), rule));
            } else if !self.regulators(var).is_empty() {
                return Err(format!(
                    "Variable `{}` has no update function. Parametrised networks \
cannot be exported to booleannet.",
                    self.get_variable_name(var)
                ));
            }
        }
        Ok(result)
    }
}

fn fn_update_to_booleannet_string(
    function: &FnUpdate,
    network: &BooleanNetwork,
) -> Result<String, String> {
    Ok(match function {
        FnUpdate::Var(id) => network.get_variable_name(*id).clone(),
        FnUpdate::Const(value) => {
            if *value {
                "True".to_string()
            } else {
                "False".to_string()
            }
        }
        FnUpdate::Param(id, args) => {
            if args.is_empty() {
                network.get_parameter(*id).get_name().to_string()
            } else {
                return Err(
                    "Networks with free (parameterised) functions cannot be exported to booleannet."
                        .to_string(),
                );
            }
        }
        FnUpdate::Not(inner) => {
            format!("(not {})", fn_update_to_booleannet_string(inner, network)?)
        }
        FnUpdate::Binary(op, left, right) => {
            let left = fn_update_to_booleannet_string(left, network)?;
            let right = fn_update_to_booleannet_string(right, network)?;
            match *op {
                BinaryOp::And => format!("({} and {})", left, right),
                BinaryOp::Or => format!("({} or {})", left, right),
                BinaryOp::Imp => format!("((not {}) or {})", left, right),
                BinaryOp::Iff => format!(
                    "((({} and {}) or ((not {}) and (not {}))))",
                    left, right, left, right
                ),
                BinaryOp::Xor => format!(
                    "((({} and (not {})) or ((not {}) and {})))",
                    left, right, left, right
                ),
            }
        }
    })
}

#[cfg(test)]
mod tests {
    use crate::BooleanNetwork;
    use std::convert::TryFrom;

    #[test]
    fn booleannet_round_trip() {
        let model = std::fs::read_to_string("aeon_models/g2a_instantiated.aeon").unwrap();
        let network = BooleanNetwork::try_from(model.as_str()).unwrap();

        let exported = network.to_booleannet().unwrap();
        let network_after =
            BooleanNetwork::try_from_booleannet(exported.as_str()).expect("round trip");

        assert_eq!(network.graph.num_vars(), network_after.graph.num_vars());
        for v in network.graph.variables() {
            assert_eq!(
                network.graph.get_variable(v),
                network_after.graph.get_variable(v)
            );
            let source_regs = network.graph.regulators(v);
            let roundtrip_regs = network_after.graph.regulators(v);
            if source_regs != roundtrip_regs {
                let var_name = network.graph.get_variable_name(v);
                let before: Vec<String> = source_regs
                    .iter()
                    .map(|id| network.graph.get_variable_name(*id).clone())
                    .collect();
                let after: Vec<String> = roundtrip_regs
                    .iter()
                    .map(|id| network_after.graph.get_variable_name(*id).clone())
                    .collect();
                panic!(
                    "Regulators differ for `{}`. Expected {:?} but found {:?}.",
                    var_name, before, after
                );
            }
            assert_eq!(
                network.get_update_function(v),
                network_after.get_update_function(v)
            );
        }
    }

    #[test]
    fn booleannet_export_invalid() {
        let bn = BooleanNetwork::try_from("A -> B \n B -> A").unwrap();
        assert!(bn.to_booleannet().is_err());
    }
}
