// Here, we should implement a new way for working with symbolic encodings which does not depend
// on semi-symbolic constraints.

#[cfg(test)]
mod tests {
    use crate::bdd_params::{build_static_constraints, BddParameterEncoder};
    use crate::BooleanNetwork;
    use std::convert::TryFrom;

    #[test]
    fn hmox_pathway() {
        let model = std::fs::read_to_string("aeon_models/hmox_pathway.aeon").unwrap();
        let network = BooleanNetwork::try_from(model.as_str()).unwrap();
        println!("Variables: {}", network.graph.num_vars());
        let encoder = BddParameterEncoder::new(&network);
        let constraints = build_static_constraints(&network, &encoder);
        assert!(!constraints.is_false());
    }
}
