use crate::BooleanNetwork;
use crate::bdd_params::{BddParams, BddParameterEncoder};

impl BooleanNetwork {

    pub fn make_witness(&self, params: &BddParams, encoder: &BddParameterEncoder) -> BooleanNetwork {
        let valuation = params.as_bdd().sat_witness();
        if valuation.is_none() {
            panic!("Cannot create witness for empty parameter set.");
        }
        let valuation = valuation.unwrap();
        
    }

}