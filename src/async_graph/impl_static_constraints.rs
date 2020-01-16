//! **(internal)** This module implements functions for creating `Bdd`s corresponding
//! to the static constraints of the individual regulations of a `BooleanNetwork`.

use crate::BooleanNetwork;
use crate::bdd_params::BddParameterEncoder;
use biodivine_lib_bdd::Bdd;

pub fn build_static_constraints(bn: &BooleanNetwork, encoder: &BddParameterEncoder) -> Bdd {
    
}
