//!Adds support for SBML-qual import and export to `BooleanNetwork`.

use std::collections::HashMap;

/// Contains code for parsing SBML models using xml-tree library. It is not 100% SBML-qual
/// compliant, but should be good enough for now. Also most code is ready for possible extension
/// to multi-valued models in the future.
pub mod import;

/// A very crude SBML export module. It basically just dumps `BooleanNetwork` into valid XML,
/// but there are some things that could be better checked.
pub mod export;

/// A layout type for transferring information about node position from SBML files.
pub type Layout = HashMap<String, (f64, f64)>;
