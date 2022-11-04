use crate::{RegulatoryGraph, VariableId};
use std::fmt::{Display, Error, Formatter};

impl From<VariableId> for usize {
    fn from(value: VariableId) -> Self {
        value.0
    }
}

impl VariableId {
    /// Try to construct a `VariableId` from the given `usize` value. The id must be valid
    /// inside the context of the specified `RegulatoryGraph`, otherwise `None` is returned.
    pub fn try_from_usize(context: &RegulatoryGraph, value: usize) -> Option<VariableId> {
        if value < context.variables.len() {
            Some(VariableId(value))
        } else {
            None
        }
    }

    /// Create a `VariableId` from a constant value without any sanity checks.
    pub fn from_index(value: usize) -> VariableId {
        VariableId(value)
    }

    /// Convert the `VariableId` to the corresponding numeric identifier.
    pub fn to_index(self) -> usize {
        self.into()
    }
}

impl Display for VariableId {
    fn fmt(&self, f: &mut Formatter) -> Result<(), Error> {
        write!(f, "BnVariable({})", self.0)
    }
}

#[cfg(test)]
mod tests {
    use crate::{RegulatoryGraph, VariableId};
    use std::convert::TryFrom;

    #[test]
    fn variable_id_conversion() {
        let rg = RegulatoryGraph::try_from("a -> b").unwrap();
        let a = rg.find_variable("a").unwrap();
        assert_eq!(Some(a), VariableId::try_from_usize(&rg, a.into()));
        assert_eq!(None, VariableId::try_from_usize(&rg, 10));
    }
}
