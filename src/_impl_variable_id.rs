use crate::VariableId;
use std::fmt::{Display, Error, Formatter};

impl From<usize> for VariableId {
    fn from(val: usize) -> Self {
        VariableId(val)
    }
}

impl From<VariableId> for usize {
    fn from(value: VariableId) -> Self {
        value.0
    }
}

impl Display for VariableId {
    fn fmt(&self, f: &mut Formatter) -> Result<(), Error> {
        write!(f, "BnVariable({})", self.0)
    }
}
