use crate::VariableId;
use std::fmt::{Display, Error, Formatter};

impl From<usize> for VariableId {
    fn from(val: usize) -> Self {
        return VariableId(val);
    }
}

impl Into<usize> for VariableId {
    fn into(self) -> usize {
        return self.0;
    }
}

impl Display for VariableId {
    fn fmt(&self, f: &mut Formatter) -> Result<(), Error> {
        return write!(f, "BnVariable({})", self.0);
    }
}
