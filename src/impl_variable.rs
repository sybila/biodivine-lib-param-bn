use crate::Variable;
use std::fmt::{Display, Error, Formatter};

impl Display for Variable {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), Error> {
        return write!(f, "{}", self.name);
    }
}
