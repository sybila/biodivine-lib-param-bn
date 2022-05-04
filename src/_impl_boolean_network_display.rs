use crate::BooleanNetwork;
use std::fmt::{Display, Error, Formatter};

impl Display for BooleanNetwork {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), Error> {
        write!(f, "{}", self.graph)?;
        for var in self.variables() {
            // print all update functions
            if let Some(fun) = self.get_update_function(var) {
                writeln!(f, "${}: {}", self[var], fun.to_string(self))?;
            }
        }
        Ok(())
    }
}
