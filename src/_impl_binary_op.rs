use crate::BinaryOp;
use crate::BinaryOp::*;
use std::fmt::{Display, Error, Formatter};

impl Display for BinaryOp {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), Error> {
        let symbol = match self {
            And => "&",
            Or => "|",
            Xor => "^",
            Imp => "=>",
            Iff => "<=>",
        };
        write!(f, "{}", symbol)?;
        Ok(())
    }
}
