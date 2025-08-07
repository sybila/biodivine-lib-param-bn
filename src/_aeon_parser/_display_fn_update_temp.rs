use crate::_aeon_parser::FnUpdateTemp;
use crate::_aeon_parser::FnUpdateTemp::*;
use std::fmt::{Display, Error, Formatter};

impl Display for FnUpdateTemp {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), Error> {
        match self {
            Const(value) => write!(f, "{value}")?,
            Var(name) => write!(f, "{name}")?,
            Not(inner) => write!(f, "!{inner}")?,
            Binary(op, l, r) => write!(f, "({l} {op} {r})")?,
            Param(name, args) => {
                write!(f, "{name}")?;
                if !args.is_empty() {
                    write!(f, "({}", args[0])?;
                    for arg in args.iter().skip(1) {
                        write!(f, ", {arg}")?;
                    }
                    write!(f, ")")?;
                }
            }
        }
        Ok(())
    }
}
