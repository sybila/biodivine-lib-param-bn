use crate::parser::FnUpdateTemp;
use crate::parser::FnUpdateTemp::*;
use std::fmt::{Display, Error, Formatter};

impl Display for FnUpdateTemp {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), Error> {
        match self {
            Const(value) => write!(f, "{}", value)?,
            Var(name) => write!(f, "{}", name)?,
            Not(inner) => write!(f, "!{}", inner)?,
            Binary(op, l, r) => write!(f, "({} {} {})", l, op, r)?,
            Param(name, args) => {
                write!(f, "{}", name)?;
                if args.len() > 0 {
                    write!(f, "({}", args[0])?;
                    for i in 1..args.len() {
                        write!(f, ", {}", args[i])?;
                    }
                    write!(f, ")")?;
                }
            }
        }
        return Ok(());
    }
}
