use crate::{BooleanNetwork, FnUpdate};
use std::fmt::{Display, Error, Formatter};

impl Display for BooleanNetwork {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), Error> {
        write!(f, "{}", self.graph)?;
        for var in self.variables() {
            // print all update functions
            if let Some(fun) = self.get_update_function(var) {
                writeln!(f, "${}: {}", self[var], Fun(self, fun))?;
            }
        }
        Ok(())
    }
}

struct Fun<'a>(&'a BooleanNetwork, &'a FnUpdate);

impl Display for Fun<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), Error> {
        let Fun(bn, fun) = self;
        match fun {
            FnUpdate::Const(value) => write!(f, "{}", value)?,
            FnUpdate::Binary(op, l, r) => write!(f, "({} {} {})", Fun(bn, l), op, Fun(bn, r))?,
            FnUpdate::Not(inner) => write!(f, "!{}", Fun(bn, inner))?,
            FnUpdate::Var(id) => write!(f, "{}", bn[*id])?,
            FnUpdate::Param(id, args) => {
                write!(f, "{}", bn[*id].get_name())?;
                if !args.is_empty() {
                    write!(f, "({}", bn[args[0]])?;
                    for i in 1..args.len() {
                        write!(f, ", {}", bn[args[i]])?;
                    }
                    write!(f, ")")?;
                }
            }
        };
        Ok(())
    }
}
