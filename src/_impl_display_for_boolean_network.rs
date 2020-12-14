use crate::{BooleanNetwork, FnUpdate};
use std::fmt::{Display, Error, Formatter};

impl Display for BooleanNetwork {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), Error> {
        write!(f, "{}", self.graph)?;
        for var in self.variables() {
            // print all update functions
            if let Some(fun) = self.get_update_function(var) {
                write!(f, "${}: {}\n", self[var], Fun(self, fun))?;
            }
        }
        return Ok(());
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
                if args.len() > 0 {
                    write!(f, "({}", bn[args[0]])?;
                    for i in 1..args.len() {
                        write!(f, ", {}", bn[args[i]])?;
                    }
                    write!(f, ")")?;
                }
            }
        };
        return Ok(());
    }
}
