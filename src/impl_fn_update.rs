use crate::FnUpdate::*;
use crate::{FnUpdate, VariableId};
use std::collections::HashSet;

impl FnUpdate {
    /// Return a sorted vector of all variables that are used as inputs in this function.
    pub fn arguments(&self) -> Vec<VariableId> {
        let mut set = HashSet::new();
        self.args(&mut set);
        let mut result: Vec<VariableId> = set.into_iter().collect();
        result.sort();
        return result;
    }

    fn args(&self, result: &mut HashSet<VariableId>) {
        match self {
            Const(_) => {}
            Var(id) => {
                result.insert(*id);
            }
            Param(_, _) => {}
            Not(inner) => inner.args(result),
            Binary(_, l, r) => {
                l.args(result);
                r.args(result);
            }
        };
    }
}
