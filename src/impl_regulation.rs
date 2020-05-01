use crate::{Regulation, Monotonicity, VariableId};

impl Regulation {

    pub fn is_observable(&self) -> bool {
        return self.observable;
    }

    pub fn get_monotonicity(&self) -> Option<Monotonicity> {
        return self.monotonicity;
    }

    pub fn get_regulator(&self) -> VariableId {
        return self.regulator;
    }

    pub fn get_target(&self) -> VariableId {
        return self.target;
    }

}