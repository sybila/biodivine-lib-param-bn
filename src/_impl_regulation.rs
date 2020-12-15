use crate::{Monotonicity, Regulation, VariableId};

impl Regulation {
    pub fn is_observable(&self) -> bool {
        self.observable
    }

    pub fn get_monotonicity(&self) -> Option<Monotonicity> {
        self.monotonicity
    }

    pub fn get_regulator(&self) -> VariableId {
        self.regulator
    }

    pub fn get_target(&self) -> VariableId {
        self.target
    }
}
