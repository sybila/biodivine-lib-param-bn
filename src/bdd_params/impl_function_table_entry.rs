use crate::bdd_params::FunctionTableEntry;
use crate::VariableId;

impl FunctionTableEntry<'_> {
    /// Obtain the value of the input variable. Panics if the variable is not an
    /// input of this function.
    pub fn get_value(&self, variable: VariableId) -> bool {
        for i in 0..self.regulators.len() {
            if variable == self.regulators[i] {
                // first argument is least significant bit, last argument most significant
                let mask = 1 << i;
                return (self.entry_index & mask) != 0;
            }
        }
        panic!("Variable {:?} is not an input.", variable);
    }

    /// Obtain a table entry with the value of [variable] flipped.
    pub fn flip_value(&self, variable: VariableId) -> FunctionTableEntry {
        for i in 0..self.regulators.len() {
            if variable == self.regulators[i] {
                let mask = 1 << i;
                return FunctionTableEntry {
                    entry_index: self.entry_index ^ mask,
                    regulators: self.regulators,
                    table: self.table,
                };
            }
        }
        panic!("Variable {:?} is not an input.", variable);
    }
}
