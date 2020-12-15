use crate::Parameter;

impl Parameter {
    pub fn get_name(&self) -> &String {
        &self.name
    }

    pub fn get_arity(&self) -> u32 {
        self.arity
    }
}
