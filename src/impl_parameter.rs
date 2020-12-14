use crate::Parameter;

impl Parameter {
    pub fn get_name(&self) -> &String {
        return &self.name;
    }

    pub fn get_arity(&self) -> u32 {
        return self.arity;
    }
}
