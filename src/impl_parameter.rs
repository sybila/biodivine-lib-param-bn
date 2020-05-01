use crate::Parameter;

impl Parameter {
    pub fn get_name(&self) -> &String {
        return &self.name;
    }

    pub fn get_cardinality(&self) -> usize {
        return self.cardinality;
    }
}
