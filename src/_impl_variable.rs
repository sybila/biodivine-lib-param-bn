use crate::Variable;
use std::fmt::{Display, Error, Formatter};

impl Display for Variable {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), Error> {
        write!(f, "{}", self.name)
    }
}

impl Variable {
    /// Human-readable name of this variable.
    pub fn get_name(&self) -> &String {
        &self.name
    }
}

#[cfg(test)]
mod tests {
    use crate::RegulatoryGraph;

    #[test]
    fn basic_variable_test() {
        let rg = RegulatoryGraph::new(vec!["A".to_string()]);
        let a = rg.find_variable("A").unwrap();
        let a = &rg[a];
        assert_eq!("A", a.to_string().as_str());
        assert_eq!("A", a.get_name());
    }
}
