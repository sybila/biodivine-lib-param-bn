use crate::Parameter;
use std::fmt::{Display, Formatter};

impl Parameter {
    /// **(internal)** A create-visible utility constructor.
    pub(crate) fn new(name: &str, arity: u32) -> Parameter {
        Parameter {
            name: name.to_string(),
            arity,
        }
    }

    /// Obtain reference to the parameter name.
    pub fn get_name(&self) -> &String {
        &self.name
    }

    /// Read parameter arity (number of arguments).
    pub fn get_arity(&self) -> u32 {
        self.arity
    }
}

impl Display for Parameter {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.name)
    }
}

#[cfg(test)]
mod tests {
    use crate::Parameter;

    #[test]
    fn basic_parameter_struct_test() {
        let p = Parameter::new("test", 13);
        assert_eq!(13, p.get_arity());
        assert_eq!("test", p.get_name());
        assert_eq!("test", p.to_string().as_str());
    }
}
