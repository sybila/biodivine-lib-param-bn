use crate::{BooleanNetwork, ParameterId};

impl From<ParameterId> for usize {
    fn from(x: ParameterId) -> Self {
        x.0
    }
}

impl ParameterId {
    /// Try to construct a `ParameterId` from the given `usize` value. The id must be valid
    /// inside the context of the specified `BooleanNetwork`, otherwise `None` is returned.
    pub fn try_from_usize(context: &BooleanNetwork, value: usize) -> Option<ParameterId> {
        if value < context.parameters.len() {
            Some(ParameterId(value))
        } else {
            None
        }
    }

    /// Create a `ParameterId` from a constant value without any sanity checks.
    pub fn from_index(value: usize) -> ParameterId {
        ParameterId(value)
    }

    /// Convert the `ParameterId` to the corresponding numeric identifier.
    pub fn to_index(self) -> usize {
        self.into()
    }
}

#[cfg(test)]
mod tests {
    use crate::{BooleanNetwork, ParameterId};
    use std::convert::TryFrom;

    #[test]
    fn parameter_id_conversion() {
        let mut bn = BooleanNetwork::try_from("x -> y").unwrap();
        assert_eq!(None, ParameterId::try_from_usize(&bn, 0));
        let p = bn.add_parameter("test", 13).unwrap();
        assert_eq!(Some(p), ParameterId::try_from_usize(&bn, p.into()));
    }
}
