use crate::ExtendedBoolean::{Any, One, Zero};
use crate::{BooleanNetwork, ExtendedBoolean, Space, VariableId};
use std::cmp::Ordering;
use std::fmt::{Display, Formatter};
use std::ops::{Index, IndexMut};

impl Index<VariableId> for Space {
    type Output = ExtendedBoolean;

    fn index(&self, index: VariableId) -> &Self::Output {
        &self.0[index.to_index()]
    }
}

impl IndexMut<VariableId> for Space {
    fn index_mut(&mut self, index: VariableId) -> &mut Self::Output {
        &mut self.0[index.to_index()]
    }
}

impl Display for Space {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        for x in &self.0 {
            write!(f, "{}", x)?;
        }
        Ok(())
    }
}

impl PartialOrd for Space {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        if self == other {
            return Some(Ordering::Equal);
        }

        let mut is_sub_space = true;
        let mut is_super_space = true;
        for (x, y) in self.0.iter().zip(other.0.iter()) {
            is_sub_space = is_sub_space && x <= y;
            is_super_space = is_super_space && x >= y;
        }
        assert!(!(is_super_space && is_sub_space));
        if is_sub_space {
            Some(Ordering::Less)
        } else if is_super_space {
            Some(Ordering::Greater)
        } else {
            None
        }
    }
}

impl Space {
    /// Create a new space tracking the variables of the given network, where all values are
    /// initially assigned as `Any`.
    pub fn new(network: &BooleanNetwork) -> Space {
        Self::new_raw(network.num_vars())
    }

    pub fn new_raw(num_vars: usize) -> Space {
        Space(vec![Any; num_vars])
    }

    /// Convert a list of values (such as used by `SymbolicAsyncGraph`) into a proper "space" object.
    pub fn from_values(bn: &BooleanNetwork, values: Vec<(VariableId, bool)>) -> Space {
        let mut result = Self::new(bn);
        for (k, v) in values {
            result[k] = ExtendedBoolean::from(v);
        }
        result
    }

    /// Convert a space into a list of values compatible with the normal `SymbolicAsyncGraph`.
    pub fn to_values(&self) -> Vec<(VariableId, bool)> {
        let mut result = Vec::new();
        for (k, v) in self.0.iter().enumerate() {
            if let Some(v) = v.try_as_bool() {
                result.push((VariableId::from_index(k), v))
            }
        }
        result
    }

    /// Try to intersect two spaces. If the result is empty, returns `None`.
    pub fn intersect(&self, other: &Space) -> Option<Space> {
        let mut result = self.clone();
        for i in 0..self.0.len() {
            match (self.0[i], other.0[i]) {
                (One, Zero) | (Zero, One) => {
                    return None;
                }
                (One, Any) | (Any, One) => {
                    result.0[i] = One;
                }
                (Zero, Any) | (Any, Zero) => {
                    result.0[i] = Zero;
                }
                (Zero, Zero) | (One, One) | (Any, Any) => {
                    // Do nothing.
                }
            }
        }
        Some(result)
    }

    /// Count the number of `*` in this space.
    pub fn count_any(&self) -> usize {
        self.0.iter().filter(|it| **it == Any).count()
    }

    /// Count the number of `0` and `1` in this space.
    pub fn count_fixed(&self) -> usize {
        self.0.iter().filter(|it| **it != Any).count()
    }
}
