use crate::trap_spaces::ExtendedBoolean::Any;
use crate::trap_spaces::{ExtendedBoolean, OptionalExtendedBoolean, PartialSpace, Space};
use crate::{BooleanNetwork, VariableId};
use std::cmp::Ordering;
use std::fmt::{Display, Formatter};
use std::ops::{Index, IndexMut};
use ExtendedBoolean::{One, Zero};

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
        Space(vec![Any; network.num_vars()])
    }

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

    pub fn count_any(&self) -> usize {
        self.0
            .iter()
            .filter(|it| **it == ExtendedBoolean::Any)
            .count()
    }

    pub fn to_partial_space(self) -> PartialSpace {
        PartialSpace(
            self.0
                .into_iter()
                .map(|it| match it {
                    One => OptionalExtendedBoolean::One,
                    Zero => OptionalExtendedBoolean::Zero,
                    ExtendedBoolean::Any => OptionalExtendedBoolean::Any,
                })
                .collect(),
        )
    }

    /// Check if this `Space` is a **trap** space within the given `BooleanNetwork`.
    ///
    /// A trap space is a `Space` in which every asynchronous transition from every state leads
    /// to a state within the same `Space`.
    pub fn is_trap_space(&self, network: &BooleanNetwork) -> bool {
        for var in network.variables() {
            let expected_value = self[var];
            if expected_value.is_fixed() {
                if let Some(update) = network.get_update_function(var) {
                    let actual_value = update.eval_in_space(self);
                    if expected_value != actual_value {
                        // Since expected value is fixed, either actual value is a different
                        // constant, or `Any`, in which case this is still not a trap space.
                        return false;
                    }
                } else {
                    // If the function is unknown, the whole thing is a giant parameter that we
                    // know nothing about, hence the value cannot be fixed.
                    return false;
                }
            } else {
                // If the expected value is `Any`, then there can be no transitions escaping
                // using this variable, so we can just skip it.
            }
        }

        true
    }

    /*
        /// Check if this `Space` has a **trap conflict variable** (within the given `BooleanNetwork`).
        ///
        /// A "conflict variable" is a specific BN variable that can always be updated, and where the
        /// update always leads outside of the given `Space`. In other words, from every state, one
        /// can escape this `Space` in a single step using this variable.
        ///
        /// Note that a space with a conflict variable cannot be a trap space. However, a space that
        /// is not a trap space may not have a single conflict variable, even if every state can
        /// escape this `Space` in one step.
        pub fn has_trap_conflict_variable(&self, network: &BooleanNetwork) -> Option<VariableId> {
            for var in network.variables() {
                let expected_value = self[var];
                if expected_value.is_fixed() {
                    if let Some(update) = network.get_update_function(var) {
                        let actual_value = update.eval_in_space(self);
                        if actual_value.is_fixed() && actual_value != expected_value {
                            return Some(var);
                        } else {
                            // If actual value is "any", then the space is not a trap space, but
                            // the variable is not transient either.
                        }
                    } else {
                        // If the function is unknown, then this is also not a trap space, but
                        // it does not guarantee that the variable is transient.
                    }
                }
            }
            None
        }
    */
}
