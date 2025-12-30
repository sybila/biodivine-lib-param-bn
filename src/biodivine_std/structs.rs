use crate::biodivine_std::traits::State;
use std::collections::HashMap;
/// Basic structs which are carried over from lib-biodivine_std for now.
///
/// In the future, these will be replaced by a more stable variants.
use std::fmt::{Display, Error, Formatter};
use std::hash::Hash;

/// Build a mapping from elements of the given vector to their respective indices.
///
/// **Warning:** Duplicates are not detected or handled in any way, they are just overwritten.
pub fn build_index_map<T, F, R>(keys: &[T], transform_index: F) -> HashMap<T, R>
where
    F: Fn(&T, usize) -> R,
    T: Clone + Hash + PartialEq + Eq,
{
    let mut result = HashMap::new();
    for (i, item) in keys.iter().enumerate() {
        result.insert(item.clone(), transform_index(item, i));
    }
    result
}

/// A very basic implementation of a `State` which simply stores a single `usize` index.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct IdState(usize);

/// A simple `IdState` iterator used for graphs where the states are consecutive integers.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct IdStateRange {
    next: usize,
    remaining: usize,
}

impl State for IdState {}

impl From<usize> for IdState {
    fn from(val: usize) -> Self {
        IdState(val)
    }
}

impl From<IdState> for usize {
    fn from(state: IdState) -> Self {
        state.0
    }
}

impl Display for IdState {
    fn fmt(&self, f: &mut Formatter) -> Result<(), Error> {
        write!(f, "State({})", self.0)
    }
}

impl IdState {
    /// Test if the bit at the given position is set or not.
    pub fn get_bit(self, bit: usize) -> bool {
        (self.0 >> bit) & 1 == 1
    }

    /// Flip the bit at the given position.
    pub fn flip_bit(self, bit: usize) -> IdState {
        IdState(self.0 ^ (1 << bit))
    }
}

impl IdStateRange {
    pub fn new(state_count: usize) -> IdStateRange {
        IdStateRange {
            next: 0,
            remaining: state_count,
        }
    }
}

impl Iterator for IdStateRange {
    type Item = IdState;

    fn next(&mut self) -> Option<Self::Item> {
        if self.remaining == 0 {
            None
        } else {
            let result = self.next;
            self.remaining -= 1;
            self.next += 1;
            Some(IdState::from(result))
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::biodivine_std::structs::{IdState, IdStateRange};

    #[test]
    fn id_state_test() {
        let state = IdState::from(0b10110);
        assert!(!state.get_bit(0));
        assert!(state.get_bit(1));
        assert!(state.get_bit(2));
        assert!(!state.get_bit(3));
        assert!(state.get_bit(4));
        let flipped = state.flip_bit(3);
        assert_eq!(0b11110_usize, flipped.into());
    }

    #[test]
    fn test_state_range_iterator() {
        let mut iter = IdStateRange::new(6);
        assert_eq!(Some(IdState::from(0)), iter.next());
        assert_eq!(Some(IdState::from(1)), iter.next());
        assert_eq!(Some(IdState::from(2)), iter.next());
        assert_eq!(Some(IdState::from(3)), iter.next());
        assert_eq!(Some(IdState::from(4)), iter.next());
        assert_eq!(Some(IdState::from(5)), iter.next());
        assert_eq!(None, iter.next());
        assert_eq!(None, iter.next());
    }
}
