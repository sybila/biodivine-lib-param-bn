use crate::trap_spaces::ExtendedBoolean;
use std::cmp::Ordering;
use std::fmt::{Debug, Display, Formatter};
use ExtendedBoolean::{Any, One, Zero};

impl Debug for ExtendedBoolean {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Zero => write!(f, "0"),
            One => write!(f, "1"),
            Any => write!(f, "*"),
        }
    }
}

impl Display for ExtendedBoolean {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", self)
    }
}

/// Implements a "set-like" ordering for extended Booleans. "Any" is greater than constant values
/// (since it covers both values), while constant values are incomparable between each other.
impl PartialOrd for ExtendedBoolean {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        match (self, other) {
            (Zero, Zero) | (One, One) | (Any, Any) => Some(Ordering::Equal),
            (Zero, Any) | (One, Any) => Some(Ordering::Less),
            (Any, One) | (Any, Zero) => Some(Ordering::Greater),
            (One, Zero) | (Zero, One) => None,
        }
    }
}

impl ExtendedBoolean {
    pub fn is_any(&self) -> bool {
        *self == Any
    }

    pub fn is_fixed(&self) -> bool {
        *self != Any
    }
}

/// Logical operations on extended booleans.
impl ExtendedBoolean {
    pub fn not(self) -> Self {
        match self {
            Zero => One,
            One => Zero,
            Any => Any,
        }
    }

    pub fn or(self, other: Self) -> Self {
        match (self, other) {
            (One, _) | (_, One) => One,
            (Zero, Zero) => Zero,
            (Any, Zero) | (Zero, Any) | (Any, Any) => Any,
        }
    }

    pub fn and(self, other: Self) -> Self {
        match (self, other) {
            (Zero, _) | (_, Zero) => Zero,
            (One, One) => One,
            (Any, One) | (One, Any) | (Any, Any) => Any,
        }
    }

    pub fn implies(self, other: Self) -> Self {
        match (self, other) {
            (Zero, _) | (_, One) => One,
            (One, Zero) => Zero,
            (Any, Zero) | (One, Any) | (Any, Any) => Any,
        }
    }

    pub fn iff(self, other: Self) -> Self {
        match (self, other) {
            (One, One) | (Zero, Zero) => One,
            (One, Zero) | (Zero, One) => Zero,
            (Any, _) | (_, Any) => Any,
        }
    }

    pub fn xor(self, other: Self) -> Self {
        match (self, other) {
            (One, Zero) | (Zero, One) => One,
            (One, One) | (Zero, Zero) => Zero,
            (Any, _) | (_, Any) => Any,
        }
    }
}
