use crate::trap_spaces::OptionalExtendedBoolean;
use std::fmt::{Debug, Display, Formatter};
use OptionalExtendedBoolean::{Any, One, Unknown, Zero};

impl Debug for OptionalExtendedBoolean {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Zero => write!(f, "0"),
            One => write!(f, "1"),
            Any => write!(f, "*"),
            Unknown => write!(f, "?"),
        }
    }
}

impl Display for OptionalExtendedBoolean {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", self)
    }
}

impl OptionalExtendedBoolean {
    pub fn is_unknown(&self) -> bool {
        *self == Unknown
    }

    pub fn is_known(&self) -> bool {
        *self != Unknown
    }

    pub fn is_any(&self) -> bool {
        *self == Any
    }

    pub fn is_fixed(&self) -> bool {
        *self != Any && *self != Unknown
    }
}

/// Boolean operators on optional extended Booleans.
///
/// Note that operations like `(? <=> *) = *` are valid, because no matter what I specialize
/// `?` to, I always get `*` as a result (i.e. once one of the operands is a `*`, I can obtain
/// both results regardless of the second argument). This is not true for `and`, `or` or `imp`,
/// as there fixing `?` to a fixed value can always potentially cancel out the `*` in the second
/// argument.
impl OptionalExtendedBoolean {
    pub fn negate(self) -> Self {
        match self {
            One => Zero,
            Zero => One,
            Any => Any,
            Unknown => Unknown,
        }
    }

    pub fn or(self, other: Self) -> Self {
        match (self, other) {
            (One, _) | (_, One) => One,
            (Zero, Zero) => Zero,
            (Zero, Any) | (Any, Zero) | (Any, Any) => Any,
            (Unknown, _) | (_, Unknown) => Unknown,
        }
    }

    pub fn and(self, other: Self) -> Self {
        match (self, other) {
            (Zero, _) | (_, Zero) => Zero,
            (One, One) => One,
            (One, Any) | (Any, One) | (Any, Any) => Any,
            (Unknown, _) | (_, Unknown) => Unknown,
        }
    }

    pub fn implies(self, other: Self) -> Self {
        match (self, other) {
            (Zero, _) | (_, One) => One,
            (One, Zero) => Zero,
            (Any, Zero) | (One, Any) | (Any, Any) => Any,
            (Unknown, _) | (_, Unknown) => Unknown,
        }
    }

    pub fn iff(self, other: Self) -> Self {
        match (self, other) {
            (One, One) | (Zero, Zero) => One,
            (One, Zero) | (Zero, One) => Zero,
            (Any, _) | (_, Any) => Any,
            (Unknown, _) | (_, Unknown) => Unknown,
        }
    }

    pub fn xor(self, other: Self) -> Self {
        match (self, other) {
            (One, Zero) | (Zero, One) => One,
            (Zero, Zero) | (One, One) => Zero,
            (Any, _) | (_, Any) => Any,
            (Unknown, _) | (_, Unknown) => Unknown,
        }
    }
}
