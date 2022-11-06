use crate::trap_spaces::{ExtendedBoolean, OptionalExtendedBoolean, PartialSpace, Space};
use crate::{BinaryOp, FnUpdate};

impl FnUpdate {
    /// Perform partial evaluation of this function using extended Boolean values in the given
    /// `Space`.
    pub fn eval_in_space(&self, space: &Space) -> ExtendedBoolean {
        match self {
            FnUpdate::Const(value) => {
                if *value {
                    ExtendedBoolean::One
                } else {
                    ExtendedBoolean::Zero
                }
            }
            FnUpdate::Var(var) => space[*var],
            FnUpdate::Param(_, _) => {
                // We assume that a parameter can evaluate to anything.
                ExtendedBoolean::Any
            }
            FnUpdate::Not(inner) => inner.eval_in_space(space).negate(),
            FnUpdate::Binary(op, left, right) => {
                let left = left.eval_in_space(space);
                let right = right.eval_in_space(space);
                match op {
                    BinaryOp::Or => left.or(right),
                    BinaryOp::And => left.and(right),
                    BinaryOp::Imp => left.implies(right),
                    BinaryOp::Iff => left.iff(right),
                    BinaryOp::Xor => left.xor(right),
                }
            }
        }
    }

    /// Perform partial evaluation of this function using the optional extended Boolean vlaues
    /// in the given `PartialSpace`.
    pub fn eval_in_partial_space(&self, space: &PartialSpace) -> OptionalExtendedBoolean {
        match self {
            FnUpdate::Const(value) => {
                if *value {
                    OptionalExtendedBoolean::One
                } else {
                    OptionalExtendedBoolean::Zero
                }
            }
            FnUpdate::Var(var) => space[*var],
            FnUpdate::Param(_, _) => OptionalExtendedBoolean::Any,
            FnUpdate::Not(inner) => inner.eval_in_partial_space(space).negate(),
            FnUpdate::Binary(op, left, right) => {
                let left = left.eval_in_partial_space(space);
                let right = right.eval_in_partial_space(space);
                match op {
                    BinaryOp::Or => left.or(right),
                    BinaryOp::And => left.and(right),
                    BinaryOp::Imp => left.implies(right),
                    BinaryOp::Iff => left.iff(right),
                    BinaryOp::Xor => left.xor(right),
                }
            }
        }
    }
}
