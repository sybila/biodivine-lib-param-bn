use crate::bdd_params::{BddParameterEncoder, BddParams};
use crate::{BinaryOp, FnUpdate};
use biodivine_lib_bdd::Bdd;
use biodivine_lib_std::IdState;

impl FnUpdate {
    /// Evaluate this `FnUpdate` into symbolic `BddParams` that represent all parameter
    /// valuations for which this function evaluates to `true`.
    pub fn symbolic_eval_true(&self, state: IdState, encoder: &BddParameterEncoder) -> BddParams {
        return BddParams(self._symbolic_eval(state, encoder));
    }

    /// Evaluate this `FnUpdate` into symbolic `BddParams` that represent all parameter
    /// valuations for which this function evaluates to `false`.
    pub fn symbolic_eval_false(&self, state: IdState, encoder: &BddParameterEncoder) -> BddParams {
        return BddParams(self._symbolic_eval(state, encoder).not());
    }

    pub(super) fn _symbolic_eval(&self, state: IdState, encoder: &BddParameterEncoder) -> Bdd {
        return match self {
            FnUpdate::Const(value) => {
                if *value {
                    encoder.bdd_variables.mk_true()
                } else {
                    encoder.bdd_variables.mk_false()
                }
            }
            FnUpdate::Not(inner) => inner._symbolic_eval(state, encoder).not(),
            FnUpdate::Var(id) => {
                if state.get_bit(id.0) {
                    encoder.bdd_variables.mk_true()
                } else {
                    encoder.bdd_variables.mk_false()
                }
            }
            FnUpdate::Param(id, args) => {
                let var = encoder.get_explicit(state, *id, args);
                encoder.bdd_variables.mk_var(var)
            }
            FnUpdate::Binary(op, l, r) => {
                let l = l._symbolic_eval(state, encoder);
                let r = r._symbolic_eval(state, encoder);
                match op {
                    BinaryOp::And => l.and(&r),
                    BinaryOp::Or => l.or(&r),
                    BinaryOp::Xor => l.xor(&r),
                    BinaryOp::Imp => l.imp(&r),
                    BinaryOp::Iff => l.iff(&r),
                }
            }
        };
    }
}
