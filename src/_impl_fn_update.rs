use crate::FnUpdate::*;
use crate::{BinaryOp, BooleanNetwork, FnUpdate, ParameterId, VariableId};
use std::collections::HashSet;

/// Constructor and destructor utility methods. These mainly avoid unnecessary boxing
/// and exhaustive pattern matching when not necessary.
impl FnUpdate {
    /// Create a `true` formula.
    pub fn mk_true() -> FnUpdate {
        FnUpdate::Const(true)
    }

    /// Create a `false` formula.
    pub fn mk_false() -> FnUpdate {
        FnUpdate::Const(false)
    }

    /// Create an `x` formula where `x` is a Boolean variable.
    pub fn mk_var(id: VariableId) -> FnUpdate {
        FnUpdate::Var(id)
    }

    /// Create a `p(x_1, ..., x_k)` formula where `p` is a parameter function and `x_1` through
    /// `x_k` are its arguments.
    pub fn mk_param(id: ParameterId, args: &[VariableId]) -> FnUpdate {
        FnUpdate::Param(id, args.to_vec())
    }

    /// Create a `!phi` formula, where `phi` is an inner `FnUpdate`.
    pub fn mk_not(inner: FnUpdate) -> FnUpdate {
        FnUpdate::Not(Box::new(inner))
    }

    /// Create a `phi 'op' psi` where `phi` and `psi` are arguments of `op` operator.
    pub fn mk_binary(op: BinaryOp, left: FnUpdate, right: FnUpdate) -> FnUpdate {
        FnUpdate::Binary(op, Box::new(left), Box::new(right))
    }

    /// Negate this function.
    pub fn negation(self) -> FnUpdate {
        FnUpdate::mk_not(self)
    }

    /// Create a conjunction.
    pub fn and(self, other: FnUpdate) -> FnUpdate {
        FnUpdate::mk_binary(BinaryOp::And, self, other)
    }

    /// Create a disjunction.
    pub fn or(self, other: FnUpdate) -> FnUpdate {
        FnUpdate::mk_binary(BinaryOp::Or, self, other)
    }

    /// Create an exclusive or.
    pub fn xor(self, other: FnUpdate) -> FnUpdate {
        FnUpdate::mk_binary(BinaryOp::Xor, self, other)
    }

    /// Create an implication.
    pub fn implies(self, other: FnUpdate) -> FnUpdate {
        FnUpdate::mk_binary(BinaryOp::Imp, self, other)
    }

    /// Create an equivalence.
    pub fn iff(self, other: FnUpdate) -> FnUpdate {
        FnUpdate::mk_binary(BinaryOp::Iff, self, other)
    }

    /// If `Const`, return the value, otherwise return `None`.
    pub fn as_const(&self) -> Option<bool> {
        match self {
            FnUpdate::Const(value) => Some(*value),
            _ => None,
        }
    }

    /// If `Var`, return the id, otherwise return `None`.
    pub fn as_var(&self) -> Option<VariableId> {
        match self {
            FnUpdate::Var(value) => Some(*value),
            _ => None,
        }
    }

    /// If `Param`, return the id and args, otherwise return `None`.
    pub fn as_param(&self) -> Option<(ParameterId, &[VariableId])> {
        match self {
            FnUpdate::Param(id, args) => Some((*id, args)),
            _ => None,
        }
    }

    /// If `Not`, return the inner function, otherwise return `None`.
    pub fn as_not(&self) -> Option<&FnUpdate> {
        match self {
            FnUpdate::Not(inner) => Some(inner),
            _ => None,
        }
    }

    /// If `Binary`, return the operator and left/right formulas, otherwise return `None`.
    pub fn as_binary(&self) -> Option<(&FnUpdate, BinaryOp, &FnUpdate)> {
        match self {
            FnUpdate::Binary(op, l, r) => Some((l, *op, r)),
            _ => None,
        }
    }
}

/// Other utility methods.
impl FnUpdate {
    /// Return a sorted vector of all variables that are actually used as inputs in this function.
    pub fn collect_arguments(&self) -> Vec<VariableId> {
        fn r_arguments(function: &FnUpdate, args: &mut HashSet<VariableId>) {
            match function {
                Const(_) => (),
                Var(id) => {
                    args.insert(*id);
                }
                Param(_, p_args) => {
                    for id in p_args {
                        args.insert(*id);
                    }
                }
                Not(inner) => r_arguments(inner, args),
                Binary(_, l, r) => {
                    r_arguments(l, args);
                    r_arguments(r, args);
                }
            };
        }
        let mut args = HashSet::new();
        r_arguments(self, &mut args);
        let mut result: Vec<VariableId> = args.into_iter().collect();
        result.sort();
        result
    }

    /// Return a sorted vector of all parameters (i.e. uninterpreted functions) that are used
    /// in this update function.
    pub fn collect_parameters(&self) -> Vec<ParameterId> {
        fn r_parameters(function: &FnUpdate, params: &mut HashSet<ParameterId>) {
            match function {
                Const(_) => (),
                Var(_) => (),
                Param(id, _) => {
                    params.insert(*id);
                }
                Not(inner) => r_parameters(inner, params),
                Binary(_, l, r) => {
                    r_parameters(l, params);
                    r_parameters(r, params);
                }
            };
        }
        let mut params = HashSet::new();
        r_parameters(self, &mut params);
        let mut result: Vec<ParameterId> = params.into_iter().collect();
        result.sort();
        result
    }

    /// Convert this update function to a string, taking names from the provided `BooleanNetwork`.
    pub fn to_string(&self, context: &BooleanNetwork) -> String {
        match self {
            FnUpdate::Const(value) => value.to_string(),
            FnUpdate::Var(id) => context.get_variable_name(*id).to_string(),
            FnUpdate::Not(inner) => format!("!{}", inner.to_string(context)),
            FnUpdate::Binary(op, l, r) => {
                format!("({} {} {})", l.to_string(context), op, r.to_string(context))
            }
            FnUpdate::Param(id, args) => {
                if args.is_empty() {
                    context[*id].get_name().to_string()
                } else {
                    let mut arg_string = format!("({}", context.get_variable_name(args[0]));
                    for arg in args.iter().skip(1) {
                        arg_string = format!("{}, {}", arg_string, context.get_variable_name(*arg));
                    }
                    format!("{}{})", context[*id].get_name(), arg_string)
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::{BinaryOp, BooleanNetwork, FnUpdate};
    use std::convert::TryFrom;

    #[test]
    fn basic_fn_update_test() {
        // Note that ids here are used dangerously (across different networks), but they work
        // because everything has the same variables and parameters.

        let bn = BooleanNetwork::try_from(
            r"
            a -> c
            b -| c
            # Note that this is not really a `valid` function but syntatically it is ok.
            $c: a & (a | (a ^ (a => (a <=> !(f(a, b) | (true | false))))))
        ",
        )
        .unwrap();

        let a = bn.as_graph().find_variable("a").unwrap();
        let b = bn.as_graph().find_variable("b").unwrap();
        let c = bn.as_graph().find_variable("c").unwrap();
        let fun = bn.get_update_function(c).as_ref().unwrap();
        let fun_string = fun.to_string(&bn);

        assert_eq!(vec![a, b], fun.collect_arguments());
        assert_eq!(
            vec![bn.find_parameter("f").unwrap()],
            fun.collect_parameters()
        );

        let mut bn = BooleanNetwork::try_from(
            r"
            a -> c
            b -| c
        ",
        )
        .unwrap();
        let id_f = bn.add_parameter("f", 2).unwrap();
        bn.add_update_function_string("c", fun_string.as_str())
            .unwrap();

        assert_eq!(fun, bn.get_update_function(c).as_ref().unwrap());

        // Construct a FnUpdate
        let f_a_b = FnUpdate::mk_param(id_f, &vec![a, b]);
        let f_a = FnUpdate::mk_var(a);
        let mut fun_2 = f_a_b.or(FnUpdate::mk_true().or(FnUpdate::mk_false()));
        fun_2 = f_a.clone().iff(fun_2.negation());
        fun_2 = f_a.clone().implies(fun_2);
        fun_2 = f_a.clone().xor(fun_2);
        fun_2 = f_a.clone().or(fun_2);
        fun_2 = f_a.clone().and(fun_2);

        assert_eq!(fun, &fun_2);

        // Destruct a FnUpdate
        let (_, op, r) = fun_2.as_binary().unwrap();
        assert_eq!(BinaryOp::And, op);
        let (_, op, r) = r.as_binary().unwrap();
        assert_eq!(BinaryOp::Or, op);
        let (_, op, r) = r.as_binary().unwrap();
        assert_eq!(BinaryOp::Xor, op);
        let (_, op, r) = r.as_binary().unwrap();
        assert_eq!(BinaryOp::Imp, op);
        let (l, op, r) = r.as_binary().unwrap();
        assert_eq!(BinaryOp::Iff, op);
        assert_eq!(a, l.as_var().unwrap());
        let inner = r.as_not().unwrap();
        let (l, _, r) = inner.as_binary().unwrap();
        assert_eq!((id_f, vec![a, b].as_slice()), l.as_param().unwrap());
        let (l, _, r) = r.as_binary().unwrap();
        assert!(l.as_const().unwrap());
        assert!(!r.as_const().unwrap());
    }
}
