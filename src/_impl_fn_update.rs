use crate::symbolic_async_graph::SymbolicContext;
use crate::FnUpdate::*;
use crate::_aeon_parser::FnUpdateTemp;
use crate::{BinaryOp, BooleanNetwork, ExtendedBoolean, FnUpdate, ParameterId, Space, VariableId};
use biodivine_lib_bdd::{Bdd, BddPartialValuation, BddVariable};
use std::collections::{HashMap, HashSet};

/// Constructor and destructor utility methods. These mainly avoid unnecessary boxing
/// and exhaustive pattern matching when not necessary.
impl FnUpdate {
    /// Create a `true` formula.
    pub fn mk_true() -> FnUpdate {
        Const(true)
    }

    /// Create a `false` formula.
    pub fn mk_false() -> FnUpdate {
        Const(false)
    }

    /// Create an `x` formula where `x` is a Boolean variable.
    pub fn mk_var(id: VariableId) -> FnUpdate {
        Var(id)
    }

    /// Create a `p(x_1, ..., x_k)` formula where `p` is a parameter function and `x_1` through
    /// `x_k` are its arguments.
    pub fn mk_param(id: ParameterId, args: &[VariableId]) -> FnUpdate {
        Param(id, args.to_vec())
    }

    /// Create a `!phi` formula, where `phi` is an inner `FnUpdate`.
    pub fn mk_not(inner: FnUpdate) -> FnUpdate {
        Not(Box::new(inner))
    }

    /// Create a `phi 'op' psi` where `phi` and `psi` are arguments of `op` operator.
    pub fn mk_binary(op: BinaryOp, left: FnUpdate, right: FnUpdate) -> FnUpdate {
        Binary(op, Box::new(left), Box::new(right))
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
            Const(value) => Some(*value),
            _ => None,
        }
    }

    /// If `Var`, return the id, otherwise return `None`.
    pub fn as_var(&self) -> Option<VariableId> {
        match self {
            Var(value) => Some(*value),
            _ => None,
        }
    }

    /// If `Param`, return the id and args, otherwise return `None`.
    pub fn as_param(&self) -> Option<(ParameterId, &[VariableId])> {
        match self {
            Param(id, args) => Some((*id, args)),
            _ => None,
        }
    }

    /// If `Not`, return the inner function, otherwise return `None`.
    pub fn as_not(&self) -> Option<&FnUpdate> {
        match self {
            Not(inner) => Some(inner),
            _ => None,
        }
    }

    /// If `Binary`, return the operator and left/right formulas, otherwise return `None`.
    pub fn as_binary(&self) -> Option<(&FnUpdate, BinaryOp, &FnUpdate)> {
        match self {
            Binary(op, l, r) => Some((l, *op, r)),
            _ => None,
        }
    }
}

/// Other utility methods.
impl FnUpdate {
    /// Try to parse an update function from a string expression using the provided `network`
    /// as context.
    pub fn try_from_str(expression: &str, network: &BooleanNetwork) -> Result<FnUpdate, String> {
        let tmp = FnUpdateTemp::try_from(expression)?;
        let update = tmp.into_fn_update(network)?;
        Ok(*update)
    }

    /// Build an update function from an instantiated `Bdd`.
    ///
    /// The support set of the `Bdd` must be a subset of the state variables, i.e. the `Bdd`
    /// can only depend on the network variables. Note that it should be possible to also build
    /// a variant of this function where this requirement is lifted, but it's a bit more
    /// complicated and so far we are ok with only building fully instantiated update functions.
    ///
    /// The function produces a DNF representation based on all satisfying clauses. This is far
    /// from minimal, but appears to be slightly more concise than the default translation in
    /// lib-bdd.
    pub fn build_from_bdd(context: &SymbolicContext, bdd: &Bdd) -> FnUpdate {
        if bdd.is_true() {
            return FnUpdate::mk_true();
        }
        if bdd.is_false() {
            return FnUpdate::mk_false();
        }

        let state_variables: HashMap<BddVariable, VariableId> = context
            .state_variables()
            .iter()
            .enumerate()
            .map(|(i, v)| (*v, VariableId::from_index(i)))
            .collect();
        let support = bdd.support_set();
        for k in &support {
            if !state_variables.contains_key(k) {
                panic!("Non-state variables found in the provided BDD.")
            }
        }

        // Because the BDD isn't constant, there must be at least one clause and each clause
        // must have at least one literal.

        fn build_clause(
            map: &HashMap<BddVariable, VariableId>,
            clause: BddPartialValuation,
        ) -> FnUpdate {
            fn build_literal(
                map: &HashMap<BddVariable, VariableId>,
                literal: (BddVariable, bool),
            ) -> FnUpdate {
                let var = FnUpdate::mk_var(*map.get(&literal.0).unwrap());
                if literal.1 {
                    var
                } else {
                    FnUpdate::mk_not(var)
                }
            }

            let mut literals = clause.to_values().into_iter();
            let mut clause = build_literal(map, literals.next().unwrap());
            for literal in literals {
                let literal = build_literal(map, literal);
                clause = FnUpdate::mk_binary(BinaryOp::And, clause, literal);
            }
            clause
        }

        let mut clauses = bdd.sat_clauses();
        let mut result = build_clause(&state_variables, clauses.next().unwrap());
        for clause in clauses {
            let clause = build_clause(&state_variables, clause);
            result = FnUpdate::mk_binary(BinaryOp::Or, result, clause);
        }
        result
    }

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
            Const(value) => value.to_string(),
            Var(id) => context.get_variable_name(*id).to_string(),
            Not(inner) => format!("!{}", inner.to_string(context)),
            Binary(op, l, r) => {
                format!("({} {} {})", l.to_string(context), op, r.to_string(context))
            }
            Param(id, args) => {
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

    /// If possible, evaluate this function using the given network variable valuation.
    ///
    /// Note that this only works when the function output does not depend on parameters, and
    /// all necessary variable values are part of the valuation. Otherwise, the function
    /// returns `None`, as the value cannot be determined.
    ///
    /// However, note that in some cases, even a partially specified function can be evaluated.
    /// For example, `A & f(X, Y)` is false whenever `A = false`, regardless of uninterpreted
    /// function `f`. In such cases, this method may still output the correct result.
    ///
    /// In other words, the meaning of this method should be interpreted as "if it is possible
    /// to unambiguously evaluate this function using the provided valuation, do it; otherwise
    /// return `None`".
    pub fn evaluate(&self, values: &HashMap<VariableId, bool>) -> Option<bool> {
        match self {
            Const(value) => Some(*value),
            Var(id) => values.get(id).cloned(),
            Param(_, _) => None,
            Not(inner) => inner.evaluate(values).map(|it| !it),
            Binary(op, left, right) => {
                let left = left.evaluate(values);
                let right = right.evaluate(values);
                match op {
                    BinaryOp::And => match (left, right) {
                        (Some(false), _) => Some(false),
                        (_, Some(false)) => Some(false),
                        (Some(true), Some(true)) => Some(true),
                        _ => None,
                    },
                    BinaryOp::Or => match (left, right) {
                        (Some(true), _) => Some(true),
                        (_, Some(true)) => Some(true),
                        (Some(false), Some(false)) => Some(false),
                        _ => None,
                    },
                    BinaryOp::Iff => match (left, right) {
                        (Some(left), Some(right)) => Some(left == right),
                        _ => None,
                    },
                    BinaryOp::Xor => match (left, right) {
                        (Some(left), Some(right)) => Some(left != right),
                        _ => None,
                    },
                    BinaryOp::Imp => match (left, right) {
                        (Some(false), _) => Some(true),
                        (_, Some(true)) => Some(true),
                        (Some(true), Some(false)) => Some(false),
                        _ => None,
                    },
                }
            }
        }
    }

    /// Test that this update function is a syntactic specialisation of the provided `FnUpdate`.
    ///
    /// Syntactic specialisation is a function that has the same abstract syntax tree, except that
    /// some occurrences of parameters can be substituted for more concrete Boolean functions.
    ///
    /// Note that this is not entirely bulletproof, as it does not check for usage of multiple
    /// parameters within the same function, which could influence the semantics of the main
    /// function, but does not influence the specialisation.
    pub fn is_specialisation_of(&self, other: &FnUpdate) -> bool {
        match other {
            Const(_) => self == other,
            Var(_) => self == other,
            Not(inner) => {
                if let Some(self_inner) = self.as_not() {
                    self_inner.is_specialisation_of(inner)
                } else {
                    false
                }
            }
            Binary(op, left, right) => {
                if let Some((self_left, self_op, self_right)) = self.as_binary() {
                    self_op == *op
                        && self_left.is_specialisation_of(left)
                        && self_right.is_specialisation_of(right)
                } else {
                    false
                }
            }
            Param(_, args) => {
                // Every argument in this sub-tree must be declared in the parameter.
                self.collect_arguments()
                    .iter()
                    .all(|arg| args.contains(arg))
            }
        }
    }

    /// Allows us to iterate through all nodes of the abstract syntax tree of this function
    /// in post-order.
    ///
    /// Note that this is a preliminary version of the API. A more robust implementation should
    /// provide a standard iterator interface.
    pub fn walk_postorder<F>(&self, action: &mut F)
    where
        F: FnMut(&FnUpdate),
    {
        match self {
            Const(_) => action(self),
            Param(_, _) => action(self),
            Var(_) => action(self),
            Not(inner) => {
                inner.walk_postorder(action);
                action(self);
            }
            Binary(_, left, right) => {
                left.walk_postorder(action);
                right.walk_postorder(action);
                action(self);
            }
        }
    }

    /// Create a copy of this function which replaces every occurrence of every
    /// `VariableId` with a new one supplied by the provided vector (original `VariableId`
    /// is the index into the vector). Similarly replaces every `ParameterId`.
    pub fn substitute(&self, vars: &[VariableId], params: &[ParameterId]) -> FnUpdate {
        match self {
            Const(_) => self.clone(),
            Param(id, args) => {
                let new_args = args.iter().map(|it| vars[it.0]).collect();
                Param(params[id.0], new_args)
            }
            Var(id) => FnUpdate::mk_var(vars[id.0]),
            Not(inner) => {
                let inner = inner.substitute(vars, params);
                FnUpdate::mk_not(inner)
            }
            Binary(op, left, right) => {
                let left = left.substitute(vars, params);
                let right = right.substitute(vars, params);
                FnUpdate::mk_binary(*op, left, right)
            }
        }
    }

    /// Returns true if this update function uses the given parameter.
    pub fn contains_parameter(&self, parameter: ParameterId) -> bool {
        let mut result = false;
        let mut is_param = |it: &FnUpdate| {
            if let Param(id, _) = it {
                result = result || (*id == parameter);
            }
        };
        self.walk_postorder(&mut is_param);
        result
    }

    /// Returns true if this update function uses the given variable.
    pub fn contains_variable(&self, variable: VariableId) -> bool {
        let mut result = false;
        let mut is_var = |it: &FnUpdate| match it {
            Var(id) => result = result || (*id == variable),
            Param(_, args) => result = result || args.contains(&variable),
            _ => {}
        };
        self.walk_postorder(&mut is_var);
        result
    }

    /// Perform a syntactic transformation of this update function which eliminates all binary
    /// operators except for `&` and `|`. Negation is also preserved.
    ///
    /// Note that the result is neither a conjunction or disjunctive normal form, it just
    /// eliminates all operators other than conjunction and disjunction.
    pub fn to_and_or_normal_form(&self) -> FnUpdate {
        match self {
            Const(_) | Var(_) | Param(_, _) => self.clone(),
            Not(inner) => inner.to_and_or_normal_form().negation(),
            Binary(op, left, right) => {
                let left = left.to_and_or_normal_form();
                let right = right.to_and_or_normal_form();
                match op {
                    BinaryOp::And | BinaryOp::Or => FnUpdate::mk_binary(*op, left, right),
                    BinaryOp::Imp => {
                        // !left | right
                        left.negation().or(right)
                    }
                    BinaryOp::Xor => {
                        // (left | right) & !(left & right)
                        let both = left.clone().and(right.clone());
                        let one = left.and(right);
                        one.and(both.negation())
                    }
                    BinaryOp::Iff => {
                        // (left & right) | (!left & !right)
                        let both = left.clone().and(right.clone());
                        let neither = left.negation().and(right.negation());
                        both.or(neither)
                    }
                }
            }
        }
    }

    /// Perform a syntactic transformation which pushes every negation to literals (constants,
    /// variables, and parameter terms).
    ///
    /// Note that constants will be automatically negated (true => false, false => true). Also,
    /// keep in mind that this will rewrite binary operators (and => or, iff => xor, etc.), so
    /// don't expect the function to look the same afterwards.
    pub fn distribute_negation(&self) -> FnUpdate {
        fn recursion(update: &FnUpdate, invert: bool) -> FnUpdate {
            match update {
                Const(value) => Const(*value != invert),
                Var(var) => {
                    if invert {
                        Var(*var).negation()
                    } else {
                        update.clone()
                    }
                }
                Param(id, args) => {
                    if invert {
                        Param(*id, args.clone()).negation()
                    } else {
                        update.clone()
                    }
                }
                Not(inner) => recursion(inner, !invert),
                Binary(op, left, right) => {
                    if !invert {
                        // If we are not inverting, just propagate the result.
                        FnUpdate::mk_binary(*op, recursion(left, false), recursion(right, false))
                    } else {
                        // Otherwise we must do magic.
                        match op {
                            BinaryOp::And => {
                                // !(left & right) = (!left | !right)
                                let left = recursion(left, true);
                                let right = recursion(right, true);
                                left.or(right)
                            }
                            BinaryOp::Or => {
                                // !(left | right) = (!left & !right)
                                let left = recursion(left, true);
                                let right = recursion(right, true);
                                left.and(right)
                            }
                            BinaryOp::Imp => {
                                // !(left => right) = (left & !right)
                                let left = recursion(left, false);
                                let right = recursion(right, true);
                                left.and(right)
                            }
                            BinaryOp::Xor => {
                                // !(left ^ right) = (left <=> right)
                                let left = recursion(left, false);
                                let right = recursion(right, false);
                                left.iff(right)
                            }
                            BinaryOp::Iff => {
                                // !(left <=> right) = (left ^ right)
                                let left = recursion(left, false);
                                let right = recursion(right, false);
                                left.xor(right)
                            }
                        }
                    }
                }
            }
        }

        recursion(self, false)
    }

    /// Perform partial evaluation of this function using extended Boolean values in the given
    /// `Space`.

    pub fn eval_in_space(&self, space: &Space) -> ExtendedBoolean {
        match self {
            Const(value) => {
                if *value {
                    ExtendedBoolean::One
                } else {
                    ExtendedBoolean::Zero
                }
            }
            Var(var) => space[*var],
            Param(_, _) => {
                // We assume that a parameter can evaluate to anything.
                ExtendedBoolean::Any
            }
            Not(inner) => inner.eval_in_space(space).negate(),
            Binary(op, left, right) => {
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
}

#[cfg(test)]
mod tests {
    use crate::symbolic_async_graph::SymbolicContext;
    use crate::{BinaryOp, BooleanNetwork, FnUpdate, VariableId};
    use biodivine_lib_bdd::bdd;
    use std::collections::HashMap;
    use std::convert::TryFrom;

    #[test]
    fn fn_update_specialisation_test() {
        let bn = BooleanNetwork::try_from(
            r"
                a -> c1
                b -> c1
                a -> c2
                b -> c2
                a -> c3
                b -> c3
                $c1: !(a => b) | f(a, b)
                $c2: !(a => b) | ((a <=> b) & g(b))
                $c3: (a => b) | f(a, b)
            ",
        )
        .unwrap();

        let c1 = bn.as_graph().find_variable("c1").unwrap();
        let c2 = bn.as_graph().find_variable("c2").unwrap();
        let c3 = bn.as_graph().find_variable("c3").unwrap();

        let fn_c1 = bn.get_update_function(c1).as_ref().unwrap();
        let fn_c2 = bn.get_update_function(c2).as_ref().unwrap();
        let fn_c3 = bn.get_update_function(c3).as_ref().unwrap();

        assert!(fn_c2.is_specialisation_of(fn_c1));
        assert!(!fn_c1.is_specialisation_of(fn_c2));
        assert!(!fn_c3.is_specialisation_of(fn_c1));
        assert!(!fn_c3.is_specialisation_of(fn_c2));
        assert!(fn_c3.is_specialisation_of(fn_c3));
    }

    #[test]
    fn fn_update_eval_test() {
        let bn = BooleanNetwork::try_from(
            r"
            a -> c
            b -| c
            $c: true & (!a | (a & b) | f(b))
        ",
        )
        .unwrap();

        // This will not test all possible branches, but should cover the decisions
        // reasonably well...

        let a = bn.as_graph().find_variable("a").unwrap();
        let b = bn.as_graph().find_variable("b").unwrap();
        let c = bn.as_graph().find_variable("c").unwrap();
        let fun = bn.get_update_function(c).as_ref().unwrap();

        let mut vals = HashMap::new();
        assert_eq!(None, fun.evaluate(&vals));

        vals.insert(a, false);
        assert_eq!(Some(true), fun.evaluate(&vals));

        vals.insert(a, true);
        vals.insert(b, true);
        assert_eq!(Some(true), fun.evaluate(&vals));

        vals.insert(a, true);
        vals.insert(b, false);
        assert_eq!(None, fun.evaluate(&vals));
    }

    #[test]
    fn basic_fn_update_test() {
        // Note that ids here are used dangerously (across different networks), but they work
        // because everything has the same variables and parameters.

        let bn = BooleanNetwork::try_from(
            r"
            a -> c
            b -| c
            # Note that this is not really a `valid` function in terms of the regulatory graph.
            # But syntatically it is ok and should go through the parser.
            $c: a & (a | (a ^ (a => (a <=> !(f(a, b) | (true | false))))))
            # Another function just for comparisons.
            c -| b
            $b: !c
        ",
        )
        .unwrap();

        let a = bn.as_graph().find_variable("a").unwrap();
        let b = bn.as_graph().find_variable("b").unwrap();
        let c = bn.as_graph().find_variable("c").unwrap();
        let f = bn.find_parameter("f").unwrap();
        let fun = bn.get_update_function(c).as_ref().unwrap();
        let fun_string = fun.to_string(&bn);

        let fun_parse = FnUpdate::try_from_str(
            "a & (a | (a ^ (a => (a <=> !(f(a, b) | (true | false))))))",
            &bn,
        )
        .unwrap();
        assert_eq!(fun, &fun_parse);

        assert_eq!(vec![a, b], fun.collect_arguments());
        assert_eq!(
            vec![bn.find_parameter("f").unwrap()],
            fun.collect_parameters()
        );

        assert!(fun.contains_variable(a));
        assert!(fun.contains_variable(b));
        assert!(!fun.contains_variable(c));
        assert!(fun.contains_parameter(f));

        let fun_b = bn.get_update_function(b).as_ref().unwrap();
        assert!(!fun_b.contains_variable(a));
        assert!(!fun_b.contains_variable(b));
        assert!(fun_b.contains_variable(c));
        assert!(!fun_b.contains_parameter(f));

        let mut bn = BooleanNetwork::try_from(
            r"
            a -> c
            b -| c
        ",
        )
        .unwrap();
        let id_f = bn.add_parameter("f", 2).unwrap();
        bn.add_string_update_function("c", fun_string.as_str())
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

    #[test]
    pub fn test_symbolic_instantiation() {
        let bn = BooleanNetwork::try_from(
            "
            a -> b
            b -> a
            b -| b
        ",
        )
        .unwrap();

        let ctx = SymbolicContext::new(&bn).unwrap();
        let vars = ctx.bdd_variable_set();

        let var_a = &FnUpdate::mk_var(VariableId(0));
        let var_b = &FnUpdate::mk_var(VariableId(1));
        let not_var_a = &FnUpdate::mk_not(var_a.clone());
        let not_var_b = &FnUpdate::mk_not(var_b.clone());

        let bdd = bdd!(vars, "a");
        assert_eq!(
            FnUpdate::mk_var(VariableId(0)),
            FnUpdate::build_from_bdd(&ctx, &bdd)
        );

        let bdd = bdd!(vars, "a" & "b");
        assert_eq!(
            FnUpdate::mk_binary(BinaryOp::And, var_a.clone(), var_b.clone()),
            FnUpdate::build_from_bdd(&ctx, &bdd)
        );

        let bdd = bdd!(vars, "a" <=> "b");
        let a_and_b = FnUpdate::mk_binary(BinaryOp::And, var_a.clone(), var_b.clone());
        let not_a_and_b = FnUpdate::mk_binary(BinaryOp::And, not_var_a.clone(), not_var_b.clone());
        assert_eq!(
            FnUpdate::mk_binary(BinaryOp::Or, not_a_and_b, a_and_b),
            FnUpdate::build_from_bdd(&ctx, &bdd)
        );
    }
}
