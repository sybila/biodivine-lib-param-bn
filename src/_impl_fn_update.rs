use crate::symbolic_async_graph::SymbolicContext;
use crate::BinaryOp::{And, Iff, Imp, Or, Xor};
use crate::FnUpdate::*;
use crate::_aeon_parser::FnUpdateTemp;
use crate::{BinaryOp, BooleanNetwork, FnUpdate, ParameterId, VariableId};
use biodivine_lib_bdd::{Bdd, BddVariable};
use std::collections::{HashMap, HashSet};
use std::fmt::{Display, Formatter};

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

    /// Create a `p(e_1, ..., e_k)` formula where `p` is a parameter function and `e_1` through
    /// `e_k` are general argument expressions.
    pub fn mk_param(id: ParameterId, args: &[FnUpdate]) -> FnUpdate {
        Param(id, args.to_vec())
    }

    /// Same as [Self::mk_param], but can take variable IDs as arguments directly.
    pub fn mk_basic_param(id: ParameterId, args: &[VariableId]) -> FnUpdate {
        let args = args
            .iter()
            .map(|it| FnUpdate::mk_var(*it))
            .collect::<Vec<_>>();
        Param(id, args)
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
        FnUpdate::mk_binary(And, self, other)
    }

    /// Create a disjunction.
    pub fn or(self, other: FnUpdate) -> FnUpdate {
        FnUpdate::mk_binary(Or, self, other)
    }

    /// Create an exclusive or.
    pub fn xor(self, other: FnUpdate) -> FnUpdate {
        FnUpdate::mk_binary(Xor, self, other)
    }

    /// Create an implication.
    pub fn implies(self, other: FnUpdate) -> FnUpdate {
        FnUpdate::mk_binary(Imp, self, other)
    }

    /// Create an equivalence.
    pub fn iff(self, other: FnUpdate) -> FnUpdate {
        FnUpdate::mk_binary(Iff, self, other)
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
    pub fn as_param(&self) -> Option<(ParameterId, &[FnUpdate])> {
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

    /// Build an expression which is equivalent to the conjunction of the given expressions.
    pub fn mk_conjunction(items: &[FnUpdate]) -> FnUpdate {
        if items.is_empty() {
            // Empty conjunction is `true`.
            return Self::mk_true();
        }
        if items.len() == 1 {
            return items[0].clone();
        }
        if items.len() == 2 {
            return Self::mk_binary(And, items[0].clone(), items[1].clone());
        }

        let Some(first) = items.first() else {
            // Empty conjunction is `true`.
            return Self::mk_true();
        };
        let rest = Self::mk_conjunction(&items[1..]);
        first.clone().and(rest)
    }

    /// Build an expression which is equivalent to the disjunction of the given expressions.
    pub fn mk_disjunction(items: &[FnUpdate]) -> FnUpdate {
        if items.is_empty() {
            // Empty conjunction is `true`.
            return Self::mk_true();
        }
        if items.len() == 1 {
            return items[0].clone();
        }
        if items.len() == 2 {
            return Self::mk_binary(Or, items[0].clone(), items[1].clone());
        }

        let Some(first) = items.first() else {
            // Empty conjunction is `true`.
            return Self::mk_true();
        };
        let rest = Self::mk_disjunction(&items[1..]);
        first.clone().or(rest)
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
    /// The support set of the `Bdd` must be a subset of the state variables and zero-arity
    /// parameters.
    ///
    /// Note that it should be possible to also build a variant of this function where this
    /// requirement is lifted, but it's a bit more complicated and so far we are ok with only
    /// building fully instantiated update functions.
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

        let translation_map: HashMap<BddVariable, VariableId> = context
            .state_variables()
            .iter()
            .enumerate()
            .map(|(i, v)| (*v, VariableId::from_index(i)))
            .collect();

        let param_map: HashMap<BddVariable, ParameterId> = context
            .network_parameters()
            .filter_map(|p| {
                let table = context.get_explicit_function_table(p).symbolic_variables();
                if table.len() == 1 {
                    Some((table[0], p))
                } else {
                    None
                }
            })
            .collect();

        // All variables must be state variables.
        for var in bdd.support_set() {
            assert!(translation_map.contains_key(&var) || param_map.contains_key(&var));
        }

        // Now, we transform the BDD into DNF and that into a FnUpdate.
        let dnf = bdd.to_optimized_dnf();
        let dnf = dnf
            .into_iter()
            .map(|valuation| {
                let literals = valuation
                    .to_values()
                    .into_iter()
                    .map(|(var, value)| {
                        let literal = if let Some(bn_var) = translation_map.get(&var) {
                            FnUpdate::mk_var(*bn_var)
                        } else if let Some(par) = param_map.get(&var) {
                            FnUpdate::mk_param(*par, &[])
                        } else {
                            unreachable!();
                        };
                        if value {
                            literal
                        } else {
                            literal.negation()
                        }
                    })
                    .collect::<Vec<_>>();
                FnUpdate::mk_conjunction(&literals)
            })
            .collect::<Vec<_>>();
        FnUpdate::mk_disjunction(&dnf)
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
                    for fun in p_args {
                        r_arguments(fun, args);
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
                Param(id, args) => {
                    params.insert(*id);
                    for fun in args {
                        r_parameters(fun, params);
                    }
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

    /// Private to_string helper.
    fn to_string_rec(&self, context: Option<&BooleanNetwork>, no_paren: bool) -> String {
        match self {
            Const(value) => value.to_string(),
            Var(id) => {
                if let Some(ctx) = context {
                    ctx.get_variable_name(*id).to_string()
                } else {
                    format!("v_{}", id.to_index())
                }
            }
            Not(inner) => format!("!{}", Self::to_string_rec(inner, context, false)),
            Binary(op, l, r) => {
                // And/Or have special treatments so that chains don't produce
                // unnecessary parenthesis.
                let l_nested_and = *op == And && matches!(**l, Binary(And, _, _));
                let r_nested_and = *op == And && matches!(**r, Binary(And, _, _));
                let l_nested_or = *op == Or && matches!(**l, Binary(Or, _, _));
                let r_nested_or = *op == Or && matches!(**r, Binary(Or, _, _));

                let l_no_paren = l_nested_and || l_nested_or;
                let r_no_paren = r_nested_and || r_nested_or;

                let l = l.to_string_rec(context, l_no_paren);
                let r = r.to_string_rec(context, r_no_paren);

                if no_paren {
                    format!("{} {} {}", l, op, r)
                } else {
                    format!("({} {} {})", l, op, r)
                }
            }
            Param(id, args) => {
                let name = if let Some(ctx) = context {
                    ctx[*id].get_name().to_string()
                } else {
                    format!("p_{}", id.to_index())
                };
                if args.is_empty() {
                    name
                } else {
                    // No need for top-level parenthesis in parameters, since commas
                    // serve the same purpose.
                    let mut arg_string = format!("({}", args[0].to_string_rec(context, true));
                    for arg in args.iter().skip(1) {
                        arg_string =
                            format!("{}, {}", arg_string, arg.to_string_rec(context, true));
                    }
                    format!("{}{})", name, arg_string)
                }
            }
        }
    }

    /// Convert this update function to a string, taking names from the provided `BooleanNetwork`.
    pub fn to_string(&self, context: &BooleanNetwork) -> String {
        self.to_string_rec(Some(context), true)
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
                    And => match (left, right) {
                        (Some(false), _) => Some(false),
                        (_, Some(false)) => Some(false),
                        (Some(true), Some(true)) => Some(true),
                        _ => None,
                    },
                    Or => match (left, right) {
                        (Some(true), _) => Some(true),
                        (_, Some(true)) => Some(true),
                        (Some(false), Some(false)) => Some(false),
                        _ => None,
                    },
                    Iff => match (left, right) {
                        (Some(left), Some(right)) => Some(left == right),
                        _ => None,
                    },
                    Xor => match (left, right) {
                        (Some(left), Some(right)) => Some(left != right),
                        _ => None,
                    },
                    Imp => match (left, right) {
                        (Some(false), _) => Some(true),
                        (_, Some(true)) => Some(true),
                        (Some(true), Some(false)) => Some(false),
                        _ => None,
                    },
                }
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
            Param(_, args) => {
                for arg in args {
                    arg.walk_postorder(action);
                }
                action(self)
            }
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

    /// Create a copy of this [FnUpdate] with every occurrence of [VariableId] `var` substituted
    /// for [FnUpdate] `expression`.
    pub fn substitute_variable(&self, var: VariableId, expression: &FnUpdate) -> FnUpdate {
        match self {
            Const(_) => self.clone(),
            Param(p, args) => {
                let new_args = args
                    .iter()
                    .map(|it| it.substitute_variable(var, expression))
                    .collect::<Vec<_>>();
                Param(*p, new_args)
            }
            Var(id) => {
                if id == &var {
                    expression.clone()
                } else {
                    self.clone()
                }
            }
            Not(inner) => {
                let inner = inner.substitute_variable(var, expression);
                FnUpdate::mk_not(inner)
            }
            Binary(op, left, right) => {
                let left = left.substitute_variable(var, expression);
                let right = right.substitute_variable(var, expression);
                FnUpdate::mk_binary(*op, left, right)
            }
        }
    }

    /// Rename all occurrences of the specified `variables` and `parameters` to new IDs.
    pub fn rename_all(
        &self,
        variables: &HashMap<VariableId, VariableId>,
        parameters: &HashMap<ParameterId, ParameterId>,
    ) -> FnUpdate {
        match self {
            Const(_) => self.clone(),
            Var(id) => match variables.get(id) {
                Some(new_id) => Var(*new_id),
                None => self.clone(),
            },
            Param(id, args) => {
                let args = args
                    .iter()
                    .map(|it| it.rename_all(variables, parameters))
                    .collect::<Vec<_>>();
                match parameters.get(id) {
                    Some(new_id) => Param(*new_id, args),
                    None => Param(*id, args),
                }
            }
            Not(inner) => inner.rename_all(variables, parameters).negation(),
            Binary(op, left, right) => {
                let left = left.rename_all(variables, parameters);
                let right = right.rename_all(variables, parameters);
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
        let mut is_var = |it: &FnUpdate| {
            if let Var(id) = it {
                result = result || (*id == variable);
            }
        };
        self.walk_postorder(&mut is_var);
        result
    }

    /// Perform a syntactic transformation of this update function which eliminates all binary
    /// operators except for `&` and `|`. Negation is also preserved.
    ///
    /// Note that the result is neither a conjunction nor disjunctive normal form, it just
    /// eliminates all operators other than conjunction and disjunction.
    ///
    /// Furthermore, when the function contains parameters with expression arguments, the
    /// arguments are normalized as well.
    pub fn to_and_or_normal_form(&self) -> FnUpdate {
        match self {
            Const(_) | Var(_) => self.clone(),
            Param(p, args) => {
                let args = args
                    .iter()
                    .map(|it| it.to_and_or_normal_form())
                    .collect::<Vec<_>>();
                Param(*p, args)
            }
            Not(inner) => inner.to_and_or_normal_form().negation(),
            Binary(op, left, right) => {
                let left = left.to_and_or_normal_form();
                let right = right.to_and_or_normal_form();
                match op {
                    And | Or => FnUpdate::mk_binary(*op, left, right),
                    Imp => {
                        // !left | right
                        left.negation().or(right)
                    }
                    Xor => {
                        // (left | right) & !(left & right)
                        let both = left.clone().and(right.clone());
                        let one = left.or(right);
                        one.and(both.negation())
                    }
                    Iff => {
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
    /// don't expect the function to look the same afterward.
    ///
    /// Similar to [Self::to_and_or_normal_form], when the function contains parameters with
    /// complex arguments, each argument is also normalized.
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
                    let args = args
                        .iter()
                        .map(|it| it.distribute_negation())
                        .collect::<Vec<_>>();
                    let param = Param(*id, args);
                    if invert {
                        param.negation()
                    } else {
                        param
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
                            And => {
                                // !(left & right) = (!left | !right)
                                let left = recursion(left, true);
                                let right = recursion(right, true);
                                left.or(right)
                            }
                            Or => {
                                // !(left | right) = (!left & !right)
                                let left = recursion(left, true);
                                let right = recursion(right, true);
                                left.and(right)
                            }
                            Imp => {
                                // !(left => right) = (left & !right)
                                let left = recursion(left, false);
                                let right = recursion(right, true);
                                left.and(right)
                            }
                            Xor => {
                                // !(left ^ right) = (left <=> right)
                                let left = recursion(left, false);
                                let right = recursion(right, false);
                                left.iff(right)
                            }
                            Iff => {
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

    /// Utility function that eliminates unnecessary constants from this update function
    /// using standard syntactic transformations.
    pub fn simplify_constants(&self) -> FnUpdate {
        match self {
            Const(value) => Const(*value),
            Var(id) => Var(*id),
            Param(id, args) => {
                let args = args
                    .iter()
                    .map(|it| it.simplify_constants())
                    .collect::<Vec<_>>();
                Param(*id, args)
            }
            Not(inner) => {
                // !true = false
                // !false = true
                let inner = inner.simplify_constants();
                if let Some(inner_const) = inner.as_const() {
                    Const(!inner_const)
                } else {
                    Not(Box::new(inner))
                }
            }
            Binary(op, left, right) => {
                let left = left.simplify_constants();
                let right = right.simplify_constants();
                match op {
                    And => match (left.as_const(), right.as_const()) {
                        (Some(false), _) | (_, Some(false)) => Const(false),
                        (Some(true), _) => right,
                        (_, Some(true)) => left,
                        _ => left.and(right),
                    },
                    Or => match (left.as_const(), right.as_const()) {
                        (Some(true), _) | (_, Some(true)) => Const(true),
                        (Some(false), _) => right,
                        (_, Some(false)) => left,
                        _ => left.or(right),
                    },
                    Xor => match (left.as_const(), right.as_const()) {
                        (Some(true), Some(true)) | (Some(false), Some(false)) => Const(false),
                        (Some(false), Some(true)) | (Some(true), Some(false)) => Const(true),
                        (Some(false), _) => right,
                        (_, Some(false)) => left,
                        (Some(true), _) => FnUpdate::mk_not(right),
                        (_, Some(true)) => FnUpdate::mk_not(left),
                        _ => left.xor(right),
                    },
                    Iff => match (left.as_const(), right.as_const()) {
                        (Some(true), Some(true)) | (Some(false), Some(false)) => Const(true),
                        (Some(false), Some(true)) | (Some(true), Some(false)) => Const(false),
                        (Some(true), _) => right,
                        (_, Some(true)) => left,
                        (Some(false), _) => FnUpdate::mk_not(right),
                        (_, Some(false)) => FnUpdate::mk_not(left),
                        _ => left.iff(right),
                    },
                    Imp => match (left.as_const(), right.as_const()) {
                        (Some(false), _) | (_, Some(true)) => Const(true),
                        (Some(true), _) => right,
                        (_, Some(false)) => FnUpdate::mk_not(left),
                        _ => left.implies(right),
                    },
                }
            }
        }
    }
}

impl Display for FnUpdate {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.to_string_rec(None, true))
    }
}

#[cfg(test)]
mod tests {
    use crate::symbolic_async_graph::SymbolicContext;
    use crate::{BinaryOp, BooleanNetwork, FnUpdate, ParameterId, RegulatoryGraph, VariableId};
    use biodivine_lib_bdd::bdd;
    use std::collections::HashMap;
    use std::convert::TryFrom;

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
        let f_a_b = FnUpdate::mk_param(id_f, &[FnUpdate::mk_var(a), FnUpdate::mk_var(b)]);
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
        assert_eq!(
            (id_f, vec![FnUpdate::Var(a), FnUpdate::Var(b)].as_slice()),
            l.as_param().unwrap()
        );
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
            $a: b | in
        ",
        )
        .unwrap();

        let ctx = SymbolicContext::new(&bn).unwrap();
        let vars = ctx.bdd_variable_set();

        let var_a = &FnUpdate::mk_var(VariableId(0));
        let var_b = &FnUpdate::mk_var(VariableId(1));
        let par_in = &FnUpdate::mk_param(ParameterId(0), &[]);
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
            FnUpdate::mk_binary(BinaryOp::Or, a_and_b, not_a_and_b),
            FnUpdate::build_from_bdd(&ctx, &bdd)
        );

        let bdd = bdd!(vars, "a" & "in[]");
        assert_eq!(
            FnUpdate::mk_binary(BinaryOp::And, var_a.clone(), par_in.clone()),
            FnUpdate::build_from_bdd(&ctx, &bdd)
        );
    }

    #[test]
    pub fn test_variable_substitution() {
        let mut bn = BooleanNetwork::new(RegulatoryGraph::new(vec![
            "a".to_string(),
            "b".to_string(),
            "c".to_string(),
        ]));
        bn.add_parameter("f", 2).unwrap();
        let fn1 = FnUpdate::try_from_str("(a & b) | !(c & !a) & f(b, c)", &bn).unwrap();
        let fn2 = FnUpdate::try_from_str("(b <=> c)", &bn).unwrap();
        let fn3 =
            FnUpdate::try_from_str("((b <=> c) & b) | !(c & !(b <=> c)) & f(b, c)", &bn).unwrap();
        let fn4 = FnUpdate::try_from_str("(a & b & f(a, b))", &bn).unwrap();
        let fn5 = FnUpdate::try_from_str("((b <=> c) & b & f((b <=> c), b))", &bn).unwrap();

        let a = bn.as_graph().find_variable("a").unwrap();
        assert_eq!(fn3, fn1.substitute_variable(a, &fn2));
        assert_eq!(fn5, fn4.substitute_variable(a, &fn2));
    }

    #[test]
    pub fn test_constant_simplification() {
        let bn = BooleanNetwork::try_from(
            r"
            a -> b
            b -> c
            a -> c
            $c: f(a, b) | g(a, b)
        ",
        )
        .unwrap();

        assert_eq!(
            FnUpdate::try_from_str("true & b", &bn)
                .unwrap()
                .simplify_constants(),
            FnUpdate::try_from_str("b", &bn).unwrap(),
        );

        assert_eq!(
            FnUpdate::try_from_str("b & true", &bn)
                .unwrap()
                .simplify_constants(),
            FnUpdate::try_from_str("b", &bn).unwrap(),
        );

        assert_eq!(
            FnUpdate::try_from_str("false & b", &bn)
                .unwrap()
                .simplify_constants(),
            FnUpdate::try_from_str("false", &bn).unwrap(),
        );

        assert_eq!(
            FnUpdate::try_from_str("b & false", &bn)
                .unwrap()
                .simplify_constants(),
            FnUpdate::try_from_str("false", &bn).unwrap(),
        );

        assert_eq!(
            FnUpdate::try_from_str("b | false", &bn)
                .unwrap()
                .simplify_constants(),
            FnUpdate::try_from_str("b", &bn).unwrap(),
        );

        assert_eq!(
            FnUpdate::try_from_str("false | b", &bn)
                .unwrap()
                .simplify_constants(),
            FnUpdate::try_from_str("b", &bn).unwrap(),
        );

        assert_eq!(
            FnUpdate::try_from_str("b | true", &bn)
                .unwrap()
                .simplify_constants(),
            FnUpdate::try_from_str("true", &bn).unwrap(),
        );

        assert_eq!(
            FnUpdate::try_from_str("true | b", &bn)
                .unwrap()
                .simplify_constants(),
            FnUpdate::try_from_str("true", &bn).unwrap(),
        );

        assert_eq!(
            FnUpdate::try_from_str("b ^ true", &bn)
                .unwrap()
                .simplify_constants(),
            FnUpdate::try_from_str("!b", &bn).unwrap(),
        );

        assert_eq!(
            FnUpdate::try_from_str("true ^ b", &bn)
                .unwrap()
                .simplify_constants(),
            FnUpdate::try_from_str("!b", &bn).unwrap(),
        );

        assert_eq!(
            FnUpdate::try_from_str("b ^ false", &bn)
                .unwrap()
                .simplify_constants(),
            FnUpdate::try_from_str("b", &bn).unwrap(),
        );

        assert_eq!(
            FnUpdate::try_from_str("false ^ b", &bn)
                .unwrap()
                .simplify_constants(),
            FnUpdate::try_from_str("b", &bn).unwrap(),
        );

        assert_eq!(
            FnUpdate::try_from_str("b <=> true", &bn)
                .unwrap()
                .simplify_constants(),
            FnUpdate::try_from_str("b", &bn).unwrap(),
        );

        assert_eq!(
            FnUpdate::try_from_str("true <=> b", &bn)
                .unwrap()
                .simplify_constants(),
            FnUpdate::try_from_str("b", &bn).unwrap(),
        );

        assert_eq!(
            FnUpdate::try_from_str("b <=> false", &bn)
                .unwrap()
                .simplify_constants(),
            FnUpdate::try_from_str("!b", &bn).unwrap(),
        );

        assert_eq!(
            FnUpdate::try_from_str("false <=> b", &bn)
                .unwrap()
                .simplify_constants(),
            FnUpdate::try_from_str("!b", &bn).unwrap(),
        );

        assert_eq!(
            FnUpdate::try_from_str("b => false", &bn)
                .unwrap()
                .simplify_constants(),
            FnUpdate::try_from_str("!b", &bn).unwrap(),
        );

        assert_eq!(
            FnUpdate::try_from_str("false => b", &bn)
                .unwrap()
                .simplify_constants(),
            FnUpdate::try_from_str("true", &bn).unwrap(),
        );

        assert_eq!(
            FnUpdate::try_from_str("b => true", &bn)
                .unwrap()
                .simplify_constants(),
            FnUpdate::try_from_str("true", &bn).unwrap(),
        );

        assert_eq!(
            FnUpdate::try_from_str("true => b", &bn)
                .unwrap()
                .simplify_constants(),
            FnUpdate::try_from_str("b", &bn).unwrap(),
        );

        assert_eq!(
            FnUpdate::try_from_str("true & f(b & false, c) => g(a, b) | (a <=> true)", &bn)
                .unwrap()
                .simplify_constants(),
            FnUpdate::try_from_str("f(false, c) => g(a, b) | a", &bn).unwrap(),
        );
    }

    #[test]
    fn test_operator_coalescing() {
        let bn = BooleanNetwork::try_from(
            r"
            a -> b
            b -> c
            c -> a
        ",
        )
        .unwrap();
        assert_eq!(
            FnUpdate::try_from_str("(a & !b & c) | (!a & b) | c", &bn)
                .unwrap()
                .to_string(&bn),
            "(a & !b & c) | (!a & b) | c"
        );
    }

    #[test]
    fn test_nary_operators() {
        let bn = BooleanNetwork::try_from(
            r"
            a -> b
            b -> c
            c -> a
        ",
        )
        .unwrap();
        let args = bn.variables().map(FnUpdate::mk_var).collect::<Vec<_>>();
        assert_eq!(
            FnUpdate::try_from_str("a & b & c", &bn).unwrap(),
            FnUpdate::mk_conjunction(&args)
        );
        assert_eq!(
            FnUpdate::try_from_str("a | b | c", &bn).unwrap(),
            FnUpdate::mk_disjunction(&args)
        );
    }
}
