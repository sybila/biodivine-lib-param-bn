use crate::{FnUpdate, RegulatoryGraph};
use biodivine_lib_bdd::boolean_expression::BooleanExpression;

// TODO: This really should be try_from_expression and return Option.
impl FnUpdate {
    /// Convert a `BooleanExpression` to a `FnUpdate`, using `RegulatoryGraph` to resolve variable
    /// names.
    ///
    /// Panics: expression contains unknown variable.
    pub fn from_boolean_expression(
        expression: BooleanExpression,
        graph: &RegulatoryGraph,
    ) -> FnUpdate {
        match expression {
            BooleanExpression::Const(value) => FnUpdate::Const(value),
            BooleanExpression::Variable(name) => FnUpdate::Var(graph.find_variable(&name).unwrap()),
            BooleanExpression::Not(inner) => FnUpdate::from_boolean_expression(*inner, graph).negation(),
            BooleanExpression::Or(l, r) => FnUpdate::from_boolean_expression(*l, graph)
                .or(FnUpdate::from_boolean_expression(*r, graph)),
            BooleanExpression::And(l, r) => FnUpdate::from_boolean_expression(*l, graph)
                .and(FnUpdate::from_boolean_expression(*r, graph)),
            BooleanExpression::Iff(l, r) => FnUpdate::from_boolean_expression(*l, graph)
                .iff(FnUpdate::from_boolean_expression(*r, graph)),
            BooleanExpression::Imp(l, r) => FnUpdate::from_boolean_expression(*l, graph)
                .implies(FnUpdate::from_boolean_expression(*r, graph)),
            BooleanExpression::Xor(l, r) => FnUpdate::from_boolean_expression(*l, graph)
                .xor(FnUpdate::from_boolean_expression(*r, graph)),
        }
    }
}
