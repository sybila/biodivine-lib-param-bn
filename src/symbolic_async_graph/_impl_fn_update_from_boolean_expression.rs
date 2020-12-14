use crate::{BinaryOp, FnUpdate, RegulatoryGraph};
use biodivine_lib_bdd::boolean_expression::BooleanExpression;

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
            BooleanExpression::Not(inner) => {
                FnUpdate::Not(Box::new(FnUpdate::from_boolean_expression(*inner, graph)))
            }
            BooleanExpression::Or(l, r) => FnUpdate::Binary(
                BinaryOp::Or,
                Box::new(FnUpdate::from_boolean_expression(*l, graph)),
                Box::new(FnUpdate::from_boolean_expression(*r, graph)),
            ),
            BooleanExpression::And(l, r) => FnUpdate::Binary(
                BinaryOp::And,
                Box::new(FnUpdate::from_boolean_expression(*l, graph)),
                Box::new(FnUpdate::from_boolean_expression(*r, graph)),
            ),
            BooleanExpression::Iff(l, r) => FnUpdate::Binary(
                BinaryOp::Iff,
                Box::new(FnUpdate::from_boolean_expression(*l, graph)),
                Box::new(FnUpdate::from_boolean_expression(*r, graph)),
            ),
            BooleanExpression::Imp(l, r) => FnUpdate::Binary(
                BinaryOp::Imp,
                Box::new(FnUpdate::from_boolean_expression(*l, graph)),
                Box::new(FnUpdate::from_boolean_expression(*r, graph)),
            ),
            BooleanExpression::Xor(l, r) => FnUpdate::Binary(
                BinaryOp::Xor,
                Box::new(FnUpdate::from_boolean_expression(*l, graph)),
                Box::new(FnUpdate::from_boolean_expression(*r, graph)),
            ),
        }
    }
}
