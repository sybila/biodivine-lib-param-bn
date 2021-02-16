use crate::{FnUpdate, RegulatoryGraph};
use biodivine_lib_bdd::boolean_expression::BooleanExpression;

impl FnUpdate {
    /// Convert a `BooleanExpression` to a `FnUpdate`, using `RegulatoryGraph` to resolve variable
    /// names.
    pub fn try_from_expression(
        expression: BooleanExpression,
        graph: &RegulatoryGraph,
    ) -> Option<FnUpdate> {
        Some(match expression {
            BooleanExpression::Const(value) => FnUpdate::Const(value),
            BooleanExpression::Variable(name) => FnUpdate::Var(graph.find_variable(&name)?),
            BooleanExpression::Not(inner) => {
                FnUpdate::try_from_expression(*inner, graph)?.negation()
            }
            BooleanExpression::Or(l, r) => {
                let l = FnUpdate::try_from_expression(*l, graph)?;
                let r = FnUpdate::try_from_expression(*r, graph)?;
                l.or(r)
            }
            BooleanExpression::And(l, r) => {
                let l = FnUpdate::try_from_expression(*l, graph)?;
                let r = FnUpdate::try_from_expression(*r, graph)?;
                l.and(r)
            }
            BooleanExpression::Iff(l, r) => {
                let l = FnUpdate::try_from_expression(*l, graph)?;
                let r = FnUpdate::try_from_expression(*r, graph)?;
                l.iff(r)
            }
            BooleanExpression::Imp(l, r) => {
                let l = FnUpdate::try_from_expression(*l, graph)?;
                let r = FnUpdate::try_from_expression(*r, graph)?;
                l.implies(r)
            }
            BooleanExpression::Xor(l, r) => {
                let l = FnUpdate::try_from_expression(*l, graph)?;
                let r = FnUpdate::try_from_expression(*r, graph)?;
                l.xor(r)
            }
        })
    }
}
