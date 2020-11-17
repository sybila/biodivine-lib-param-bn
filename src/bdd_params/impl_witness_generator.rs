use crate::bdd_params::{BddParameterEncoder, BddParams};
use crate::{BinaryOp, BooleanNetwork, FnUpdate, VariableId};
use biodivine_lib_bdd::boolean_expression::BooleanExpression;
use biodivine_lib_bdd::{Bdd, BddValuation, BddValuationIterator, BddVariableSet};

impl BooleanNetwork {
    pub fn make_witness(
        &self,
        params: &BddParams,
        encoder: &BddParameterEncoder,
    ) -> BooleanNetwork {
        let valuation = params.as_bdd().sat_witness();
        if valuation.is_none() {
            panic!("Cannot create witness for empty parameter set.");
        }
        return self.make_witness_for_valuation(valuation.unwrap(), encoder);
    }

    pub fn make_witness_for_valuation(
        &self,
        valuation: BddValuation,
        encoder: &BddParameterEncoder,
    ) -> BooleanNetwork {
        // First, make functions for explicit parameters:
        let mut explicit_parameter_expressions = Vec::with_capacity(self.parameters.len());
        for i_p in 0..self.parameters.len() {
            let parameter = &self.parameters[i_p];
            let parameter_input_table = &encoder.explicit_function_tables[i_p];
            let num_inputs = parameter.cardinality as u16;
            if num_inputs == 0 {
                assert_eq!(parameter_input_table.len(), 1);
                explicit_parameter_expressions.push(BooleanExpression::Const(
                    valuation.value(parameter_input_table[0]),
                ));
            } else {
                let parameter_function_input_vars = BddVariableSet::new_anonymous(num_inputs);

                let variables_and_valuations = parameter_input_table
                    .iter()
                    .zip(BddValuationIterator::new(num_inputs));

                // initially, the function is just false
                let mut function_bdd = parameter_function_input_vars.mk_false();
                for (bdd_variable, input_valuation) in variables_and_valuations {
                    if valuation.value(*bdd_variable) {
                        // and for each `1` in the function table, we add the input valuation
                        let input_valuation_bdd = Self::valuation_to_formula(
                            &input_valuation,
                            &parameter_function_input_vars,
                        );
                        function_bdd = function_bdd.or(&input_valuation_bdd);
                    }
                }

                let parameter_expression =
                    function_bdd.to_boolean_expression(&parameter_function_input_vars);
                explicit_parameter_expressions.push(parameter_expression);
            }
        }

        let mut result = self.clone();
        for i_var in 0..self.graph.num_vars() {
            if let Some(function) = &self.update_functions[i_var] {
                // Replace parameters in the explicit function with actual functions
                let resolved_function =
                    *Self::replace_parameters(function, &explicit_parameter_expressions);
                result.update_functions[i_var] = Some(resolved_function);
            } else {
                // Build an anonymous update function
                let regulators = &encoder.regulators[i_var];
                let num_inputs = regulators.len() as u16;
                let function_input_table = &encoder.implicit_function_tables[i_var];
                let function_input_vars = BddVariableSet::new_anonymous(num_inputs);

                let variables_and_valuations = function_input_table
                    .iter()
                    .zip(BddValuationIterator::new(num_inputs));
                let mut function_bdd = function_input_vars.mk_false();
                for (bdd_variable, input_valuation) in variables_and_valuations {
                    if valuation.value(*bdd_variable) {
                        let input_valuation_bdd =
                            Self::valuation_to_formula(&input_valuation, &function_input_vars);
                        function_bdd = function_bdd.or(&input_valuation_bdd);
                    }
                }

                let function_expression = function_bdd.to_boolean_expression(&function_input_vars);
                result.update_functions[i_var] = Some(*Self::expression_to_fn_update(
                    &function_expression,
                    &regulators,
                ));
            }
        }

        result.parameters.clear();
        result.parameter_to_index.clear();

        return result;
    }

    /// Make a Bdd that exactly describes given valuation.
    /// TODO: This should maybe be part of the bdd library.
    fn valuation_to_formula(valuation: &BddValuation, vars: &BddVariableSet) -> Bdd {
        assert_eq!(valuation.num_vars(), vars.num_vars());
        let mut bdd = vars.mk_true();
        for var in vars.variables() {
            bdd = bdd.and(&if valuation.value(var) {
                vars.mk_var(var)
            } else {
                vars.mk_not_var(var)
            });
        }
        return bdd;
    }

    fn replace_parameters(
        update_function: &FnUpdate,
        parameter_expressions: &Vec<BooleanExpression>,
    ) -> Box<FnUpdate> {
        return Box::new(match update_function {
            FnUpdate::Const(value) => FnUpdate::Const(*value),
            FnUpdate::Var(id) => FnUpdate::Var(*id),
            FnUpdate::Not(a) => FnUpdate::Not(Self::replace_parameters(a, parameter_expressions)),
            FnUpdate::Binary(op, a, b) => FnUpdate::Binary(
                *op,
                Self::replace_parameters(a, parameter_expressions),
                Self::replace_parameters(b, parameter_expressions),
            ),
            FnUpdate::Param(id, args) => {
                let parameter_expression = &parameter_expressions[id.0];
                *Self::expression_to_fn_update(parameter_expression, args)
            }
        });
    }

    fn expression_to_fn_update(
        expression: &BooleanExpression,
        args: &Vec<VariableId>,
    ) -> Box<FnUpdate> {
        return Box::new(match expression {
            BooleanExpression::Const(value) => FnUpdate::Const(*value),
            BooleanExpression::Iff(a, b) => FnUpdate::Binary(
                BinaryOp::Iff,
                Self::expression_to_fn_update(a, args),
                Self::expression_to_fn_update(b, args),
            ),
            BooleanExpression::Imp(a, b) => FnUpdate::Binary(
                BinaryOp::Imp,
                Self::expression_to_fn_update(a, args),
                Self::expression_to_fn_update(b, args),
            ),
            BooleanExpression::Or(a, b) => FnUpdate::Binary(
                BinaryOp::Or,
                Self::expression_to_fn_update(a, args),
                Self::expression_to_fn_update(b, args),
            ),
            BooleanExpression::And(a, b) => FnUpdate::Binary(
                BinaryOp::And,
                Self::expression_to_fn_update(a, args),
                Self::expression_to_fn_update(b, args),
            ),
            BooleanExpression::Xor(a, b) => FnUpdate::Binary(
                BinaryOp::Xor,
                Self::expression_to_fn_update(a, args),
                Self::expression_to_fn_update(b, args),
            ),
            BooleanExpression::Not(a) => FnUpdate::Not(Self::expression_to_fn_update(a, args)),
            BooleanExpression::Variable(name) => {
                // name is x_i, so we can strip x_ away and parse it
                let name = &name[2..];
                let arg_index: usize = name.parse().unwrap();
                FnUpdate::Var(args[arg_index])
            }
        });
    }
}

#[cfg(test)]
mod tests {
    use crate::async_graph::AsyncGraph;
    use crate::BooleanNetwork;
    use std::convert::TryFrom;

    #[test]
    pub fn make_witness_0() {
        let network = BooleanNetwork::try_from(
            "
            a -> b
            a -?? a
            b -|? c
            a ->? c
            c -? a
            c -| d
            $a: a & (p(c) => (c | c))
            $b: p(a) <=> q(a, a)
            $c: q(b, b) => !(b ^ k)
        ",
        )
        .unwrap();
        let graph = AsyncGraph::new(network).unwrap();
        let witness = graph.make_witness(graph.unit_params());
        let witness_string = BooleanNetwork::try_from(
            "
            a -> b
            a -?? a
            b -|? c
            a ->? c
            c -? a
            c -| d
            # validity of the functions has been manually verified
            $a: (a & (true => (c | c)))
            $b: (true <=> (a & a))
            $c: ((b & b) => !(b ^ false))
            $d: !c
        ",
        )
        .unwrap();
        assert_eq!(witness, witness_string);
        // turn the witness into a graph again - there should be exactly one parametrisation:
        let graph = AsyncGraph::new(witness).unwrap();
        assert_eq!(graph.unit_params().cardinality(), 1.0);
    }

    #[test]
    pub fn make_witness_1() {
        let network = BooleanNetwork::try_from(
            "
            SSF -> SWI5

            SSF -> ACE2

            SBF -> SSF
            HCM1 -> SSF

            MBF -> YHP1
            SBF -> YHP1

            MBF -> HCM1
            SBF -> HCM1

            MBF -> YOX1
            SBF -> YOX1

            CLN3 -> SBF
            MBF -> SBF
            YHP1 -| SBF
            YOX1 -| SBF

            CLN3 -> MBF

            ACE2 -> CLN3
            YHP1 -| CLN3
            SWI5 -> CLN3
            YOX1 -| CLN3
        ",
        )
        .unwrap();
        let graph = AsyncGraph::new(network).unwrap();
        let witness = graph.make_witness(graph.unit_params());
        let witness_string = BooleanNetwork::try_from(
            "
            SSF -> SWI5

            SSF -> ACE2

            SBF -> SSF
            HCM1 -> SSF

            MBF -> YHP1
            SBF -> YHP1

            MBF -> HCM1
            SBF -> HCM1

            MBF -> YOX1
            SBF -> YOX1

            CLN3 -> SBF
            MBF -> SBF
            YHP1 -| SBF
            YOX1 -| SBF

            CLN3 -> MBF

            ACE2 -> CLN3
            YHP1 -| CLN3
            SWI5 -> CLN3
            YOX1 -| CLN3
            $ACE2: SSF
            $CLN3: ACE2 | SWI5 | !YHP1 | !YOX1
            $HCM1: MBF | SBF
            $MBF: CLN3
            $SBF: CLN3 | MBF | !YHP1 | !YOX1
            $SSF: HCM1 | SBF
            $SWI5: SSF
            $YHP1: MBF | SBF
            $YOX1: MBF | SBF
        ",
        )
        .unwrap();

        assert_eq!(witness, witness_string);

        let graph = AsyncGraph::new(witness).unwrap();
        assert_eq!(graph.unit_params().cardinality(), 1.0);
    }
}
