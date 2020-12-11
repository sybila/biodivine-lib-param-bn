use crate::symbolic_async_graph::{FunctionTable, FunctionTableIterator, SymbolicFunctionContext};
use crate::{BinaryOp, BooleanNetwork, FnUpdate, ParameterId, VariableId};
use biodivine_lib_bdd::{
    bdd, Bdd, BddValuation, BddValuationIterator, BddVariable, BddVariableSetBuilder,
};

impl SymbolicFunctionContext {
    pub fn new(network: &BooleanNetwork) -> SymbolicFunctionContext {
        let mut builder = BddVariableSetBuilder::new();

        let state_variables: Vec<BddVariable> = network
            .graph
            .variable_ids()
            .map(|v| {
                let variable = network.graph.get_variable(v);
                builder.make_variable(&variable.name)
            })
            .collect();

        let implicit_function_tables: Vec<Option<FunctionTable>> = network
            .graph
            .variable_ids()
            .map(|v| {
                let has_implicit_function = network.get_update_function(v).is_none();
                if has_implicit_function {
                    let arity = network.graph.regulators(v).len();
                    let variable = network.graph.get_variable(v);
                    if arity > (u16::MAX as usize) {
                        panic!("Variable {} has too many regulators.", variable.name);
                    }
                    let function_table = FunctionTable::new(
                        format!("f_{}", variable.name).as_str(),
                        arity as u16,
                        &mut builder,
                    );
                    Some(function_table)
                } else {
                    None
                }
            })
            .collect();

        let explicit_function_tables: Vec<FunctionTable> = network
            .parameters
            .iter()
            .map(|p| {
                if p.cardinality > (u16::MAX as usize) {
                    panic!("Parameter {} has too many arguments.", p.name);
                }
                FunctionTable::new(&p.name, p.cardinality as u16, &mut builder)
            })
            .collect();

        let mut parameter_variables = Vec::new();
        for table in &explicit_function_tables {
            for p in &table.rows {
                parameter_variables.push(*p);
            }
        }
        for table in &implicit_function_tables {
            if let Some(table) = table {
                for p in &table.rows {
                    parameter_variables.push(*p);
                }
            }
        }

        SymbolicFunctionContext {
            bdd: builder.build(),
            p_var_count: parameter_variables.len() as u16,
            state_variables,
            parameter_variables,
            explicit_function_tables,
            implicit_function_tables,
        }
    }

    pub fn mk_constant(&self, value: bool) -> Bdd {
        if value {
            self.bdd.mk_true()
        } else {
            self.bdd.mk_false()
        }
    }

    pub fn true_when_variable(&self, variable: VariableId) -> Bdd {
        self.bdd.mk_var(self.state_variables[variable.0])
    }

    pub fn true_when_parameter(&self, parameter: ParameterId, args: &Vec<VariableId>) -> Bdd {
        let table = &self.explicit_function_tables[parameter.0];
        let args: Vec<Bdd> = args.iter().map(|v| self.true_when_variable(*v)).collect();
        self.true_when_unknown_function(table, &args)
    }

    pub fn true_when_implicit_parameter(&self, variable: VariableId, args: Vec<VariableId>) -> Bdd {
        let table = &self.implicit_function_tables[variable.0];
        let table = table.as_ref().unwrap_or_else(|| {
            panic!("Variable {:?} does not have an implicit update function.");
        });
        let args: Vec<Bdd> = args.iter().map(|v| self.true_when_variable(*v)).collect();
        self.true_when_unknown_function(table, &args)
    }

    pub fn true_when_function(&self, function: &FnUpdate) -> Bdd {
        match function {
            FnUpdate::Const(value) => self.mk_constant(*value),
            FnUpdate::Var(id) => self.true_when_variable(*id),
            FnUpdate::Not(inner) => self.true_when_function(inner).not(),
            FnUpdate::Param(id, args) => self.true_when_parameter(*id, args),
            FnUpdate::Binary(op, left, right) => {
                let l = self.true_when_function(left);
                let r = self.true_when_function(right);
                match op {
                    BinaryOp::And => l.and(&r),
                    BinaryOp::Or => l.or(&r),
                    BinaryOp::Xor => l.xor(&r),
                    BinaryOp::Imp => l.imp(&r),
                    BinaryOp::Iff => l.iff(&r),
                }
            }
        }
    }

    // Note that this actually allows functions which do not have just variables as arguments...
    // In the future we can use this to build truly universal system.
    fn true_when_unknown_function(&self, function_table: &FunctionTable, args: &Vec<Bdd>) -> Bdd {
        let mut result = self.bdd.mk_true();
        for (inputs, output) in function_table {
            let input_bdd = inputs
                .iter()
                .zip(args)
                .map(|(v, b)| if *v { b.clone() } else { b.not() })
                .fold(self.bdd.mk_true(), |a, b| a.and(&b));
            let output_bdd = self.bdd.mk_var(output);
            result = bdd![result & (input_bdd => output_bdd)];
        }
        result
    }

    fn unknown_function_instantiation(
        &self,
        valuation: &BddValuation,
        function_table: &FunctionTable,
        args: &Vec<Bdd>,
    ) -> Bdd {
        let mut result = self.bdd.mk_false();
        for (inputs, output) in function_table {
            if valuation.value(output) {
                let input_bdd = inputs
                    .iter()
                    .zip(args)
                    .map(|(v, b)| if *v { b.clone() } else { b.not() })
                    .fold(self.bdd.mk_true(), |a, b| a.and(&b));
                result = bdd![result | input_bdd];
            }
        }
        result
    }

    pub fn implicit_parameter_instantiation(
        &self,
        valuation: &BddValuation,
        variable: VariableId,
        args: &Vec<VariableId>,
    ) -> Bdd {
        let table = &self.implicit_function_tables[variable.0];
        let table = table.as_ref().unwrap_or_else(|| {
            panic!("Variable {:?} does not have an implicit update function.");
        });
        let args: Vec<Bdd> = args.iter().map(|v| self.true_when_variable(*v)).collect();
        self.unknown_function_instantiation(valuation, table, &args)
    }

    fn parameter_instantiation(
        &self,
        valuation: &BddValuation,
        parameter: ParameterId,
        args: &Vec<VariableId>,
    ) -> Bdd {
        let table = &self.explicit_function_tables[parameter.0];
        let args: Vec<Bdd> = args.iter().map(|v| self.true_when_variable(*v)).collect();
        self.unknown_function_instantiation(valuation, table, &args)
    }

    pub fn function_instantiation(&self, valuation: &BddValuation, function: &FnUpdate) -> Bdd {
        match function {
            FnUpdate::Const(value) => self.mk_constant(*value),
            FnUpdate::Var(id) => self.true_when_variable(*id),
            FnUpdate::Not(inner) => self.function_instantiation(valuation, inner).not(),
            FnUpdate::Param(id, args) => self.parameter_instantiation(valuation, *id, args),
            FnUpdate::Binary(op, left, right) => {
                let l = self.function_instantiation(valuation, left);
                let r = self.function_instantiation(valuation, right);
                match op {
                    BinaryOp::And => l.and(&r),
                    BinaryOp::Or => l.or(&r),
                    BinaryOp::Xor => l.xor(&r),
                    BinaryOp::Imp => l.imp(&r),
                    BinaryOp::Iff => l.iff(&r),
                }
            }
        }
    }
}

impl FunctionTable {
    pub fn new(name: &str, arity: u16, bdd_builder: &mut BddVariableSetBuilder) -> FunctionTable {
        let rows: Vec<BddVariable> = BddValuationIterator::new(arity)
            .map(|arg_valuation| {
                let bdd_var_name = format!("{}{}", name, arg_valuation);
                bdd_builder.make_variable(bdd_var_name.as_str())
            })
            .collect();
        FunctionTable { arity, rows }
    }
}

impl<'a> IntoIterator for &'a FunctionTable {
    type Item = (Vec<bool>, BddVariable);
    type IntoIter = FunctionTableIterator<'a>;

    fn into_iter(self) -> Self::IntoIter {
        FunctionTableIterator::new(self)
    }
}

impl FunctionTableIterator<'_> {
    pub fn new(table: &FunctionTable) -> FunctionTableIterator {
        FunctionTableIterator {
            table,
            inner_iterator: BddValuationIterator::new(table.arity).enumerate(),
        }
    }
}

impl Iterator for FunctionTableIterator<'_> {
    type Item = (Vec<bool>, BddVariable);

    fn next(&mut self) -> Option<Self::Item> {
        if let Some((index, valuation)) = self.inner_iterator.next() {
            Some((valuation.vector(), self.table.rows[index]))
        } else {
            None
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::symbolic_async_graph::SymbolicAsyncGraph;
    use crate::BooleanNetwork;
    use std::convert::TryFrom;

    #[test]
    fn hmox_pathway() {
        let model = std::fs::read_to_string("aeon_models/hmox_pathway.aeon").unwrap();
        let network = BooleanNetwork::try_from(model.as_str()).unwrap();
        println!("Variables: {}", network.graph.num_vars());
        let graph = SymbolicAsyncGraph::new(network).unwrap();
        assert!(!graph.unit_vertices().is_empty());
    }
}
