use crate::symbolic_async_graph::{FunctionTable, FunctionTableIterator};
use biodivine_lib_bdd::{BddVariable, BddVariableSetBuilder, ValuationsOfClauseIterator};

impl FunctionTable {
    /// Construct a new `FunctionTable`, registering each row of the table as `BddVariable` in
    /// the given `bdd_builder`.
    ///
    /// The `name` is necessary to give some semantic names to the
    /// symbolic variables.
    pub fn new(name: &str, arity: u16, bdd_builder: &mut BddVariableSetBuilder) -> FunctionTable {
        let rows: Vec<BddVariable> = ValuationsOfClauseIterator::new_unconstrained(arity)
            .map(|arg_valuation| {
                let bdd_var_name = format!("{}{}", name, arg_valuation);
                bdd_builder.make_variable(bdd_var_name.as_str())
            })
            .collect();
        let name = name.to_string();
        FunctionTable { arity, rows, name }
    }

    /// List the symbolic variables that appear in this function table.
    ///
    /// Note that you can use `FunctionTable::into_iter` to list the variables with their
    /// corresponding input vectors. This is just for cases where you need the variables but
    /// don't care about their input valuations.
    pub fn symbolic_variables(&self) -> &Vec<BddVariable> {
        &self.rows
    }

    /// True if this [FunctionTable] contains the provided [BddVariable].
    pub fn contains(&self, var: BddVariable) -> bool {
        self.rows.contains(&var)
    }
}

/// Converts a `FunctionTable` into an iterator of `Vec<bool>` (function table row) and
/// `BddVariable` (corresponding symbolic variable).
impl<'a> IntoIterator for &'a FunctionTable {
    type Item = (Vec<bool>, BddVariable);
    type IntoIter = FunctionTableIterator<'a>;

    fn into_iter(self) -> Self::IntoIter {
        FunctionTableIterator::new(self)
    }
}

impl FunctionTableIterator<'_> {
    /// Create a new `FunctionTableIterator` for a given `FunctionTable`.
    pub fn new(table: &FunctionTable) -> FunctionTableIterator {
        FunctionTableIterator {
            table,
            inner_iterator: ValuationsOfClauseIterator::new_unconstrained(table.arity).enumerate(),
        }
    }
}

/// Iterator implementation for the `FunctionTableIterator`.
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
    use crate::symbolic_async_graph::FunctionTable;
    use biodivine_lib_bdd::{BddVariable, BddVariableSetBuilder};

    #[test]
    fn test_function_table() {
        let mut builder = BddVariableSetBuilder::new();
        let table = FunctionTable::new("test", 3, &mut builder);
        let bdd = builder.build();
        let bdd_variables = bdd.variables();
        let table_variables: Vec<BddVariable> = table.into_iter().map(|(_, v)| v).collect();
        assert_eq!(bdd_variables, table_variables);
        assert_eq!(8, table_variables.len());
    }
}
