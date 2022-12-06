use crate::{Monotonicity, RegulatoryGraph};
use std::io::Write;

impl RegulatoryGraph {
    /// Export this regulatory graph to a `.dot` format.
    ///
    /// In the representation, we use red and green color to distinguish positive and negative
    /// regulations. Dashed edges show regulations without observability requirement.
    pub fn to_dot(&self) -> String {
        let mut buffer: Vec<u8> = Vec::new();
        self.write_as_dot(&mut buffer)
            .expect("I/O error converting `RegulatoryGraph` to `.dot`.");
        String::from_utf8(buffer).expect("Invalid UTF formatting in .dot string.")
    }

    pub fn write_as_dot(&self, output: &mut dyn Write) -> Result<(), std::io::Error> {
        writeln!(output, "digraph G {{")?;
        for var in self.variables() {
            let name = self.get_variable_name(var);
            writeln!(
                output,
                "v{} [shape=box, label=\"{}\", style=filled];",
                var.0, name
            )?;
        }
        for reg in self.regulations() {
            let line = match reg.observable {
                true => "filled",
                false => "dashed",
            };
            let color = match reg.monotonicity {
                Some(Monotonicity::Activation) => "#4abd73",
                Some(Monotonicity::Inhibition) => "#d05d5d",
                None => "#797979",
            };
            let arrow = match reg.monotonicity {
                Some(Monotonicity::Activation) => "normal",
                Some(Monotonicity::Inhibition) => "tee",
                None => "empty",
            };
            writeln!(
                output,
                "v{} -> v{} [style=\"{}\", color=\"{}\", arrowhead=\"{}\"];",
                reg.regulator.0, reg.target.0, line, color, arrow,
            )?;
        }
        writeln!(output, "}}")?;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use crate::RegulatoryGraph;

    #[test]
    pub fn test_regulatory_graph_to_dot() {
        let mut rg = RegulatoryGraph::new(vec!["a".to_string(), "b".to_string(), "c".to_string()]);

        rg.add_string_regulation("a -?? a").unwrap();
        rg.add_string_regulation("a -> b").unwrap();
        rg.add_string_regulation("b -| c").unwrap();
        rg.add_string_regulation("c ->? a").unwrap();
        rg.add_string_regulation("a -|? c").unwrap();
        rg.add_string_regulation("b -? b").unwrap();

        println!("{}", rg.to_dot());
    }
}
