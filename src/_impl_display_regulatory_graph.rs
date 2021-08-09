use crate::RegulatoryGraph;
use std::fmt::{Display, Error, Formatter};

impl Display for RegulatoryGraph {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), Error> {
        for r in &self.regulations {
            writeln!(f, "{}", r.to_string(self))?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use crate::RegulatoryGraph;
    use std::convert::TryFrom;

    #[test]
    fn test_regulatory_graph_to_string() {
        let graph_string = "a -> b\na ->? a\nb -| b\nb -|? a\nc -?? a\na -? c\n";
        let rg = RegulatoryGraph::try_from(graph_string).unwrap();
        assert_eq!(graph_string, rg.to_string());
    }
}
