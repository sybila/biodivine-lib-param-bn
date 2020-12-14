use crate::Monotonicity::{Activation, Inhibition};
use crate::{Regulation, RegulatoryGraph};
use std::fmt::{Display, Error, Formatter};

impl Display for RegulatoryGraph {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), Error> {
        for r in &self.regulations {
            write!(
                f,
                "{} {} {}\n",
                self.get_variable(r.regulator),
                relationship_string(&r),
                self.get_variable(r.target)
            )?;
        }
        Ok(())
    }
}

fn relationship_string(regulation: &Regulation) -> &str {
    let s = match (regulation.observable, regulation.monotonicity) {
        (true, Some(Activation)) => "->",
        (true, Some(Inhibition)) => "-|",
        (true, None) => "-?",
        (false, Some(Activation)) => "->?",
        (false, Some(Inhibition)) => "-|?",
        (false, None) => "-??",
    };
    return s;
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
