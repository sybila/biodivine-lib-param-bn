use crate::RegulatoryGraph;

/// To consider two regulatory graphs equivalent, we generally assume that they have the same
/// number of variables, with the same names, and stored in the same order. Furthermore, they
/// also need to have the same regulations, however, these do not have a specific order that
/// needs to be preserved. The reason why we enforce variable order and not regulation order
/// is that `VariableId` objects should be compatible across equivalent graphs, but there is no
/// `RegulationId` or a similar requirement.
impl PartialEq for RegulatoryGraph {
    fn eq(&self, other: &Self) -> bool {
        if self.variables != other.variables {
            return false;
        }
        // Check that every regulation present in `self` is equivalent in `other`.
        for self_reg in self.regulations() {
            if let Some(other_reg) = other.find_regulation(self_reg.regulator, self_reg.target) {
                if self_reg != other_reg {
                    return false;
                }
            } else {
                return false;
            }
        }

        // And symmetrically that every regulation in `other` is equivalent in `self`.
        for other_reg in other.regulations() {
            if let Some(self_reg) = self.find_regulation(other_reg.regulator, other_reg.target) {
                if self_reg != other_reg {
                    return false;
                }
            } else {
                return false;
            }
        }

        true
    }
}

impl Eq for RegulatoryGraph {}

#[cfg(test)]
mod tests {
    use crate::RegulatoryGraph;

    #[test]
    fn test_regulation_order_equivalence() {
        let mut a = RegulatoryGraph::new(vec!["a".to_string(), "b".to_string()]);
        let mut b = RegulatoryGraph::new(vec!["a".to_string(), "b".to_string()]);

        a.add_string_regulation("a -> b").unwrap();
        a.add_string_regulation("b -| a").unwrap();

        b.add_string_regulation("b -| a").unwrap();
        b.add_string_regulation("a -> b").unwrap();

        assert_eq!(a, b);
    }
}
