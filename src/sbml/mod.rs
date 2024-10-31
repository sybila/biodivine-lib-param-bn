//!Adds support for SBML-qual import and export to `BooleanNetwork`.

use std::collections::HashMap;

/// Contains code for parsing SBML models using xml-tree library. It is not 100% SBML-qual
/// compliant, but should be good enough for now. Also most code is ready for possible extension
/// to multi-valued models in the future.
pub mod import;

/// A very crude SBML export module. It basically just dumps `BooleanNetwork` into valid XML,
/// but there are some things that could be better checked.
pub mod export;

/// A layout type for transferring information about node position from SBML files.
pub type Layout = HashMap<String, (f64, f64)>;

#[cfg(test)]
mod tests {
    use crate::BooleanNetwork;

    #[test]
    fn test_sbml_extended_support() {
        let model = BooleanNetwork::try_from(
            "\
            $C:(A & g(C, B))
            A -> C
            B -> C
            C -| C
            $A:h(C)
            C -?? A
            $B:f(A, D)
            A -> B
            D -> B
            D -? D
        ",
        )
        .unwrap();
        let (model2, _layout) =
            BooleanNetwork::try_from_sbml(model.to_sbml(None).as_str()).unwrap();
        assert_eq!(
            model.as_graph().find_variable("A"),
            model.as_graph().find_variable("A")
        );
        assert_eq!(
            model.as_graph().find_variable("B"),
            model.as_graph().find_variable("B")
        );
        assert_eq!(
            model.as_graph().find_variable("C"),
            model.as_graph().find_variable("C")
        );
        assert_eq!(
            model.as_graph().find_variable("D"),
            model.as_graph().find_variable("D")
        );

        for s in model.variables() {
            for t in model.variables() {
                assert_eq!(
                    model.as_graph().find_regulation(s, t),
                    model2.as_graph().find_regulation(s, t)
                );
            }
        }

        assert_eq!(model2, model);
    }
}
