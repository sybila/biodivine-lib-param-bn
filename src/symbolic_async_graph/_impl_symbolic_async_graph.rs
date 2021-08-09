use crate::biodivine_std::bitvector::{ArrayBitVector, BitVector};
use crate::biodivine_std::traits::Set;
use crate::symbolic_async_graph::_impl_regulation_constraint::apply_regulation_constraints;
use crate::symbolic_async_graph::{
    GraphColoredVertices, GraphColors, SymbolicAsyncGraph, SymbolicContext,
};
use crate::{BooleanNetwork, FnUpdate, VariableId};
use biodivine_lib_bdd::{bdd, BddVariable};

impl SymbolicAsyncGraph {
    pub fn new(network: BooleanNetwork) -> Result<SymbolicAsyncGraph, String> {
        let context = SymbolicContext::new(&network)?;
        let unit_bdd = apply_regulation_constraints(context.bdd.mk_true(), &network, &context)?;

        // For each variable, pre-compute contexts where the update function can be applied, i.e.
        // (F = 1 & var = 0) | (F = 0 & var = 1)
        let update_functions = network
            .graph
            .variables()
            .map(|variable| {
                let regulators = network.regulators(variable);
                let function_is_one = network
                    .get_update_function(variable)
                    .as_ref()
                    .map(|fun| context.mk_fn_update_true(fun))
                    .unwrap_or_else(|| context.mk_implicit_function_is_true(variable, &regulators));
                let variable_is_zero = context.mk_state_variable_is_true(variable).not();
                bdd!(variable_is_zero <=> function_is_one)
            })
            .collect();

        Ok(SymbolicAsyncGraph {
            vertex_space: (
                GraphColoredVertices::new(context.bdd.mk_false(), &context),
                GraphColoredVertices::new(unit_bdd.clone(), &context),
            ),
            color_space: (
                GraphColors::new(context.bdd.mk_false(), &context),
                GraphColors::new(unit_bdd.clone(), &context),
            ),
            symbolic_context: context,
            unit_bdd,
            network,
            update_functions,
        })
    }
}

/// Examine the general properties of the graph.
impl SymbolicAsyncGraph {
    /// Return a reference to the original Boolean network.
    pub fn as_network(&self) -> &BooleanNetwork {
        &self.network
    }

    /// Return a reference to the symbolic context of this graph.
    pub fn symbolic_context(&self) -> &SymbolicContext {
        &self.symbolic_context
    }

    /// Create a colored vertex set with a fixed value of the given variable.
    pub fn fix_network_variable(&self, variable: VariableId, value: bool) -> GraphColoredVertices {
        let bdd_variable = self.symbolic_context.state_variables[variable.0];
        GraphColoredVertices::new(
            self.unit_bdd.var_select(bdd_variable, value),
            &self.symbolic_context,
        )
    }

    /// Make a witness network for one color in the given set.
    pub fn pick_witness(&self, colors: &GraphColors) -> BooleanNetwork {
        if colors.is_empty() {
            panic!("Cannot create witness for empty color set.");
        }
        let witness_valuation = colors.bdd.sat_witness().unwrap();
        let mut witness = self.network.clone();
        for variable in witness.graph.variables() {
            if let Some(function) = &mut witness.update_functions[variable.0] {
                let instantiated_expression = self
                    .symbolic_context
                    .instantiate_fn_update(&witness_valuation, function)
                    .to_boolean_expression(&self.symbolic_context.bdd);
                *function =
                    FnUpdate::try_from_expression(instantiated_expression, self.network.as_graph())
                        .unwrap();
            } else {
                let regulators = self.network.regulators(variable);
                let instantiated_expression = self
                    .symbolic_context
                    .instantiate_implicit_function(&witness_valuation, variable, &regulators)
                    .to_boolean_expression(&self.symbolic_context.bdd);
                let instantiated_fn_update =
                    FnUpdate::try_from_expression(instantiated_expression, self.network.as_graph());
                witness.update_functions[variable.0] = instantiated_fn_update;
            }
        }
        // Remove all explicit parameters since they have been eliminated.
        witness.parameters.clear();
        witness.parameter_to_index.clear();
        witness
    }

    /// Reference to an empty color set.
    pub fn empty_colors(&self) -> &GraphColors {
        &self.color_space.0
    }

    /// Make a new copy of empty color set.
    pub fn mk_empty_colors(&self) -> GraphColors {
        self.color_space.0.clone()
    }

    /// Reference to a unit color set.
    pub fn unit_colors(&self) -> &GraphColors {
        &self.color_space.1
    }

    /// Make a new copy of unit color set.
    pub fn mk_unit_colors(&self) -> GraphColors {
        self.color_space.1.clone()
    }

    /// Reference to an empty colored vertex set.
    pub fn empty_vertices(&self) -> &GraphColoredVertices {
        &self.vertex_space.0
    }

    /// Make a new copy of empty vertex set.
    pub fn mk_empty_vertices(&self) -> GraphColoredVertices {
        self.vertex_space.0.clone()
    }

    /// Reference to a unit colored vertex set.
    pub fn unit_colored_vertices(&self) -> &GraphColoredVertices {
        &self.vertex_space.1
    }

    /// Make a new copy of unit vertex set.
    pub fn mk_unit_colored_vertices(&self) -> GraphColoredVertices {
        self.vertex_space.1.clone()
    }

    /// Construct a vertex set that only contains one vertex, but all colors
    pub fn vertex(&self, state: &ArrayBitVector) -> GraphColoredVertices {
        let partial_valuation: Vec<(BddVariable, bool)> = state
            .values()
            .into_iter()
            .enumerate()
            .map(|(i, v)| (self.symbolic_context.state_variables[i], v))
            .collect();
        GraphColoredVertices::new(
            self.unit_bdd.select(&partial_valuation),
            &self.symbolic_context,
        )
    }
}

#[cfg(test)]
mod tests {
    use crate::biodivine_std::bitvector::BitVector;
    use crate::biodivine_std::traits::Set;
    use crate::symbolic_async_graph::SymbolicAsyncGraph;
    use crate::BooleanNetwork;
    use std::convert::TryFrom;

    #[test]
    fn test_constraints_1() {
        let network = BooleanNetwork::try_from("a -> t \n $a: true").unwrap();
        let graph = SymbolicAsyncGraph::new(network).unwrap();
        assert_eq!(1.0, graph.unit_colors().approx_cardinality());
        let network = BooleanNetwork::try_from("a -| t \n $a: true").unwrap();
        let graph = SymbolicAsyncGraph::new(network).unwrap();
        assert_eq!(1.0, graph.unit_colors().approx_cardinality());
        let network = BooleanNetwork::try_from("a ->? t \n $a: true").unwrap();
        let graph = SymbolicAsyncGraph::new(network).unwrap();
        assert_eq!(3.0, graph.unit_colors().approx_cardinality());
        let network = BooleanNetwork::try_from("a -|? t \n $a: true").unwrap();
        let graph = SymbolicAsyncGraph::new(network).unwrap();
        assert_eq!(3.0, graph.unit_colors().approx_cardinality());
        let network = BooleanNetwork::try_from("a -? t \n $a: true").unwrap();
        let graph = SymbolicAsyncGraph::new(network).unwrap();
        assert_eq!(2.0, graph.unit_colors().approx_cardinality());
        let network = BooleanNetwork::try_from("a -?? t \n $a: true").unwrap();
        let graph = SymbolicAsyncGraph::new(network).unwrap();
        assert_eq!(4.0, graph.unit_colors().approx_cardinality());
    }

    #[test]
    fn test_constraints_2() {
        /*        a&!b a  a|!b
           a b | f_1 f_2 f_3
           0 0 |  0   0   1
           0 1 |  0   0   0
           1 0 |  1   1   1
           1 1 |  0   1   1
        */
        let network = "
            a -> t \n b -|? t
            $a: true \n $b: true
        ";
        let network = BooleanNetwork::try_from(network).unwrap();
        let graph = SymbolicAsyncGraph::new(network).unwrap();
        assert_eq!(3.0, graph.unit_colors().approx_cardinality());
    }

    /* For a monotonous function, the cardinality should follow dedekind numbers... */

    #[test]
    fn test_monotonicity_2() {
        let network = "
            a ->? t \n b -|? t
            $a: true \n $b: true
        ";
        let network = BooleanNetwork::try_from(network).unwrap();
        let graph = SymbolicAsyncGraph::new(network).unwrap();
        assert_eq!(6.0, graph.unit_colors().approx_cardinality());
    }

    #[test]
    fn test_monotonicity_3() {
        let network = "
            a ->? t \n b -|? t \n c ->? t
            $a: true \n $b: true \n $c: true
        ";
        let network = BooleanNetwork::try_from(network).unwrap();
        let graph = SymbolicAsyncGraph::new(network).unwrap();
        assert_eq!(20.0, graph.unit_colors().approx_cardinality());
    }

    #[test]
    fn test_monotonicity_4() {
        let network = "
            a ->? t \n b -|? t \n c ->? t \n d -|? t
            $a: true \n $b: true \n $c: true \n $d: true
        ";
        let network = BooleanNetwork::try_from(network).unwrap();
        let graph = SymbolicAsyncGraph::new(network).unwrap();
        assert_eq!(168.0, graph.unit_colors().approx_cardinality());
    }

    #[test]
    fn test_invalid_function() {
        let network = "
            a -> t \n b -| t \n
            $a: true \n $b: true \n $t: b
        ";
        let network = BooleanNetwork::try_from(network).unwrap();
        let graph = SymbolicAsyncGraph::new(network);
        assert!(graph.is_err());
    }

    /*
        This is essentially a copy paste from the tutorial, but for some reason code coverage
        does not count documentation tests, so let's make a copy here!
    */
    #[test]
    fn basic_test() {
        // Boolean network from the previous tutorial:
        let bn = BooleanNetwork::try_from(
            r"
            A -> B
            C -|? B
            $B: A
            C -> A
            B -> A
            A -| A
            $A: C | f(A, B)
        ",
        )
        .unwrap();
        let stg = SymbolicAsyncGraph::new(bn).unwrap();
        assert_eq!(32.0, stg.unit_colored_vertices().approx_cardinality());
        assert_eq!(
            8.0,
            stg.unit_colored_vertices().vertices().approx_cardinality()
        );
        assert_eq!(
            4.0,
            stg.unit_colored_vertices().colors().approx_cardinality()
        );
        assert!(stg.empty_vertices().is_empty());
        assert!(stg.mk_empty_colors().is_empty());
        assert_eq!(stg.mk_unit_colors(), stg.unit_colored_vertices().colors());
        assert_eq!(3, stg.as_network().num_vars());

        let id_a = stg.as_network().as_graph().find_variable("A").unwrap();
        stg.fix_network_variable(id_a, true);
        let witness = stg.pick_witness(stg.unit_colors());
        assert_eq!(0, witness.parameters().count());

        for vertex in stg.unit_colored_vertices().vertices().materialize().iter() {
            println!(
                "Value of A in state {:?} is {}",
                vertex,
                vertex.get(id_a.into())
            );
            let singleton = stg.vertex(&vertex);
            assert_eq!(4.0, singleton.approx_cardinality());
            assert_eq!(1.0, singleton.vertices().approx_cardinality());
        }

        let one_color = stg.unit_colors().pick_singleton();
        assert_eq!(1.0, one_color.approx_cardinality());
        assert_eq!(
            4.0,
            stg.unit_colored_vertices()
                .pick_vertex()
                .approx_cardinality()
        );
        assert_eq!(
            8.0,
            stg.unit_colored_vertices()
                .pick_color()
                .approx_cardinality()
        );
    }
}
