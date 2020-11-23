/*
   HOW DOES THIS ALL WORK?

   Warning: This is a prototype. We should definitely work on architectural updates to BDD lib
   which will make this much nicer. Also something something FUTURES! However, that being said...

   We consider the same encoding as in normal AsyncGraph, but we add extra BDD variables
   to represent the variables of the network (we call these state variables). These are added
   AFTER the parameter variables.

   This means that if there are no constraints on the state variables, our BDDs look exactly as
   normal `BddParams`, except their cardinality is higher (since the cardinality algorithm also
   counts state variable valuations). However, we can normalize this...
*/

mod _impl_graph_colored_vertices;
mod _impl_graph_colors;
mod _impl_graph_vertices;
mod _impl_symbolic_async_graph;

use crate::bdd_params::BddParameterEncoder;
use crate::BooleanNetwork;
use biodivine_lib_bdd::{Bdd, BddSatisfyingValuations, BddVariable, BddVariableSet};

/*
   BDDs representing the graph colors. These still contain both state and parameter variables,
   but are only constrained on parameter variables. We thus need a normalization factor to
   account for this.
*/
#[derive(Clone, Eq, PartialEq, Hash)]
pub struct GraphColors {
    bdd: Bdd,
    p_var_count: u16,
}

/*
   BDD representing the $V \times C$ relation (colored vertex set) of a graph. Essentially
   behaves like a relation/set.
*/
#[derive(Clone, Eq, PartialEq, Hash)]
pub struct GraphColoredVertices {
    bdd: Bdd,
    p_var_count: u16,
}

/*
   Bdd representing the graph vertices. This has all parameter variables fixed to zero
   because we need to be able to iterate over it. TODO: This is bad design.
*/
#[derive(Clone, Eq, PartialEq, Hash)]
pub struct GraphVertices {
    bdd: Bdd,
    p_var_count: u16,
}

pub struct GraphVertexIterator<'a, 'b> {
    state_variables: &'a Vec<BddVariable>,
    iterator: BddSatisfyingValuations<'b>,
}

pub struct SymbolicAsyncGraph {
    network: BooleanNetwork,
    pub bdd_variable_set: BddVariableSet,
    state_variables: Vec<BddVariable>,
    /// Number of parameter variables.
    p_var_count: u16,
    empty_color_set: GraphColors,
    unit_color_set: GraphColors,
    empty_set: GraphColoredVertices,
    unit_set: GraphColoredVertices,
    /// For every update function, store !v <=> function (used for pre/post)
    update_functions: Vec<Bdd>,
    function_context: BddParameterEncoder,
}
