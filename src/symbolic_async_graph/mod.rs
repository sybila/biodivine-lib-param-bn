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

use crate::BooleanNetwork;
use biodivine_lib_bdd::{
    Bdd, BddSatisfyingValuations, BddValuationIterator, BddVariable, BddVariableSet,
};
use std::iter::Enumerate;

/// **(internal)** Implementing conversion between `FnUpdate` and `BooleanExpression`.
mod _impl_fn_update_from_boolean_expression;
/// **(internal)** Implementation for `FunctionTable` and `FunctionTableIterator`.
mod _impl_function_table;
/// **(internal)** Implement set operations for `GraphColoredVertices`.
mod _impl_graph_colored_vertices;
/// **(internal)** Implement set operations for `GraphColors`.
mod _impl_graph_colors;
/// **(internal)** Implement set operations for `GraphVertices`.
mod _impl_graph_vertices;
/// **(internal)** Utility methods for validation of static constraints on network regulations.
mod _impl_regulation_constraint;
/// **(internal)** Utility methods for `SymbolicAsyncGraph`.
mod _impl_symbolic_async_graph;
/// **(internal)** Implement symbolic graph operators (pre/post/...).
mod _impl_symbolic_async_graph_operators;
/// **(internal)** Implementation of the `SymbolicContext`.
mod _impl_symbolic_context;

/// Symbolic representation of a color set.
///
/// Implementation contains all symbolic variables, but state variables are unconstrained.
#[derive(Clone, Eq, PartialEq, Hash)]
pub struct GraphColors {
    bdd: Bdd,
    parameter_variables: Vec<BddVariable>,
}

/// Symbolic representation of a coloured set of graph vertices, i.e. a subset of $V \times C$.
#[derive(Clone, Eq, PartialEq, Hash)]
pub struct GraphColoredVertices {
    bdd: Bdd,
    state_variables: Vec<BddVariable>,
    parameter_variables: Vec<BddVariable>,
}

/// Symbolic representation of a vertex set.
///
/// Implementation contains all symbolic variables, but parameter variables are unconstrained.
#[derive(Clone, Eq, PartialEq, Hash)]
pub struct GraphVertices {
    bdd: Bdd,
    state_variables: Vec<BddVariable>,
}

/// A helper struct that we need in order to make `GraphVertices` iterable. Elements of such
/// iterable set are bitvectors, specifically `ArrayBitVector`.
///
/// Internally, this struct contains a `Bdd` that has all parameter variables fixed to false,
/// so that we only iterate over vertices and can safely disregard colors.
pub struct IterableVertices {
    materialized_bdd: Bdd,
    state_variables: Vec<BddVariable>,
}

/// Iterator over graph vertices.
pub struct GraphVertexIterator<'a> {
    iterator: BddSatisfyingValuations<'a>,
    state_variables: Vec<BddVariable>,
}

/// A symbolic encoding of asynchronous transition system of a `BooleanNetwork`.
///
/// Provides standard pre/post operations for exploring the graph symbolically.
pub struct SymbolicAsyncGraph {
    network: BooleanNetwork,
    symbolic_context: SymbolicContext,
    // Empty and unit vertex set.
    vertex_space: (GraphColoredVertices, GraphColoredVertices),
    // Empty and unit color set.
    color_space: (GraphColors, GraphColors),
    // General symbolic unit bdd.
    unit_bdd: Bdd,
    // For every update function, store !v <=> function (used for pre/post)
    update_functions: Vec<Bdd>,
}

/// **(internal)** Symbolic context manages the mapping between entities of the Boolean network
/// (variables, parameters, uninterpreted functions) and `BddVariables` used in `bdd-lib`.
///
/// It also provides utility methods for creating `Bdd` objects that match different conditions
/// imposed on the parameter space of the network.
///
/// Note that while this is technically public, it should not be used unless absolutely necessary.
/// Playing with raw `Bdds` is dangerous.
pub struct SymbolicContext {
    bdd: BddVariableSet,
    state_variables: Vec<BddVariable>,
    parameter_variables: Vec<BddVariable>,
    explicit_function_tables: Vec<FunctionTable>,
    implicit_function_tables: Vec<Option<FunctionTable>>,
}

/// **(internal)** Function table maps one the table of an uninterpreted function to corresponding
/// `Bdd`  variables.
///
/// The main functionality of a `FunctionTable` is that it provides an iterator over
/// pairs of `Vec<bool>` (function input assignment) and `BddVariable`
/// (corresponding symbolic variable).
#[derive(Debug, Clone)]
struct FunctionTable {
    pub arity: u16,
    rows: Vec<BddVariable>,
}

/// **(internal)** Iterator over elements of the `FunctionTable`.
struct FunctionTableIterator<'a> {
    inner_iterator: Enumerate<BddValuationIterator>,
    table: &'a FunctionTable,
}
