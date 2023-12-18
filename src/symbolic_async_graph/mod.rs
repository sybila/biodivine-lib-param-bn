//! A fully symbolic coloured graph representation of the Asynchronous Boolean Network.
//!
//! Internally, this uses the same type of encoding as "normal" `AsyncGraph`, but it uses
//! extra BDD variables to represent network state variables (note the distinction between
//! state and BDD variables).
//!
//! To the end user, this representation is available via three data structures: `GraphVertices`,
//! `GraphColors` and `GraphColoredVertices`. The first two represent just the subsets of $V$
//! and $C$ respectively, while the last is a full subset of $V \times C$.
//!
//! There is a range of methods that enable (or simplify) the conversion between these three
//! types of sets (mainly provided by `GraphColoredVertices` in the form of projections and
//! vertex-wise operations). Additionally, a `VertexSet` can be iterated with `ArrayBitVectors`
//! used to represent the set elements.
//!
//! The types of conversions and convenience methods are mainly motivated by SCC decomposition
//! algorithms - if we need something else in the future, it will be implemented.
//!
//! `SymbolicAsyncGraph` does not implement the `Graph` trait because it was not useful
//! in the fully symbolic context. It provides `post`, `pre`, and similar methods directly.
//!
//! Internally, the representation is maintained by the `SymbolicContext` which maps each
//! BDD variable either to a state variable of the network, or to a parameter stored in some
//! implicit or explicit `FunctionTable`. The BDD variables are ordered in such a way that
//! the network parameters follow the variable which they are most closely related to, but
//! please do not rely on this ordering, it probably will be changed in the future. Overall,
//! by accessing the `SymbolicContext` (via `SymbolicAsyncGraph`) allows implementing almost
//! any custom BDD operations, but it should be used with caution.
//!

use crate::symbolic_async_graph::projected_iteration::{OwnedRawSymbolicIterator, RawProjection};
use crate::BooleanNetwork;
use biodivine_lib_bdd::{Bdd, BddVariable, BddVariableSet, ValuationsOfClauseIterator};
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
/// **(internal)** Implementation of symbolic utility algorithms.
mod _impl_symbolic_async_graph_algorithm;
/// **(internal)** Implement symbolic graph operators (pre/post/...).
mod _impl_symbolic_async_graph_operators;
/// **(internal)** Implementation of the `SymbolicContext`.
mod _impl_symbolic_context;

/// Implementation of the `RawSymbolicIterator` and other low-level iterators
/// that are used to iterate through various projections of symbolic sets.
pub mod projected_iteration;

pub mod reachability;

/// A module with a trait that describes common methods shared by all set representations
/// based on BDDs.
///
/// These methods should eventually replace code that was previously duplicated across multiple
/// set objects but is kept there for now due to compatibility.
pub(crate) mod bdd_set;

/// Symbolic representation of a color set.
///
/// Implementation contains all symbolic variables, but state variables are unconstrained.
#[derive(Clone, Eq, PartialEq, Hash, Debug)]
pub struct GraphColors {
    pub(crate) bdd: Bdd,
    pub(crate) parameter_variables: Vec<BddVariable>,
}

/// Symbolic representation of a coloured set of graph vertices, i.e. a subset of $V \times C$.
#[derive(Clone, Eq, PartialEq, Hash, Debug)]
pub struct GraphColoredVertices {
    bdd: Bdd,
    state_variables: Vec<BddVariable>,
    parameter_variables: Vec<BddVariable>,
}

/// Symbolic representation of a vertex set.
///
/// Implementation contains all symbolic variables, but parameter variables are unconstrained.
#[derive(Clone, Eq, PartialEq, Hash, Debug)]
pub struct GraphVertices {
    bdd: Bdd,
    state_variables: Vec<BddVariable>,
}

/// A helper struct that we need in order to make `GraphVertices` iterable. Elements of such
/// iterable set are bitvectors, specifically `ArrayBitVector`.
///
/// Internally, this struct contains a `Bdd` that has all parameter variables fixed to false,
/// so that we only iterate over vertices and can safely disregard colors.
///
/// **This object is now deprecated and you can call [GraphVertices::into_iter] directly.**
#[derive(Clone)]
#[deprecated]
pub struct IterableVertices {
    projection: RawProjection,
    state_variables: Vec<BddVariable>,
}

/// Iterator over the states/vertices of a [GraphVertices] set.
pub struct GraphVertexIterator {
    inner_iterator: OwnedRawSymbolicIterator,
    state_variables: Vec<BddVariable>,
}

/// A symbolic encoding of asynchronous transition system of a `BooleanNetwork`.
///
/// Provides standard pre/post operations for exploring the graph symbolically.
#[derive(Clone)]
pub struct SymbolicAsyncGraph {
    // If available, provides the original network that was used to create the graph.
    // We should not rely on the network being available though, as the graph can be created
    // in different ways as well.
    network: Option<BooleanNetwork>,
    symbolic_context: SymbolicContext,
    // Empty and unit vertex set.
    colored_vertex_space: (GraphColoredVertices, GraphColoredVertices),
    // Empty and unit vertex set.
    vertex_space: (GraphVertices, GraphVertices),
    // Empty and unit color set.
    color_space: (GraphColors, GraphColors),
    // General symbolic unit bdd.
    unit_bdd: Bdd,
    // A `Bdd` which stores the exact asynchronous update function `f_i(x)` for
    // each variable `x_i`.
    fn_update: Vec<Bdd>,
    // For every update function, stores `x_i != f_i(x)` (used for pre/post).
    // In other words, this is the symbolic set of states where a transition is enabled.
    fn_transition: Vec<Bdd>,
}

/// Symbolic context manages the mapping between entities of the Boolean network
/// (variables, parameters, uninterpreted functions) and `BddVariables` used in `bdd-lib`.
///
/// It also provides utility methods for creating `Bdd` objects that match different conditions
/// imposed on the parameter space of the network.
///
/// Note that while this is technically public, it should not be used unless absolutely necessary.
/// Playing with raw `BDDs` is dangerous.
#[derive(Clone)]
pub struct SymbolicContext {
    bdd: BddVariableSet,
    // One symbolic variable for each network variable.
    state_variables: Vec<BddVariable>,
    // A (possibly empty) list of extra symbolic variables for each network variable.
    extra_state_variables: Vec<Vec<BddVariable>>,
    // The same variables as above, but in one list (some operations only need this representation
    // and it could take us some time to compute it for large models).
    all_extra_state_variables: Vec<BddVariable>,
    // All symbolic variables representing parameters. The association between
    // variables and parameters is then managed by `FunctionTable` objects below.
    parameter_variables: Vec<BddVariable>,
    explicit_function_tables: Vec<FunctionTable>,
    implicit_function_tables: Vec<Option<FunctionTable>>,
}

/// Function table maps one the table of an uninterpreted function to corresponding `Bdd` variables.
///
/// The main functionality of a `FunctionTable` is that it provides an iterator over
/// pairs of `Vec<bool>` (function input assignment) and `BddVariable`
/// (corresponding symbolic variable).
#[derive(Debug, Clone)]
pub struct FunctionTable {
    pub arity: u16,
    rows: Vec<BddVariable>,
}

/// Iterator over elements of the `FunctionTable`.
pub struct FunctionTableIterator<'a> {
    inner_iterator: Enumerate<ValuationsOfClauseIterator>,
    table: &'a FunctionTable,
}

/// A helper structure which provides a collection of static functions that can be used
/// to analyse static constraints of Boolean functions.
pub struct RegulationConstraint {
    _impossible: (), // Ensures `RegulationConstraint` cannot be instantiated.
}

#[cfg(test)]
mod tests {
    use crate::biodivine_std::traits::Set;
    use crate::symbolic_async_graph::{GraphColoredVertices, SymbolicAsyncGraph};
    use crate::BooleanNetwork;
    use std::convert::TryFrom;

    #[test]
    fn components() {
        fn fwd(graph: &SymbolicAsyncGraph, initial: &GraphColoredVertices) -> GraphColoredVertices {
            let mut result = initial.clone();
            loop {
                let post = graph.post(&result);
                if post.is_subset(&result) {
                    return result;
                } else {
                    result = result.union(&post);
                }
            }
        }
        fn bwd(graph: &SymbolicAsyncGraph, initial: &GraphColoredVertices) -> GraphColoredVertices {
            let mut result = initial.clone();
            loop {
                let post = graph.pre(&result);
                if post.is_subset(&result) {
                    return result;
                } else {
                    result = result.union(&post);
                }
            }
        }
        fn scc(graph: &SymbolicAsyncGraph) -> Vec<GraphColoredVertices> {
            let mut universe = graph.mk_unit_colored_vertices();
            let mut components = Vec::new();
            while !universe.is_empty() {
                // Pick one vertex in universe for every color in universe
                let pivots = universe.pick_vertex();
                let fwd = fwd(graph, &pivots);
                let bwd = bwd(graph, &pivots);
                let scc = fwd.intersect(&bwd);
                universe = universe.minus(&scc);
                components.push(scc);
            }
            return components;
        }
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
        let stg = SymbolicAsyncGraph::new(&bn).unwrap();
        let components = scc(&stg);
        assert_eq!(7, components.len());
        assert_eq!(2.0, components[0].vertices().approx_cardinality());
        assert_eq!(1.0, components[1].vertices().approx_cardinality());
        assert_eq!(2.0, components[2].vertices().approx_cardinality());
        assert_eq!(1.0, components[3].vertices().approx_cardinality());
        assert_eq!(2.0, components[4].vertices().approx_cardinality());
        assert_eq!(2.0, components[5].vertices().approx_cardinality());
        assert_eq!(1.0, components[6].vertices().approx_cardinality());
    }
}
