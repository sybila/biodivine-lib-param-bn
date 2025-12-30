//! A library for analysis of Boolean networks. As of now, the library supports:
//!  - Regulatory graphs with monotonicity and observability constraints.
//!  - Boolean networks, possibly with partially unknown and parametrised update functions.
//!  - Full SBML-qual support for import/export as well as custom string format `.aeon`.
//!  - Fully symbolic asynchronous state-space generator using BDDs (great overall performance).
//!  - Semi-symbolic state-space generator, using BDDs used only for the network parameters
//!    (allows state-level parallelism for smaller networks).
//!
//! For a quick introduction to Boolean networks and their symbolic manipulation, you can
//! check out our [tutorial module](./tutorial/index.html).
//!
#[macro_use]
extern crate lazy_static;
extern crate core;

use regex::Regex;
use std::collections::HashMap;
use std::iter::Map;
use std::ops::Range;

pub mod biodivine_std;
pub mod fixed_points;
pub mod sbml;
#[cfg(feature = "solver-z3")]
pub mod solver_context;
pub mod symbolic_async_graph;
pub mod trap_spaces;
pub mod tutorial;

/// **(internal)** Implements `.aeon` parser for `BooleanNetwork` and `RegulatoryGraph` objects.
mod _aeon_parser;
/// **(internal)** Methods for manipulating `ModelAnnotation` objects.
mod _impl_annotations;
/// **(internal)** Utility methods for `BinaryOp`.
mod _impl_binary_op;
/// **(internal)** Utility methods for `BooleanNetwork`.
mod _impl_boolean_network;
/// **(internal)** `BooleanNetwork` to `.aeon` string.
mod _impl_boolean_network_display;
/// **(internal)** Implements experimental `.bnet` parser for `BooleanNetwork`.
mod _impl_boolean_network_from_bnet;
/// **(internal)** Implements an experimental `.bnet` writer for `BooleanNetwork`.
mod _impl_boolean_network_to_bnet;
/// **(internal)** All methods implemented by the `ExtendedBoolean` object.
mod _impl_extended_boolean;
/// **(internal)** Utility methods for `FnUpdate`.
mod _impl_fn_update;
/// **(internal)** Utility methods for `Parameter`.
mod _impl_parameter;
/// **(internal)** Utility methods for `ParameterId`.
mod _impl_parameter_id;
/// **(internal)** Utility methods for `Regulation`.
mod _impl_regulation;
/// **(internal)** All methods for analysing and manipulating `RegulatoryGraph`.
mod _impl_regulatory_graph;
/// **(internal)** All methods implemented by the `Space` object.
mod _impl_space;
/// **(internal)** Utility methods for `Variable`.
mod _impl_variable;
/// **(internal)** Utility methods for `VariableId`.
mod _impl_variable_id;

// Re-export data structures used for advanced graph algorithms on `RegulatoryGraph`.
pub use _impl_regulatory_graph::signed_directed_graph::SdGraph;
pub use _impl_regulatory_graph::signed_directed_graph::Sign;

/// **(internal)** A regex string of an identifier which we currently allow to appear
/// as a variable or parameter name.
const ID_REGEX_STR: &str = r"[a-zA-Z0-9_]+";

lazy_static! {
    /// A regular expression that matches the identifiers allowed as names of
    /// Boolean parameters or variables.
    static ref ID_REGEX: Regex = Regex::new(ID_REGEX_STR).unwrap();
}

/* TODO: These log level utils can probably move to a separate util crate at some point. */
/* TODO: Logging could be more useful, e.g. print line number and similar info. */
const LOG_NOTHING: usize = 0;
const LOG_ESSENTIAL: usize = 1;
const LOG_VERBOSE: usize = 2;

fn global_log_level() -> usize {
    if cfg!(feature = "print-progress") {
        1
    } else {
        0
    }
}

fn log_essential(log_level: usize, symbolic_size: usize) -> bool {
    log_level >= LOG_VERBOSE || (symbolic_size > 100_000 && log_level >= LOG_ESSENTIAL)
}

fn should_log(log_level: usize) -> bool {
    log_level > LOG_NOTHING
}

fn never_stop() -> Result<(), ()> {
    Ok(())
}

/// A type-safe index of a `Variable` inside a `RegulatoryGraph` (or a `BooleanNetwork`).
///
/// If needed, it can be converted into `usize` for serialisation and safely read
/// again by providing the original `RegulatoryGraph` as context
/// to the `VariableId::try_from_usize`.
///
/// **Warning:** Do not mix type-safe indices between different networks/graphs!
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct VariableId(usize);

/// A type-safe index of a `Parameter` inside a `BooleanNetwork`.
///
/// If needed, it can be converted into `usize` for serialisation and safely read
/// again by providing the original `BooleanNetwork` as context
/// to the `ParameterId::try_from_usize`.
///
/// **Warning:** Do not mix type-safe indices between different networks!
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct ParameterId(usize);

/// Possible monotonous effects of a `Regulation` in a `RegulatoryGraph`.
///
/// Activation means positive and inhibition means negative monotonicity.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum Monotonicity {
    Activation,
    Inhibition,
}

/// A Boolean variable of a `RegulatoryGraph` (or a `BooleanNetwork`) with a given `name`.
///
/// `Variable` can be only created by and borrowed from a `RegulatoryGraph`.
/// It has no public constructor.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct Variable {
    name: String,
}

/// An explicit parameter of a `BooleanNetwork`; an uninterpreted Boolean function with a given
/// `name` and `arity`.
///
/// `Parameter` can be only created by and borrowed form the `BooleanNetwork` itself.
/// It has no public constructor.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct Parameter {
    name: String,
    arity: u32,
}

/// Describes an interaction between two `Variables` in a `RegulatoryGraph`
/// (or a `BooleanNetwork`).
///
/// Every regulation can be *monotonous*, and can be set as *observable*:
///
///  - Monotonicity is either *positive* or *negative* and signifies that the influence of the
///    `regulator` on the `target` has to *increase* or *decrease* the `target` value respectively.
///  - If observability is set to `true`, the `regulator` *must* have influence on the outcome
///    of the `target` update function in *some* context. If set to false, this is not enforced
///    (i.e. the `regulator` *can* have an influence on the `target`, but it is not required).
///
/// Regulations can be represented as strings in the
/// form `"regulator_name 'relationship' target_name"`. The 'relationship' starts with `-`, which
/// is followed by `>` for activation (positive monotonicity), `|` for inhibition (negative
/// monotonicity) or `?` for unspecified monotonicity. Finally, an additional `?` at the end
/// of 'relationship' signifies a non-observable regulation. Together, this gives the
/// following options:  `->, ->?, -|, -|?, -?, -??`.
///
/// Regulations cannot be created directly, they are only borrowed from a `RegulatoryGraph`
/// or a `BooleanNetwork`.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct Regulation {
    pub regulator: VariableId,
    pub target: VariableId,
    pub observable: bool,
    pub monotonicity: Option<Monotonicity>,
}

/// A directed graph representing relationships between a collection of Boolean variables
/// using `Regulations`.
///
/// It can be explored using `regulators`, `targets`, `transitive_regulators`, or
/// `transitive_targets` (for example to determine if two variables depend on each other).
/// We can also compute the SCCs of this graph.
///
/// A regulatory graph can be described using a custom string format. In this format,
/// each line represents a regulation or a comment (starting with `#`).
///
/// Regulations can be represented as strings in the form of
/// `"regulator_name 'relationship' target_name"`. The 'relationship' is one of the arrow strings
/// `->, ->?, -|, -|?, -?, -??`. Here, `>` means activation, `|` is inhibition and `?` is
/// unspecified monotonicity. The last question mark signifies observability — if it is present,
/// the regulation is not necessarily observable. See `Regulation` and tutorial module for a more
/// detailed explanation.
///
/// Example of a `RegulatoryGraph`:
///
/// ```rg
///  # Regulators of a
///  a ->? a
///  b -|? a
///
///  # Regulators of b
///  a -> b
///  b -| b
/// ```
#[derive(Clone, Debug)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct RegulatoryGraph {
    variables: Vec<Variable>,
    regulations: Vec<Regulation>,
    variable_to_index: HashMap<String, VariableId>,
}

/// Possible binary Boolean operators that can appear in `FnUpdate`.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum BinaryOp {
    And,
    Or,
    Xor,
    Iff,
    Imp,
}

/// A Boolean update function formula which references
/// `Variables` and `Parameters` of a `BooleanNetwork`.
///
/// An update function specifies the evolution rules for one specific `Variable` of a
/// `BooleanNetwork`. The arguments used in the function must be the same as specified
/// by the `RegulatoryGraph` of the network.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum FnUpdate {
    /// A true/false constant.
    Const(bool),
    /// References a network variable.
    Var(VariableId),
    /// References a network parameter (uninterpreted function).
    ///
    /// The variable list are the arguments of the function invocation.
    Param(ParameterId, Vec<FnUpdate>),
    /// Negation.
    Not(Box<FnUpdate>),
    /// Binary boolean operation.
    Binary(BinaryOp, Box<FnUpdate>, Box<FnUpdate>),
}

/// A Boolean network, possibly parametrised with uninterpreted Boolean functions.
///
/// The structure of the network is based on an underlying `RegulatoryGraph`. However,
/// compared to a `RegulatoryGraph`, `BooleanNetwork` can have a specific update function
/// given for each variable.
///
/// If the function is not specified (so called *implicit parametrisation*), all admissible
/// Boolean functions are considered in its place. A function can be also only partially
/// specified by using declared *explicit parameters*. These are uninterpreted but named Boolean
/// functions, such that, again, all admissible instantiations of these functions are considered.
/// See crate tutorial to learn more.
///
/// ### Boolean network equivalence
///
/// Please keep in mind that we consider two networks to be equivalent when they share a regulatory
/// graph, and when they have (syntactically) the same update functions and parameters. We do not
/// perform any semantic checks for whether the update functions are functionally equivalent.
///
/// Also keep in mind that the *ordering* of variables and parameters must be shared by equivalent
/// networks. This is because we want to preserve the property that `VariableId` and `ParameterId`
/// objects are interchangeable as long as networks are equivalent.
#[derive(Clone, Debug, Eq, PartialEq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct BooleanNetwork {
    graph: RegulatoryGraph,
    parameters: Vec<Parameter>,
    update_functions: Vec<Option<FnUpdate>>,
    parameter_to_index: HashMap<String, ParameterId>,
}

/// An iterator over all `VariableIds` of a `RegulatoryGraph` (or a `BooleanNetwork`).
pub type VariableIdIterator = Map<Range<usize>, fn(usize) -> VariableId>;

/// An iterator over all `ParameterIds` of a `BooleanNetwork`.
pub type ParameterIdIterator = Map<Range<usize>, fn(usize) -> ParameterId>;

/// An iterator over all `Regulations` of a `RegulatoryGraph`.
pub type RegulationIterator<'a> = std::slice::Iter<'a, Regulation>;

/// An enum representing the possible state of each variable when describing a hypercube.
#[derive(Copy, Clone, Eq, PartialEq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum ExtendedBoolean {
    Zero,
    One,
    Any,
}

/// `Space` represents a hypercube (multidimensional rectangle) in the Boolean state space.
///
/// Keep in mind that there is no way of representing an empty hypercube at the moment. So any API
/// that can take/return an empty set has to use `Option<Space>` or something similar.
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct Space(Vec<ExtendedBoolean>);

/// Annotations are "meta" objects that can be declared as part of AEON models to add additional
/// properties that are not directly recognized by the main AEON toolbox.
///
/// Annotations are comments which start with `#!`. After the `#!` "preamble", each annotation
/// can contain a "path prefix" with path segments separated using `:` (path segments can be
/// surrounded by white space that is automatically trimmed). Based on these path
/// segments, the parser will create an annotation tree. If there are multiple annotations with
/// the same path, their values are concatenated using newlines.
///
/// For example, annotations can be used to describe model layout:
///
/// ```text
/// #! layout : var_1 : 10,20
/// #! layout : var_2 : 14,-3
/// ```
///
/// Another usage for annotations are extra properties enforced on the model behaviour, for
/// example through CTL:
/// ```text
/// #! property : AG (problem => AF apoptosis)
/// ```
///
/// Obviously, you can also use annotations to specify model metadata:
/// ```text
/// #! name: My Awesome Model
/// #! description: This model describes ...
/// #! description:var_1: This variable describes ...
/// ```
///
/// You can use "empty" path (e.g. `#! is_multivalued`), and you can use an empty annotation
/// value with a non-empty path (e.g. `#!is_multivalued:var_1:`). Though this is not particularly
/// encouraged: it is better to just have `var_1` as the annotation value if you can do that.
/// An exception to this may be a case where `is_multivalued:var_1:` has an "optional" value, and
/// you want to express that while the "key" is provided, the "value" is missing. Similarly, for
/// the sake of completeness, it is technically allowed to use empty path names (e.g. `a::b:value`
/// translates to `["a", "", "b"] = "value"`), but it is discouraged.
///
/// Note that the path segments should only contain alphanumeric characters and underscores,
/// but can be escaped using backticks (`` ` ``; other backticks in path segments are not allowed).
/// Similarly, annotation values cannot contain colons (path segment separators) or backticks,
/// unless escaped with `` #`ACTUAL_STRING`# ``. You can also use escaping if you wish to
/// retain whitespace around annotation values. As mentioned, multi-line values can be split
/// into multiple annotation comments.
#[derive(PartialEq, Eq, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct ModelAnnotation {
    value: Option<String>,
    inner: HashMap<String, ModelAnnotation>,
}

#[cfg(all(test, feature = "serde"))]
mod serde_tests {
    use super::*;
    use crate::symbolic_async_graph::SymbolicAsyncGraph;
    use std::convert::TryFrom;

    fn test_round_trip<T>(value: &T)
    where
        T: serde::Serialize + serde::de::DeserializeOwned + PartialEq + std::fmt::Debug,
    {
        // Test JSON serialization
        let json = serde_json::to_string(value).expect("Serialization should succeed");
        let deserialized: T = serde_json::from_str(&json).expect("Deserialization should succeed");
        assert_eq!(
            value, &deserialized,
            "Round-trip serialization should preserve value"
        );
    }

    fn test_round_trip_clone<T>(value: T)
    where
        T: Clone + serde::Serialize + serde::de::DeserializeOwned + PartialEq + std::fmt::Debug,
    {
        test_round_trip(&value);
    }

    #[test]
    fn test_boolean_network_serialization() {
        let network = BooleanNetwork::try_from(
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

        test_round_trip(&network);

        // Test with a more complex network
        let network2 = BooleanNetwork::try_from(
            r"
            a -> b
            b -> c
            c -> a
            a -> a
            a -> c
            $a: !c & !a
            $b: a
            $c: a
        ",
        )
        .unwrap();

        test_round_trip(&network2);
    }

    #[test]
    fn test_regulatory_graph_serialization() {
        let graph = RegulatoryGraph::try_from(
            r"
            A -> B
            B -?? A
            C -> A
            C -|? B
            A -| A
        ",
        )
        .unwrap();

        test_round_trip(&graph);
    }

    #[test]
    fn test_symbolic_async_graph_serialization() {
        let network = BooleanNetwork::try_from(
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

        let stg = SymbolicAsyncGraph::new(&network).unwrap();
        // Test serialization (can't test equality as SymbolicAsyncGraph doesn't implement PartialEq)
        let json = serde_json::to_string(&stg).expect("Serialization should succeed");
        let deserialized: SymbolicAsyncGraph =
            serde_json::from_str(&json).expect("Deserialization should succeed");

        // Verify basic properties are preserved
        assert_eq!(
            stg.unit_colored_vertices().approx_cardinality(),
            deserialized.unit_colored_vertices().approx_cardinality()
        );
        assert_eq!(
            stg.unit_colored_vertices().vertices().approx_cardinality(),
            deserialized
                .unit_colored_vertices()
                .vertices()
                .approx_cardinality()
        );
        assert_eq!(
            stg.unit_colored_vertices().colors().approx_cardinality(),
            deserialized
                .unit_colored_vertices()
                .colors()
                .approx_cardinality()
        );
    }

    #[test]
    fn test_graph_colored_vertices_serialization() {
        let network = BooleanNetwork::try_from(
            r"
            A -> B
            B -> A
            $A: B
            $B: A
        ",
        )
        .unwrap();

        let stg = SymbolicAsyncGraph::new(&network).unwrap();
        let unit = stg.unit_colored_vertices();
        test_round_trip_clone(unit.clone());

        // Test empty set
        let empty = stg.empty_colored_vertices();
        test_round_trip_clone(empty.clone());

        // Test a specific vertex set
        let id_a = network.as_graph().find_variable("A").unwrap();
        let a_true = stg.fix_network_variable(id_a, true);
        test_round_trip_clone(a_true.clone());
    }

    #[test]
    fn test_graph_vertices_serialization() {
        let network = BooleanNetwork::try_from(
            r"
            A -> B
            B -> A
            $A: B
            $B: A
        ",
        )
        .unwrap();

        let stg = SymbolicAsyncGraph::new(&network).unwrap();
        let unit_vertices = stg.unit_colored_vertices().vertices();
        test_round_trip_clone(unit_vertices.clone());

        // Test empty set
        let empty_vertices = stg.empty_colored_vertices().vertices();
        test_round_trip_clone(empty_vertices.clone());
    }

    #[test]
    fn test_graph_colors_serialization() {
        let network = BooleanNetwork::try_from(
            r"
            A -> B
            B -> A
            $A: B
            $B: f(A)
        ",
        )
        .unwrap();

        let stg = SymbolicAsyncGraph::new(&network).unwrap();
        let unit_colors = stg.unit_colored_vertices().colors();
        test_round_trip_clone(unit_colors.clone());

        // Test empty set
        let empty_colors = stg.empty_colored_vertices().colors();
        test_round_trip_clone(empty_colors.clone());
    }

    #[test]
    fn test_space_serialization() {
        let network = BooleanNetwork::try_from(
            r"
            A -> B
            B -> A
        ",
        )
        .unwrap();

        // Create space with specific values for testing
        let space1_values = vec![ExtendedBoolean::Zero, ExtendedBoolean::One];
        let space1 = Space(space1_values);
        test_round_trip_clone(space1.clone());

        let space2_values = vec![
            ExtendedBoolean::Any,
            ExtendedBoolean::Zero,
            ExtendedBoolean::One,
        ];
        let space2 = Space(space2_values);
        test_round_trip_clone(space2.clone());

        // Test with a space created from network
        let space3 = Space::new(&network);
        test_round_trip_clone(space3.clone());
    }

    #[test]
    fn test_fn_update_serialization() {
        let network = BooleanNetwork::try_from(
            r"
            A -> B
            B -> A
            A -> A
            $A: B & !A
            $B: A
        ",
        )
        .unwrap();

        let id_a = network.as_graph().find_variable("A").unwrap();
        let id_b = network.as_graph().find_variable("B").unwrap();

        let update_a = network.get_update_function(id_a).as_ref().unwrap().clone();
        test_round_trip_clone(update_a.clone());

        let update_b = network.get_update_function(id_b).as_ref().unwrap().clone();
        test_round_trip_clone(update_b.clone());
    }

    #[test]
    fn test_regulation_serialization() {
        let graph = RegulatoryGraph::try_from(
            r"
            A -> B
            B -> A
            C -|? B
            A -| A
        ",
        )
        .unwrap();

        for regulation in graph.regulations() {
            test_round_trip(regulation);
        }
    }

    #[test]
    fn test_variable_and_parameter_serialization() {
        let network = BooleanNetwork::try_from(
            r"
            A -> B
            B -> A
            $A: f(B)
        ",
        )
        .unwrap();

        for var_id in network.variables() {
            let variable = network.get_variable(var_id);
            test_round_trip(variable);
        }

        for param_id in network.parameters() {
            let parameter = network.get_parameter(param_id);
            test_round_trip(parameter);
        }
    }
}
