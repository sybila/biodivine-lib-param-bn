/// **(internal)** Utility methods for constructing and modifying regulatory graphs.
pub mod _impl_misc;

/// **(internal)** Implements a simple export mechanism for visualising regulatory graphs using
/// GraphViz `.dot` format.
pub mod _impl_dot_export;

/// **(internal)** Implements a basic "syntactic" equivalence relation on regulatory graphs.
pub mod _impl_equality;

/// **(internal)** Display the regulatory graph as a partial `.aeon` model.
pub mod _impl_display;

/// **(internal)** A signed directed graph is an internal representation of the regulatory
/// graph that is used to implement some of the more demanding analysis algorithms (SCC, FVS, ...).
pub mod signed_directed_graph;
