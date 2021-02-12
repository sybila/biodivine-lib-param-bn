//! # Regulatory graphs
//!
//! One of the most basic concepts in computational biology are *regulatory graphs* (or networks).
//! A regulatory graph is a directed graph where the vertices represent some biological entities
//! and the edges correspond to some high-level abstraction of interaction between the entities.
//! Such edges are called regulations.
//!
//! For example, let's say we have a system with three chemical species, `A`, `B`, and `C`, such
//! that they all depend cyclically on each other (`A` influences `B`, which influences `C`,
//! which influences `A`), and additionally, we also have `C` influencing `B`. This relationship
//! can be represented by a graph:
//!
//! ```mermaid
//! graph LR
//! a(A)
//! b(B)
//! c(C)
//! a-->b
//! b-->c
//! c-->a
//! c-->b
//! ```
//!
//! We can then easily construct such graph in Rust:
//!
//! ```rust
//! use biodivine_lib_param_bn::RegulatoryGraph;
//! use biodivine_lib_param_bn::Monotonicity::{Activation, Inhibition};
//! // RegulatoryGraph expects `String` names, so we have to convert `&str` to `String`.
//! let mut rg = RegulatoryGraph::new(vec!["A".into(), "B".into(), "C".into()]);
//! // Notice that `add_regulation` can return an error if
//! // the edge already exists or uses invalid variable names.
//! rg.add_regulation("A", "B", true, Some(Activation))?;
//! rg.add_regulation("B", "C", true, Some(Activation))?;
//! rg.add_regulation("C", "A", true, Some(Activation))?;
//! rg.add_regulation("C", "B", false, Some(Inhibition))?;
//! # Ok::<(), String>(())
//! ```
//!
//! When adding regulations, we see an extra Boolean argument: *observability*. Observability
//! indicates whether the regulation has some effect on the target variable (in this case, we
//! require all regulations to have effect except for `C -> B`). Furthermore, for each regulation,
//! we can specify its monotonicity, which is also a common property of biological networks.
//! If a regulation is an *activation*, increasing the regulator increases the value of the
//! target species. For *inhibitions*, the effect is reversed.
//!
//! We can include this information in the visual representation of the graph as well:
//!
//! ```mermaid
//! graph LR
//!     a(A)
//!     b(B)
//!     c(C)
//!     a-- + -->b
//!     b-- + -->c
//!     c-- + -->a
//!     c-. - .->b
//! ```
//!
//! Note that here, we use `+` and `-` for activation and inhibition, and dotted arrow for
//! non-observable regulation. In other materials, you can often see other visual langauge, such
//! as different arrow heads, or color-coded arrows.
//!
//! ## Basic Manipulation of Regulatory Graphs
//!
//! At the moment, there is no way to add, remove, or edit variables once the `RegulatoryGraph`
//! is created. However, as we have seen, you can add new regulations. To easily represent
//! each variable in the graph, we use `VariableId`, which is simply a typesafe variable index.
//! The advantage of `VariableId` is that it implements `Copy` and is therefore much easier to
//! pass around than `String` names.
//! You can then also use corresponding `VariableId` to find regulations.
//!
//! ```rust
//! # use biodivine_lib_param_bn::{RegulatoryGraph, VariableId};
//! # use biodivine_lib_param_bn::Monotonicity::{Activation, Inhibition};
//! # let mut rg = RegulatoryGraph::new(vec!["A".into(), "B".into(), "C".into()]);
//! # rg.add_regulation("A", "B", true, Some(Activation))?;
//! # rg.add_regulation("B", "C", true, Some(Activation))?;
//! # rg.add_regulation("C", "A", true, Some(Activation))?;
//! # rg.add_regulation("C", "B", false, Some(Inhibition))?;
//! let id_a = rg.find_variable("A").unwrap();
//! let id_b = rg.find_variable("B").unwrap();
//! let id_c = rg.find_variable("C").unwrap();
//!
//! assert_eq!("B", rg.get_variable(id_b).get_name());
//! // There are some shortcuts for most commonly used functionality:
//! assert_eq!("A", rg.get_variable_name(id_a));
//! // You can also index the RegulatoryGraph using variable ids:
//! assert_eq!(rg.get_variable_name(id_c), rg[id_c].get_name());
//!
//! // Each regulation has a regulator, target, observability, and monotonicity.
//! assert!(rg.find_regulation(id_c, id_b).is_some());
//! assert!(rg.find_regulation(id_a, id_b).unwrap().is_observable());
//!
//! // You can also iterate through all variables and regulations of the network.
//! for v in rg.variables() {   // v: VariableId
//!     println!("Variable {:?} has name {}.", v, rg[v]);
//! }
//! for r in rg.regulations() { // r: Regulation
//!     println!("Regulation from {} to {}.", rg[r.get_regulator()], rg[r.get_target()]);
//! }
//! # Ok::<(), String>(())
//! ```
//!
//! ## Advanced Functions on Regulatory Graphs
//!
//! Aside from reading basic structure of the graph, we can also obtain some more complex
//! information from the graph structure:
//!
//! ```rust
//! # use biodivine_lib_param_bn::{RegulatoryGraph, VariableId};
//! # use biodivine_lib_param_bn::Monotonicity::{Activation, Inhibition};
//! # use std::collections::HashSet;
//! # let mut rg = RegulatoryGraph::new(vec!["A".into(), "B".into(), "C".into()]);
//! # rg.add_regulation("A", "B", true, Some(Activation))?;
//! # rg.add_regulation("B", "C", true, Some(Activation))?;
//! # rg.add_regulation("C", "A", true, Some(Activation))?;
//! # rg.add_regulation("C", "B", false, Some(Inhibition))?;
//! # let id_a = rg.find_variable("A").unwrap();
//! # let id_b = rg.find_variable("B").unwrap();
//! # let id_c = rg.find_variable("C").unwrap();
//! // Find all predecessors/successors of a node:
//! assert_eq!(vec![id_c], rg.regulators(id_a));
//! assert_eq!(vec![id_a, id_b], rg.targets(id_c));
//! // This can be used (for example) to test for input/output variables:
//! let is_input = rg.regulators(id_b).is_empty();
//! assert!(!is_input);
//!
//! // Find all transitive successors/predecessors of a node:
//! // (in our simple graph, all variables depend on each other transitively)
//! let all_variables: HashSet<VariableId> = rg.variables().collect();
//! assert_eq!(all_variables, rg.transitive_regulators(id_a));
//! assert_eq!(all_variables, rg.transitive_targets(id_b));
//! // Using this, we can (for example) test if two variables are independent:
//! let a_independent_of_b = !rg.transitive_regulators(id_a).contains(&id_b);
//! assert!(!a_independent_of_b);
//!
//! // Finally, we can compute all strongly connected components of the regulatory graph:
//! let components: Vec<HashSet<VariableId>> = rg.components();
//! assert_eq!(1, components.len());
//! assert_eq!(all_variables, components.into_iter().next().unwrap());
//! // (in our case, the whole graph is one component)
//! # Ok::<(), String>(())
//! ```
//!
//! ## String Serialisation
//!
//! To safely transfer and store regulatory graphs, we implement a simple string format.
//! Each regulation is stored as an "arrow string" (such as `A -> B`) on a separate line.
//!
//! Each arrow string starts with `-`, then followed by `>`, `|`, or `?`, corresponding
//! to activation, inhibition or unspecified monotonicity. Finally, if a regulation is not
//! observable, the arrow string also contains one more `?`.
//!
//! ```rust
//! # use biodivine_lib_param_bn::{RegulatoryGraph, VariableId};
//! # use biodivine_lib_param_bn::Monotonicity::{Activation, Inhibition};
//! # use std::collections::HashSet;
//! # use std::convert::TryFrom;
//! # let mut rg = RegulatoryGraph::new(vec!["A".into(), "B".into(), "C".into()]);
//! # rg.add_regulation("A", "B", true, Some(Activation))?;
//! # rg.add_regulation("B", "C", true, Some(Activation))?;
//! # rg.add_regulation("C", "A", true, Some(Activation))?;
//! # rg.add_regulation("C", "B", false, Some(Inhibition))?;
//! # let id_a = rg.find_variable("A").unwrap();
//! # let id_b = rg.find_variable("B").unwrap();
//! # let id_c = rg.find_variable("C").unwrap();
//! let mut rg_2 = RegulatoryGraph::try_from(r"
//!     A -> B
//!     B -> C
//!     C -> A
//!     C -|? B
//! ")?;
//!
//! assert_eq!(rg, rg_2);
//!
//! // You can also use the arrow string representation to add new regulations:
//! rg_2.add_regulation_string("A -?? C")?;
//! assert_ne!(rg, rg_2);
//!
//! // This representation corresponds to the default `Display` format:
//! let rg_string = format!("{}", rg);
//! assert_eq!(rg, RegulatoryGraph::try_from(rg_string.as_str())?);
//! # Ok::<(), String>(())
//! ```
//!
//! In the next chapter, you can learn how to turn a `RegulatoryGraph` into `BooleanNetwork` by
//! adding (partial) Boolean update functions.
//!
