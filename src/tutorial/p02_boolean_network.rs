//! # Boolean Networks
//!
//! A (parametrised) `BooleanNetwork` is an extension of a `RegulatoryGraph` that can specify
//! for each variable a Boolean update function. This update function can be used to generate
//! a state-transition graph of the network. There are different techniques for generating
//! such state-transition graphs. Later, you will learn about an *asynchronous* state-transition
//! graph used in this library, but other variants (such as *synchronous*) are also possible.
//!
//! Typically, a `BooleanNetwork` has a fixed update function for each variable. For example,
//! let's consider this simple graph:
//!
//! ```mermaid
//! graph LR
//!     a(A)
//!     b(B)
//!     c(C)
//!     a-- + -->b
//!     b-- + -->a
//!     c-- + -->a
//!     c-. - .->b
//!     a-- - -->a
//! ```
//!
//! We can extend this graph to a `BooleanNetwork` by assigning each variable an update function
//! (we use the `$` symbol to denote a function declaration):
//!
//! ```text
//! $A: C | (!A & B)
//! $B: A
//! $C: true
//! ```
//!
//! Notice that C has no regulators, hence its update function has to be constant. Also, `C -> B`
//! is not observable, hence `C` does not have to appear in the function of `A`. Finally, `A` appears
//! with a negation in `$A` because it regulates itself negatively. However, the choice of logical
//! connectives (`|` and `&`) is arbitrary.
//!
//! We can of course write all of this in Rust:
//!
//! ```rust
//! use biodivine_lib_param_bn::{RegulatoryGraph, BooleanNetwork, FnUpdate};
//! use std::convert::TryFrom;
//!
//! // First, we build the regulatory graph of the network.
//! let rg = RegulatoryGraph::try_from(r"
//!     A -> B
//!     B -> A
//!     C -> A
//!     C -|? B
//!     A -| A
//! ").unwrap();
//! let id_a = rg.find_variable("A").unwrap();
//! let id_b = rg.find_variable("B").unwrap();
//! let id_c = rg.find_variable("C").unwrap();
//!
//! // Now create a Boolean network and add update functions for each variable.
//! let mut bn = BooleanNetwork::new(rg);
//! assert!(bn.get_update_function(id_a).is_none());
//! // We can use standard Boolean operators `&`, `|`, `=>`, `<=>`, `^` and `!`.
//! // Names are alphanumeric strings (starting with a letter), possibly containing `_`.
//! bn.add_string_update_function("A", "C | (!A & B)")?;
//! bn.add_string_update_function("B", "A")?;
//! bn.add_string_update_function("C", "true")?;
//!
//! // We can also test that the functions are properly set.
//! assert_eq!(&Some(FnUpdate::Const(true)), bn.get_update_function(id_c));
//! assert_eq!(&Some(FnUpdate::Var(id_a)), bn.get_update_function(id_b));
//! # Ok::<(), String>(())
//! ```
//!
//! Normally, this would be the end of intro to Boolean networks, however, there is one more
//! important aspect that we need to discuss that is usually not available in other BN packages.
//!
//! ## Parametrised Boolean Networks
//!
//! As you might have noticed above, a `BooleanNetwork` is also valid if it does not have any
//! update functions set. If a Boolean network is missing some update functions, we say that
//! such network is *parametrised*. Intuitively, this means that there is some uncertainty
//! in *how* the update functions of the network behave. In fact, we will later show how to
//! introduce uncertainty even only into *parts* of an update function. But for now, let us only
//! focus on cases where the entire update function is unknown.
//!
//! To each parametrised `BooleanNetwork` corresponds a collection of fully specified Boolean
//! networks. We call these fully specified networks *parametrisations*, or *colors*. More
//! formally, a parametrisation assigns values to the rows of each update function table, thus
//! making the network fully specified, and color is just a more abstract concept from graph
//! theory which we can apply also outside of the domain of Boolean networks.
//!
//! Note that the structure of the `RegulatoryGraph` significantly limits the space of all possible
//! parametrisations. Only update functions that would be valid with respect to the specified graph
//! are considered (i.e. functions must depend only on the declared regulators and must follow
//! the declared monotonicity and observability rules).
//!
//! In our example, update function of `C` can thus be only `true` or `false`. Update function
//! of `B` can in fact be `A`, `A & !C`, and `A | !C` (since `C` is not declared as necessarily
//! observable, we actually also consider both cases where `C` can have impact, but also the one
//! where it does not). For the update function of `A`, there are 9 possible valid
//! update functions.
//!
//! When the update function for a variable `X` is completely unknown as in this case, we say
//! that `X` is *implicitly* parametrised.
//!
//! ### Uninterpreted Boolean Functions as Parameters
//!
//! If only part of the update function is unknown, we can use *explicit* parameters, or
//! *uninterpreted Boolean functions*, to describe such behaviour. Formally, every uninterpreted
//! Boolean function has a fixed name and arity, but its behaviour is otherwise unspecified.
//!
//! For example, for variable `A` from above, we can write:
//! ```text
//! $A: C | f(A, B)
//! ```
//!
//! Here, `f` is an uninterpreted function of artiy `2` (we can also use uninterpreted constants,
//! which are simply functions of arity `0`). This way, we have just exactly specified the
//! dependence of `A` on `C`, while leaving the dependence on `A` and `B` unknown. Note that `f`
//! can only take values which follow the properties of the regulatory graph, just as we had for
//! the implicitly parametrised case above (so in this case, there are two possible
//! instantiations of `f`).
//!
//! When the update function of a variable `X` contains such uninterpreted functions, we say `X`
//! is *explicitly* parametrised and the uninterpreted functions are its explicit parameters.
//! Note that such explicit parameter can be shared accross variables. By using a parameter with
//! the same name in two different update functions, you declare that this part of the two
//! functions is identical.
//!
//! > *At the moment, arguments of each explicit parameter must be variables (complex Boolean
//! > expressions are not allowed). However, this restriction may be lifted in the future.*
//!
//! In Rust, we can capture this in the following way:
//!
//! ```rust
//! # use biodivine_lib_param_bn::{RegulatoryGraph, BooleanNetwork, FnUpdate, ParameterId};
//! # use std::convert::TryFrom;
//! #
//! # // First, we build the regulatory graph of the network.
//! # let rg = RegulatoryGraph::try_from(r"
//! #     A -> B
//! #     B -> A
//! #     C -> A
//! #     C -|? B
//! #     A -| A
//! # ").unwrap();
//! # let id_a = rg.find_variable("A").unwrap();
//! # let id_b = rg.find_variable("B").unwrap();
//! # let id_c = rg.find_variable("C").unwrap();
//! // Use the same graph as above...
//! let mut bn = BooleanNetwork::new(rg);
//! assert!(bn.get_update_function(id_a).is_none());
//! // Every explicit parameter must be declared before you use it in a function.
//! let id_f: ParameterId = bn.add_parameter("f", 2)?;
//! // `ParameterId` indexes `BooleanNetwork` just as `VariableId` would.
//! assert_eq!("f", bn[id_f].get_name());
//! assert_eq!(2, bn[id_f].get_arity());
//! bn.add_string_update_function("A", "C | f(A, B)")?;
//!
//! let params: Vec<ParameterId> = bn.get_update_function(id_a).as_ref().unwrap().collect_parameters();
//! assert_eq!(vec![id_f], params);
//! # Ok::<(), String>(())
//! ```
//!
//! Overall, this mechanism provides a very powerful framework for capturing uncertainty
//! in Boolean networks.
//!
//! ## String serialisation and other features
//!
//! To store and share the `BooleanNetwork` objects, you can use a similar format to
//! that used by the `RegulatoryGraph`. The only difference is that now each line can be either
//! a regulation, or a function declaration (the order of declarations does not matter).
//! Furthermore, you can prefix a line with `#` to mark that line as a comment which will be
//! skipped by the parser. Together, this is what we refer to as the `.aeon` format.
//!
//! ```rust
//! use biodivine_lib_param_bn::BooleanNetwork;
//! use std::convert::TryFrom;
//! // Notice that C is implicitly parametrised since we do not specify an update function for it.
//! // Also, explicit parameters are not declared, they are inferred from declared functions.
//! let bn = BooleanNetwork::try_from(r"
//!     A -> B
//!     C -|? B
//!     ## Update function of variable B:
//!     $B: A
//!     C -> A
//!     B -> A
//!     A -| A
//!     $A: C | f(A, B)
//! ").unwrap();
//!
//! // The same format is also used by the default `Display` implementation.
//! // However, note that the comments are not preserved!
//! assert_eq!(bn, BooleanNetwork::try_from(bn.to_string().as_str()).unwrap())
//! ```
//!
//! Aside from this, `BooleanNetwork` allows you to access the underlying `RegulatoryGraph`
//! by calling `BooleanNetwork.as_graph()`. But in fact, a lot of the commonly used methods
//! of the `RegulatoryGraph` are also implemented for the `BooleanNetwork` (e.g.
//! `get_variable_name` or `regulators`), so the conversion often isn't necessary.
//!
//!
