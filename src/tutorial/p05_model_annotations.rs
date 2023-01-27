//! # Model Annotations
//!
//! As part of the `.aeon` format, we support simple "structured annotations" within the
//! language comments. You can use these annotations to store things like metadata or other
//! model properties.
//!
//! As annotations are to a large extent separate from the `.aeon` format, you have to read
//! them separately:
//!
//! ```rust
//! use biodivine_lib_param_bn::BooleanNetwork;
//! use biodivine_lib_param_bn::ModelAnnotation;
//!
//! # // Double hashtag prevents line hiding in code example.
//! let model_string = "
//!     ## You can write AEON models with comments, just as in any other file.
//!     a -> b
//!     b -> c
//!     c -> a
//!     c -| b
//!     $b: !c & a
//!
//!     ## However, you can also write 'annotation' comments, given as #! path: value
//!     #! name: My simple model
//!     #! description: The description of my simple model.
//!     ## Multi-line annotations simply repeat the same path on multiple lines.
//!     #! description: This is also part of the model description.
//!
//!     ## Path can in fact be a sequence of keys:
//!     #! description:variable:a: First variable.
//!     #! description:variable:b: Second variable.
//!     #! description:variable:c: Third variable.
//!
//!
//! ";
//!
//! // Model parsing works as before, since all annotations are just comments.
//! let model = BooleanNetwork::try_from(model_string).unwrap();
//!
//! // To get the annotations, you have to parse them separately:
//! let annotation_tree = ModelAnnotation::from_model_string(model_string);
//!
//! // To access the values, use the same "path" as in the plaintext annotation.
//! let name_node = annotation_tree.get_child(&["name"]).unwrap();
//! // Here, `name` contains all values associated with `name` path prefix. In this case,
//! // this is just the single value:
//! assert_eq!("My simple model", name_node.value().unwrap().as_str());
//!
//! // If a key repeats multiple times, all values are concatenated using a newline (extra
//! // whitespace around each line is trimmed).
//! let description_node = annotation_tree.get_child(&["description"]).unwrap();
//! assert_eq!(2, description_node.value().unwrap().lines().count());
//!
//! // Nevertheless, `description_node` also contains other child nodes. To access these, we can
//! // use a specific path:
//! let description_a = description_node.get_child(&["variable", "a"]).unwrap();
//! assert_eq!("First variable.", description_a.value().unwrap().as_str());
//!
//! // We can get the same information from the "root" node:
//! let description_a_2 = annotation_tree.get_child(&["description", "variable", "a"]).unwrap();
//! assert_eq!(description_a.value(), description_a_2.value());
//!
//! // Finally, if we only care about the value, we can directly ask for it:
//! assert_eq!(description_a.value(), annotation_tree.get_value(&["description", "variable", "a"]));
//! ```
//!
//! The `ModelAnnotation` structure supports mutable operations (see `get_child_mut`,
//! `ensure_child`, `ensure_value`, `append_value` and `children_mut`). As such, you can create
//! annotations directly and attach them to models:
//!
//! ```rust
//! # use biodivine_lib_param_bn::ModelAnnotation;
//!
//! let mut annotation = ModelAnnotation::default();
//! let variable_descriptions = annotation.ensure_child(&["description", "variable"]);
//! // Note that empty annotation object will not be printed though, we have to add some values...
//! variable_descriptions.children_mut().insert(
//!     "a".to_string(),
//!     ModelAnnotation::with_value("Describe A.".to_string())
//! );
//!
//! // We don't even have to call `ensure_child`: if we know the full path, we can just
//! // use `ensure_value` directly:
//! annotation.ensure_value(&["description", "variable", "b"], "Second variable.");
//!
//! // Finally, use `to_string` or `Display` to print all annotations in the standard format:
//! println!("{}", annotation);
//! ```
//!
//! ## Escaping and special characters
//!
//! Annotations have to follow several strict rules in order to parse correctly.
//!
//! First, a *path segment* (part of the path string) should only contain alphanumeric characters
//! and underscores. If this is not the case, you can escape it using backticks (i.e.
//! `complex + (segment)` becomes `` `complex + (segment)` ``). However, for obvious reasons,
//! this does not work for path segments that contain backticks or newlines. As such, these
//! two characters are not allowed in path segments at all, and the library will panic as soon as
//! it encounters them. If such situation occurs in the input file, it
//! will likely be parsed as an incomplete path (i.e. it the library won't panic, but the resulting
//! annotation is not well defined).
//!
//! Similarly, annotation *values* cannot contain colons (path segment separators),
//! but otherwise can contain any characters. If you want to include a colon, you can
//! escape the whole `VALUE` as `` #`VALUE`# ``. This escaping is also useful when you want
//! to preserve whitespace surrounding the value, since the parser will automatically trim
//! any whitespace around path segments or values.
//!
//! ```rust
//! # use biodivine_lib_param_bn::ModelAnnotation;
//!
//! let annotation_string = "
//!     ## A key-value pair that uses normal escaping.
//!     #! `complex+{key}` : #`Value with: colon`#
//!     ## A multi-line annotation with surrounding whitespace, place at the 'root' path.
//!     #! #`\t\tHello`#
//!     #! #`\t\tWorld`#
//! ";
//!
//! let annotation = ModelAnnotation::from_model_string(&annotation_string);
//!
//! assert_eq!("\t\tHello\n\t\tWorld", annotation.value().unwrap().as_str());
//! assert_eq!("Value with: colon", annotation.get_value(&["complex+{key}"]).unwrap().as_str());
//!
//! ```
//!
