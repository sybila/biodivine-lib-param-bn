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
//!
//!     ## Path can in fact be a sequence of keys:
//!     #! description:variable:a: First variable.
//!     #! description:variable:b: Second variable.
//!     #! description:variable:c: Third variable.
//!
//!     ## Multiple values can be associated with the same key.
//!     #! description: This is also part of the model description.
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
//! let name = annotation_tree.get_child(&["name"]).unwrap();
//! // Here, `name` contains all values associated with `name` path prefix. In this case,
//! // this is just the single value:
//! assert_eq!("My simple model", name.value_singleton().unwrap().as_str());
//!
//! // However, if a key admits more than one value, all values are preserved in an unordered set.
//! let description = annotation_tree.get_child(&["description"]).unwrap();
//! assert_eq!(2, description.values().len());
//!
//! // Nevertheless, "description" also contains other child nodes. To access these, we can
//! // use a specific path:
//! let description_a = annotation_tree.get_child(&["description", "variable", "a"]).unwrap();
//! assert_eq!("First variable.", description_a.value_singleton().unwrap().as_str());
//! ```
//!
//! The `ModelAnnotation` structure supports mutable operations (see `get_child_mut`,
//! `ensure_child`, `ensure_value`, `values_mut` and `children_mut`). As such, you can create
//! annotations directly:
//!
//! ```rust
//! # use biodivine_lib_param_bn::ModelAnnotation;
//!
//! let mut annotation = ModelAnnotation::default();
//! let variable_descriptions = annotation.ensure_child(&["description", "variable"]);
//! // Note that empty annotation object will not be printed though, we have to add some values...
//! variable_descriptions.children_mut().insert("a".to_string(), ModelAnnotation::default());
//! variable_descriptions.ensure_value(&["a"], "First variable.".to_string());
//!
//! // We didn't even have to call `ensure_child` before: if we know the full path, we can just
//! // use `ensure_value` directly:
//! annotation.ensure_value(&["description", "variable", "b"], "Second variable.".to_string());
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
//! `complex(segment)` becomes `` `complex(segment)` ``). However, for obvious reasons,
//! this does not work for path segments that contain backticks or newlines. As such, these
//! two characters are not allowed in path segments, and the library will panic as soon as
//! it encounters them in this position. If such situation occurs in the input file, it
//! will likely be parsed as an incomplete path (i.e. it won't fail).
//!
//! Similarly, annotation *values* cannot contain backticks or colons (path segment separators),
//! but otherwise can contain any characters. If you want to include a backtick or a colon, you can
//! again escape the whole value using backticks. If you need to include a newline or something else
//! that could break the annotation syntax, you can use a special `` b`BASE_64` `` escaping. Such
//! values will be decoded from standard base64 encoding when parsed and can thus contain any
//! character.
//!
//! ```rust
//! # use biodivine_lib_param_bn::ModelAnnotation;
//!
//! let annotation_string = "
//!     ## A key-value pair that uses normal escaping.
//!     #! `complex+{key}` : `Value with: colon`
//!     ## A multi-line, base64-encoded value placed at the 'root' path.
//!     #! b`bXVsdGkKbGluZQp0ZXh0`
//! ";
//!
//! let annotation = ModelAnnotation::from_model_string(&annotation_string);
//!
//! assert_eq!("multi\nline\ntext", annotation.value_singleton().unwrap().as_str());
//! assert_eq!("Value with: colon", annotation.get_child(&["complex+{key}"]).unwrap().value_singleton().unwrap().as_str());
//!
//! ```
//!
