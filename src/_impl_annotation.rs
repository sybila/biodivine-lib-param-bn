use crate::ModelAnnotation;
use base64::prelude::BASE64_STANDARD;
use base64::Engine;
use regex::Regex;
use std::collections::{HashMap, HashSet};
use std::fmt::{Debug, Display, Formatter};

impl ModelAnnotation {
    /// Create new empty annotation.
    pub fn new() -> ModelAnnotation {
        ModelAnnotation {
            values: Default::default(),
            inner: Default::default(),
        }
    }

    /// Get a reference to a child `ModelAnnotation` by specifying a path.
    ///
    /// If such annotation does not exist, returns `None`.
    pub fn get_child<'a>(&'a self, path: &[&str]) -> Option<&'a ModelAnnotation> {
        if path.is_empty() {
            Some(self)
        } else {
            self.inner
                .get(path[0])
                .and_then(|inner| inner.get_child(&path[1..]))
        }
    }

    /// Get a reference to a mutable child `ModelAnnotation` by specifying a path.
    ///
    /// If such annotation dues not exist, returns `None`. If you want to instead create
    /// the path when it does not exist, use `ModelAnnotation::ensure_child`.
    pub fn get_mut_child<'a>(&'a mut self, path: &[&str]) -> Option<&'a ModelAnnotation> {
        if path.is_empty() {
            Some(self)
        } else {
            self.inner
                .get_mut(path[0])
                .and_then(|inner| inner.get_mut_child(&path[1..]))
        }
    }

    /// Get a mutable reference to a `ModelAnnotation` child, just as `get_mut_child`, but
    /// if some part of the path does not exist, empty annotations are created to populate it.
    ///
    /// Panics: Fails if the child path segments contain curly brackets.
    pub fn ensure_child<'a>(&'a mut self, path: &[&str]) -> &'a mut ModelAnnotation {
        if path.is_empty() {
            self
        } else {
            // Sadly, we have to run the `to_string` here, as we are not sure if the key exists.
            validate_path_segment(path[0]);
            let entry = self.inner.entry(path[0].to_string()).or_default();
            entry.ensure_child(&path[1..])
        }
    }

    /// Ensure that the given value is present at the given path. If the value is not present,
    /// it is inserted. Returns `true` if the value has been inserted.
    pub fn ensure_value(&mut self, path: &[&str], value: String) -> bool {
        let annotation = self.ensure_child(path);
        annotation.values.insert(value)
    }

    /// Get the set of all `String` values stored in this model annotation.
    pub fn values(&self) -> &HashSet<String> {
        &self.values
    }

    /// Same as `values`, but mutable.
    pub fn values_mut(&mut self) -> &mut HashSet<String> {
        &mut self.values
    }

    /// Get the map of all child `ModelAnnotations`.
    pub fn children(&self) -> &HashMap<String, ModelAnnotation> {
        &self.inner
    }

    /// Self as `children` but mutable.
    pub fn children_mut(&mut self) -> &mut HashMap<String, ModelAnnotation> {
        &mut self.inner
    }

    /// Get a reference to a *single* string value stored in this annotation. If there are more
    /// string values (or no value at all), the method returns `None`.
    ///
    /// You can use this to quickly validate that a value has been indeed provided exactly once.
    pub fn value_singleton(&self) -> Option<&String> {
        if self.values.len() != 1 {
            None
        } else {
            self.values.iter().next()
        }
    }

    /// A helper function used by the `Display` implementation.
    ///
    /// Arguments:
    ///  - `valid_name` regex which matches names that can be displayed without escaping (this
    ///     is just an optimization such that we don't have to recreate the regex repeatedly).
    ///  - absolute `path` to this specific annotation. The recursive function will push/pop
    ///     items into path as needed (hence a mutable vector instead of a slice).
    ///  - A formatter from the `Display::fmt` method.
    fn fmt_with_path<'a>(
        &'a self,
        valid_name: &Regex,
        path: &mut Vec<&'a str>,
        f: &mut Formatter<'_>,
    ) -> std::fmt::Result {
        // Both values and children are explored in a sorted order to ensure
        // the output is reasonably deterministic.
        let mut values = self.values.iter().collect::<Vec<_>>();
        values.sort();
        for x in values {
            write!(f, "#!")?;
            fmt_path(valid_name, path, f)?;
            // Escape annotation value if needed.
            let has_colon = x.contains(':');
            let has_b_apostrophe = x.contains('`');
            let has_new_line = x.contains('\n');
            // TODO:
            //  Just as with path segments, we should instead specify the supported
            //  character range for each escaping method instead of this heuristic.
            if !has_colon && !has_b_apostrophe && !has_new_line {
                // If neither is present, we can just dump the value.
                writeln!(f, "{}", x)?;
            } else if has_colon != has_b_apostrophe && !has_new_line {
                // If one is present but not the other one, we can use normal escaping.
                // Yes, we are escaping `x` too, because it could be misread as an escaped value.
                // This way, it will be escaped to ``x`` and then un-escaped back to `x`.
                writeln!(f, "`{}`", x)?;
            } else {
                // The string has both a colon and a back apostrophe, or a new line. Sadly, this
                // means we have to escape it all the way to base64, because we don't know if
                // there is some super weird text that will break our escaping/parsing code.
                // (If there is a newline, things will break for sure)
                writeln!(f, "b`{}`", BASE64_STANDARD.encode(x.as_bytes()))?;
            }
            if x.contains(':') {
                writeln!(f, "`{}`", x)?;
            } else {
                writeln!(f, "{}", x)?;
            }
        }
        let mut keys = self.inner.keys().collect::<Vec<_>>();
        keys.sort();
        for key in keys {
            path.push(key.as_str());
            let child = self.inner.get(key).unwrap();
            child.fmt_with_path(valid_name, path, f)?;
            path.pop();
        }
        Ok(())
    }
}

/// Panic if the path segment name is invalid.
fn validate_path_segment(path: &str) {
    // TODO:
    //  This is woefully incomplete. People can still fit A LOT of trash into this definition.
    //  Ideally, we should specify a supported list of "printable" characters instead.
    if path.contains('`') {
        panic!(
            "Annotation path segments cannot contain back-apostrophe. Given \"{}\".",
            path
        );
    }
    if path.contains('\n') {
        panic!(
            "Annotation path segments cannot contain line breaks. Given \"{}\".",
            path
        );
    }
}

/// A helper function used by the `Display` implementation.
fn fmt_path(valid_name: &Regex, mut path: &[&str], f: &mut Formatter<'_>) -> std::fmt::Result {
    while !path.is_empty() {
        validate_path_segment(path[0]);
        if valid_name.is_match(path[0]) {
            write!(f, "{}:", path[0])?;
        } else {
            write!(f, "`{}`:", path[0])?;
        }
        path = &path[1..];
    }
    Ok(())
}

impl Default for ModelAnnotation {
    fn default() -> Self {
        ModelAnnotation::new()
    }
}

impl Debug for ModelAnnotation {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        // This is very much not efficient, but should be ok for debug prints.
        let mut v = self.values.iter().cloned().collect::<Vec<_>>();
        v.sort();
        write!(f, "Annotation[{:?}][", v.join(", "))?;
        for (k, v) in &self.inner {
            write!(f, "(`{}` : {:?})", k, v)?;
        }
        write!(f, "]")
    }
}

impl Display for ModelAnnotation {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let name_regex = Regex::new("^[a-zA-Z0-9_]*$").unwrap();
        self.fmt_with_path(&name_regex, &mut Vec::new(), f)
    }
}

#[cfg(test)]
mod tests {
    use crate::ModelAnnotation;

    #[test]
    pub fn simple_annotation_test() {
        let v_1 = "Value 1".to_string();
        let v_2 = "Value 2".to_string();

        let mut annotation = ModelAnnotation::default();

        assert!(annotation.children().is_empty());
        assert!(annotation.values().is_empty());

        // Values are kept in a set:
        annotation.ensure_value(&[], v_1.clone());
        assert_eq!(1, annotation.values().len());
        annotation.ensure_value(&[], "Value 1".to_string());
        assert_eq!(1, annotation.values().len());

        // Value singletons work:
        assert_eq!(Some(&v_1), annotation.value_singleton());
        annotation.ensure_value(&[], v_2.clone());
        assert_eq!(None, annotation.value_singleton());

        // We can also add values/children through the mut bindings:
        annotation.values_mut().insert("Value 3".to_string());
        assert_eq!(3, annotation.values().len());
        annotation
            .children_mut()
            .insert("Child 1".to_string(), ModelAnnotation::new());
        assert!(annotation.get_child(&["Child 1"]).is_some());

        assert!(annotation.get_child(&["Child 1", "Child 2"]).is_none());
        annotation.ensure_child(&["Child 1", "Child 2"]);
        assert!(annotation.get_child(&["Child 1", "Child 2"]).is_some());
    }

    #[test]
    #[should_panic]
    pub fn add_invalid_annotation_child() {
        let mut annotation = ModelAnnotation::default();
        annotation.ensure_child(&["va`R`"]);
    }

    #[test]
    #[should_panic]
    pub fn print_invalid_annotation() {
        let mut annotations = ModelAnnotation::default();
        let mut child = ModelAnnotation::new();
        child.values.insert("Hello".to_string());
        annotations
            .children_mut()
            .insert("hello\nworld".to_string(), child);
        annotations.to_string();
    }
}
