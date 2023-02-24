use crate::ModelAnnotation;
use crate::_impl_annotations::validate_path_segment;
use std::collections::HashMap;
use std::fmt::{Debug, Formatter};

impl ModelAnnotation {
    /// Create a new empty annotation.
    pub fn new() -> ModelAnnotation {
        ModelAnnotation {
            value: Default::default(),
            inner: Default::default(),
        }
    }

    /// Create a new annotation with a given `value` and no children.
    pub fn with_value(value: String) -> ModelAnnotation {
        ModelAnnotation {
            value: Some(value),
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
    pub fn get_mut_child<'a>(&'a mut self, path: &[&str]) -> Option<&'a mut ModelAnnotation> {
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
    /// it is inserted. If the value exists, but is different, it is overwritten. Returns `true`
    /// if the value has been updated.
    pub fn ensure_value(&mut self, path: &[&str], value: &str) -> bool {
        let annotation = self.ensure_child(path);
        if let Some(current) = annotation.value.as_ref() {
            if current == value {
                false
            } else {
                annotation.value = Some(value.to_string());
                true
            }
        } else {
            annotation.value = Some(value.to_string());
            true
        }
    }

    /// Append the given value to the value currently stored at the given path. If there is no
    /// such value, a new value is created.
    ///
    /// Note that this function does not automatically add a newline to the given `value`.
    /// If you want the value to have newlines, you must add them yourself.
    pub fn append_value(&mut self, path: &[&str], value: &str) {
        let annotation = self.ensure_child(path);
        if let Some(current) = annotation.value.as_mut() {
            current.push_str(value);
        } else {
            annotation.value = Some(value.to_string());
        }
    }

    /// Retrieve an annotation value stored at the given path,
    /// or `None` if such path/value does not exist.
    pub fn get_value(&self, path: &[&str]) -> Option<&String> {
        if path.is_empty() {
            self.value.as_ref()
        } else {
            self.inner
                .get(path[0])
                .and_then(|inner| inner.get_value(&path[1..]))
        }
    }

    /// Get the annotation value for this tree node.
    pub fn value(&self) -> Option<&String> {
        self.value.as_ref()
    }

    /// Same as `value`, but mutable.
    pub fn value_mut(&mut self) -> &mut Option<String> {
        &mut self.value
    }

    /// Get the map of all child `ModelAnnotations`.
    pub fn children(&self) -> &HashMap<String, ModelAnnotation> {
        &self.inner
    }

    /// Self as `children` but mutable.
    pub fn children_mut(&mut self) -> &mut HashMap<String, ModelAnnotation> {
        &mut self.inner
    }
}

impl Default for ModelAnnotation {
    fn default() -> Self {
        ModelAnnotation::new()
    }
}

impl Debug for ModelAnnotation {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "Annotation[{:?}][", self.value)?;
        // Sorting ensures deterministic representation.
        let mut keys = self.inner.keys().collect::<Vec<_>>();
        keys.sort();
        for k in keys {
            write!(f, "(`{}` : {:?})", k, self.inner.get(k).unwrap())?;
        }
        write!(f, "]")
    }
}

#[cfg(test)]
mod tests {
    use crate::ModelAnnotation;

    #[test]
    pub fn simple_annotation_test() {
        let mut annotation = ModelAnnotation::default();

        assert!(annotation.children().is_empty());
        assert!(annotation.value().is_none());

        // Return value of `ensure_value` is correct.
        assert!(annotation.ensure_value(&[], "Value 1"));
        assert_eq!("Value 1", annotation.value().unwrap().as_str());
        assert!(!annotation.ensure_value(&[], "Value 1"));

        // Value append works:
        annotation.ensure_value(&[], "Hello\n");
        annotation.append_value(&[], "World\n");
        assert_eq!("Hello\nWorld\n", annotation.value().unwrap().as_str());

        // We can also add values/children through the mut bindings:
        annotation.value_mut().as_mut().unwrap().push_str("Value 3");
        assert_eq!(
            "Hello\nWorld\nValue 3",
            annotation.value().unwrap().as_str()
        );

        annotation.children_mut().insert(
            "Child 1".to_string(),
            ModelAnnotation::with_value("Child value".to_string()),
        );
        assert!(annotation.get_child(&["Child 1"]).is_some());
        assert_eq!(
            "Child value",
            annotation.get_value(&["Child 1"]).unwrap().as_str()
        );

        assert!(annotation.get_child(&["Child 1", "Child 2"]).is_none());
        annotation.ensure_child(&["Child 1", "Child 2"]);
        assert!(annotation.get_child(&["Child 1", "Child 2"]).is_some());
    }

    #[test]
    #[should_panic]
    pub fn add_invalid_annotation_child() {
        // Backticks are not allowed.
        let mut annotation = ModelAnnotation::default();
        annotation.ensure_child(&["va`R`"]);
    }

    #[test]
    #[should_panic]
    pub fn print_invalid_annotation() {
        let mut annotations = ModelAnnotation::default();
        annotations.children_mut().insert(
            "hello\nworld".to_string(),
            ModelAnnotation::with_value("Value".to_string()),
        );
        annotations.to_string();
    }
}
