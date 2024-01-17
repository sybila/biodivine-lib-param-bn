use crate::ModelAnnotation;
use crate::_impl_annotations::{ESC_PATH_SEGMENT, SIMPLE_PATH_SEGMENT};

impl ModelAnnotation {
    /// Parse annotations from a particular model string.
    ///
    /// Note that we are not validating the format of the model in any way, we are just reading
    /// the annotations. Furthermore, the annotation language is very "benevolent" (e.g. it
    /// allows things like empty path segments and annotation values), hence there is largely
    /// no way discover any errors: everything either is an annotation, or isn't, in which case
    /// it is still a normal comment.
    pub fn from_model_string(model: &str) -> ModelAnnotation {
        let mut result = ModelAnnotation::new();

        for line in model.lines() {
            let line = line.trim();
            if !line.starts_with("#!") {
                continue;
            }

            let mut annotation = line[2..].trim();
            let mut path = Vec::new();

            // If annotation is empty, we have read the whole path.
            while !annotation.is_empty() {
                // Try to match a normal path segment, and if this fails, also try to match
                // an escaped path segment.
                let capture = SIMPLE_PATH_SEGMENT
                    .captures(annotation)
                    .or_else(|| ESC_PATH_SEGMENT.captures(annotation));
                if let Some(capture) = capture {
                    // This chain is a small hack to convince the borrow checker that `c` is in
                    // fact a reference to `line` and not to `capture`.
                    let c = capture.get(1).unwrap().as_str();
                    path.push(c);
                    // Advance the annotation string to the beginning of either the next segment,
                    // or the annotation value.
                    annotation = annotation[capture[0].len()..].trim();
                } else {
                    // If there are no more path segments, the rest is an annotation value.
                    break;
                }
            }

            // Strip away the "value escape" backticks if they are present.
            if annotation.starts_with("#`") && annotation.ends_with("`#") {
                annotation = &annotation[2..annotation.len() - 2];
            }

            // Create an annotation node for this value.
            let child = result.ensure_child(&path);

            // If the tree already has some value here, add a newline first.
            if child.value().is_some() {
                child.append_value::<&str>(&[], "\n");
            }
            // Then push the new value.
            child.append_value::<&str>(&[], annotation);
        }

        result
    }
}

#[cfg(test)]
mod tests {
    use crate::ModelAnnotation;

    #[test]
    pub fn annotations_parser_test() {
        // Basic key value:
        let annotation = ModelAnnotation::from_model_string("#! key : value");
        let key = annotation.get_child(&["key"]).unwrap();
        assert_eq!("value", key.value().unwrap().as_str());

        // Duplicate key value:
        let annotation = ModelAnnotation::from_model_string("#! key : value\n#! key : value 2");
        let key = annotation.get_child(&["key"]).unwrap();
        assert_eq!("value\nvalue 2", key.value().unwrap().as_str());

        // Escaped names:
        let annotation =
            ModelAnnotation::from_model_string("#!`complex/k:e:y`:#`complex:{value}`#");
        let key = annotation.get_child(&["complex/k:e:y"]).unwrap();
        assert_eq!("complex:{value}", key.value().unwrap().as_str());

        // Nested keys:
        let annotation = ModelAnnotation::from_model_string("#!key_1:key_2:value");
        let key = annotation.get_child(&["key_1", "key_2"]).unwrap();
        assert_eq!("value", key.value().unwrap().as_str());

        // Empty keys and values:
        let annotation = ModelAnnotation::from_model_string("#!:key_2:");
        let key = annotation.get_child(&["", "key_2"]).unwrap();
        assert!(key.value().unwrap().is_empty());

        // Mixing with normal comments:
        let annotation = ModelAnnotation::from_model_string("# Comment\n#! key : value\n# Comment");
        let key = annotation.get_child(&["key"]).unwrap();
        assert_eq!("value", key.value().unwrap().as_str());
    }
}
