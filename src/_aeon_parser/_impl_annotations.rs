use crate::ModelAnnotation;
use base64::prelude::BASE64_STANDARD;
use base64::Engine;

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

        // Matches a "foo:" path segment.
        let path_name = regex::Regex::new("^\\s*([a-zA-Z0-9_]*)\\s*:").unwrap();
        // Matches a "`foo`:" path segment.
        let esc_path_name = regex::Regex::new("^\\s*`([^`]*)`\\s*:").unwrap();
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
                let capture = path_name
                    .captures(annotation)
                    .or_else(|| esc_path_name.captures(annotation));
                if let Some(capture) = capture {
                    // This chain is a small hack to convince the borrow checker that `c` is in
                    // fact a reference to `line` and not to `capture`.
                    let c = capture.get(1).unwrap().as_str();
                    path.push(c);
                    // Advance the annotation string to the begging of either the next segment,
                    // or the annotation value.
                    annotation = annotation[capture[0].len()..].trim();
                } else {
                    // If there are no more path segments, the rest is an annotation value.
                    break;
                }
            }

            // Strip away the "value escape" brackets if they are present.
            if annotation.starts_with('`') && annotation.ends_with('`') {
                annotation = &annotation[1..annotation.len() - 1];
            }

            if annotation.starts_with("b`") && annotation.ends_with('`') {
                // Decode BASE64 values which contain problematic content, like newlines.
                let decoded = BASE64_STANDARD
                    .decode(&annotation[2..annotation.len() - 1])
                    .unwrap();
                let decoded = String::from_utf8(decoded).unwrap();
                result.ensure_value(&path, decoded);
                continue;
            }

            result.ensure_value(&path, annotation.to_string());
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
        assert_eq!("value", key.value_singleton().unwrap().as_str());

        // Duplicate key value:
        let annotation = ModelAnnotation::from_model_string("#! key : value\n#! key : value 2");
        let key = annotation.get_child(&["key"]).unwrap();
        assert_eq!(2, key.values().len());

        // Escaped names:
        let annotation = ModelAnnotation::from_model_string("#!`complex/k:e:y`:`complex:{value}`");
        let key = annotation.get_child(&["complex/k:e:y"]).unwrap();
        assert_eq!("complex:{value}", key.value_singleton().unwrap().as_str());

        // Nested keys:
        let annotation = ModelAnnotation::from_model_string("#!key_1:key_2:value");
        let key = annotation.get_child(&["key_1", "key_2"]).unwrap();
        assert_eq!("value", key.value_singleton().unwrap().as_str());

        // Empty keys and values:
        let annotation = ModelAnnotation::from_model_string("#!:key_2:\n#!");
        let key = annotation.get_child(&["", "key_2"]).unwrap();
        assert_eq!("", key.value_singleton().unwrap().as_str());
        assert_eq!("", annotation.value_singleton().unwrap().as_str());

        // Mixing with normal comments:
        let annotation = ModelAnnotation::from_model_string("# Comment\n#! key : value\n# Comment");
        let key = annotation.get_child(&["key"]).unwrap();
        assert_eq!("value", key.value_singleton().unwrap().as_str());
    }

    #[test]
    pub fn annotation_read_write_test() {
        let mut annotations = ModelAnnotation::new();
        // "root" annotation
        annotations.ensure_value(&[], "hello".to_string());
        // normal annotation
        annotations.ensure_value(&["name"], "Model name".to_string());
        // Empty key and value
        annotations.ensure_value(&["var", "", "x"], "".to_string());
        // Escaped names and values
        annotations.ensure_value(&["var {list}"], "Hello: there".to_string());
        // BASE64 value
        annotations.ensure_value(&["base64"], "Hello\nWorld: `Some text`.".to_string());

        let string = annotations.to_string();
        let parsed = ModelAnnotation::from_model_string(string.as_str());

        assert_eq!(annotations, parsed);
    }
}
