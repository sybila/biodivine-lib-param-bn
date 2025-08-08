use crate::_impl_annotations::{ALPHANUMERIC, validate_path_segment};
use crate::ModelAnnotation;
use std::fmt::{Display, Formatter};

impl Display for ModelAnnotation {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        self.fmt_with_path(&mut Vec::new(), f)
    }
}

/// A helper function used by the `Display` implementation to print annotation paths with
/// proper escaping.
fn fmt_path(mut path: &[&str], f: &mut Formatter<'_>) -> std::fmt::Result {
    while !path.is_empty() {
        // Only print path segment if it is valid.
        validate_path_segment(path[0]);
        if ALPHANUMERIC.is_match(path[0]) {
            // Alphanumeric names are printed directly.
            write!(f, "{}:", path[0])?;
        } else {
            // Everything else is escaped using backticks.
            write!(f, "`{}`:", path[0])?;
        }
        path = &path[1..];
    }
    Ok(())
}

impl ModelAnnotation {
    /// A helper function used by the `Display` implementation to recursively print the whole
    /// annotation tree.
    ///
    /// Arguments:
    ///  - absolute `path` to this specific annotation. The recursive function will push/pop
    ///    items into path as needed (hence a mutable vector instead of a slice).
    ///  - A formatter from the `Display::fmt` method.
    fn fmt_with_path<'a>(
        &'a self,
        path: &mut Vec<&'a str>,
        f: &mut Formatter<'_>,
    ) -> std::fmt::Result {
        if let Some(value) = self.value.as_ref() {
            if value.is_empty() {
                // Empty value has an empty lines iterator,
                // hence we need to print it explicitly.
                write!(f, "#!")?;
                fmt_path(path, f)?;
                writeln!(f)?;
            } else {
                // Otherwise the value is printed line-by-line:
                for line in value.lines() {
                    write!(f, "#!")?; // Preamble.
                    fmt_path(path, f)?; // Path.

                    // Escape the whole line if there is a colon, or if it by some weird coincidence
                    // matches our escape sequence.
                    let has_escape_sequence = line.starts_with("#`") && line.ends_with("`#");
                    let mut chars = line.chars();
                    // Also escape the line if it is surrounded by whitespace that would be stripped
                    // away by our parser.
                    let first_whitespace =
                        chars.next().map(|it| it.is_whitespace()).unwrap_or(false);
                    let last_whitespace =
                        chars.last().map(|it| it.is_whitespace()).unwrap_or(false);
                    let has_whitespace = first_whitespace || last_whitespace;
                    if line.contains(':') || has_escape_sequence || has_whitespace {
                        writeln!(f, "#`{}`#", line)?;
                    } else {
                        writeln!(f, "{}", line)?;
                    }
                }
            }
        }

        // Keys are explored in deterministic order:
        let mut keys = self.inner.keys().collect::<Vec<_>>();
        keys.sort();
        for key in keys {
            path.push(key.as_str());
            let child = self.inner.get(key).unwrap();
            child.fmt_with_path(path, f)?;
            path.pop();
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use crate::ModelAnnotation;

    #[test]
    pub fn annotation_read_write_test() {
        let mut annotations = ModelAnnotation::new();
        // "root" annotation
        annotations.ensure_value::<&str>(&[], "hello");
        // normal annotation
        annotations.ensure_value(&["name"], "Model name");
        // Empty key and value
        annotations.ensure_value(&["var", "", "x"], "");
        // Escaped names and values
        annotations.ensure_value(&["var {list}"], "Hello: there");
        // Multiline values
        annotations.ensure_value(&["multi_line"], " Hello\n\nWorld: #`Some escaped text`#.");

        let string = annotations.to_string();
        let parsed = ModelAnnotation::from_model_string(string.as_str());

        assert_eq!(annotations, parsed);
    }
}
