use regex::Regex;

/// **(internal)** Implements basic utility methods for `ModelAnnotation`.
pub mod _impl_annotation;
/// **(internal)** Implements annotation parsing.
pub mod _impl_reader;
/// **(internal)** Implements annotation `to_string` writer.
pub mod _impl_writer;

lazy_static! {
    /// Matches the beginning of a string if it represents a valid alphanumeric
    /// path segment (including the `:` separator).
    static ref SIMPLE_PATH_SEGMENT: regex::Regex = Regex::new("^\\s*([a-zA-Z0-9_]*)\\s*:").unwrap();

    /// Matches the beginning of a string if it represents an escaped
    /// path segment (including the `:` separator).
    static ref ESC_PATH_SEGMENT: regex::Regex = Regex::new("^\\s*`([^`]*)`\\s*:").unwrap();

    /// Matches a string that consists only of alphanumeric characters and underscores.
    static ref ALPHANUMERIC: regex::Regex = Regex::new("^[a-zA-Z0-9_]*$").unwrap();

}

/// Panic if the path segment name is invalid.
fn validate_path_segment(path: &str) {
    // TODO:
    //  This is woefully incomplete. People can still fit A LOT of trash into this definition.
    //  Ideally, we should specify a supported list of "escape-able" characters instead.
    if path.contains('`') {
        panic!(
            "Annotation path segments cannot contain backtick. Current segment: \"{}\".",
            path
        );
    }
    if path.contains('\n') {
        panic!(
            "Annotation path segments cannot contain a newline. Current segment: \"{}\".",
            path
        );
    }
}
