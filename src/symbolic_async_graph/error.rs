/// An error which is returned when a BDD operation exceeds a specified size limit.
#[derive(Debug, Clone, Eq, PartialEq)]
pub struct SizeLimitExceeded {
    limit: usize,
}

impl SizeLimitExceeded {
    /// Create a new error instance with the given limit.
    pub fn new(limit: usize) -> SizeLimitExceeded {
        SizeLimitExceeded { limit }
    }

    /// The limit that was exceeded.
    pub fn limit(&self) -> usize {
        self.limit
    }
}

impl std::fmt::Display for SizeLimitExceeded {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "BDD size limit {} exceeded.", self.limit)
    }
}

impl std::error::Error for SizeLimitExceeded {}
