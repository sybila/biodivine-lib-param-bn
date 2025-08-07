//! Bitvectors are simply sequences of boolean values. However, since they are used quite often
//! and in some very specific applications, we provide a unified optimized interface for them.
//!
//! Note that there is a ton of rust libraries which implement bitvectors (and indeed, we are
//! deferring to some of them for larger bit vectors). However, we wanted to avoid relying on
//! a specific library for this in order to provide a more unified API.
//!
//! AFAIK, `BitVector` is not used in any truly performance critical code, but there
//! are some concerns for overall memory consumption and efficiency.
//!
//! ```rust
//! use biodivine_lib_param_bn::biodivine_std::bitvector::{BitVector58, BitVector};
//! // Create a BitVector of length 4 initialized to false.
//! let mut bv = BitVector58::empty(4);
//! assert_eq!(4, bv.len());
//! bv.flip(1); // Invert value at given index.
//! bv.set(2, true); // Set value at index to a constant.
//! assert!(bv.get(1));
//! assert!(!bv.get(3));
//! // Should print BV(4)[1 2] using default `Display` implementation.
//! println!("{}", bv);
//! ```
//!
//! ### `BitVector` conversions
//!
//! Mostly for utility purposes (as this is not very efficient), every `BitVector` provides
//! conversion to and from `Vec<bool>` (exact representation of the values in the `BitVector`)
//! and `Vec<usize>` (indices of `true` item in the `BitVector`).
//!
//! ```rust
//! // Convert bool vector to BitVector.
//! use biodivine_lib_param_bn::biodivine_std::bitvector::{BitVector58, BitVector};
//! let bv = BitVector58::from(vec![false, true, true, false]);
//! // And back to bool vector.
//! assert_eq!(vec![false, true, true, false], bv.values());
//! // Convert index vector to BitVector.
//! assert_eq!(bv, BitVector58::from_ones(4, vec![1,2]));
//! // And also back to an index vector.
//! assert_eq!(vec![1,2], bv.ones());
//! // Inverted index vector is also available.
//! assert_eq!(vec![0,3], bv.zeros());
//! ```
//!
//! We recommend that users of bit vectors wrap these conversion utilities in more appropriate
//! methods aimed at the specific use case (e.g. substituting `usize` for domain specific
//! values).

use std::fmt::{Display, Formatter};

mod _impl_array_bit_vector;
mod _impl_bit_vector_58;

/// `BitVector` is a collection of boolean values of a fixed length.
///
/// When implementing `Display` and `From<Vec<bool>>`, please consult `BitVector::display` and
/// `BitVector::from_bool_vector`.
pub trait BitVector: Clone + Eq + Display + From<Vec<bool>> {
    /// If a `BitVector` implementation cannot handle arbitrary vector lengths, it can use this
    /// method to declare the largest bitvector it can handle.
    fn max_length() -> usize {
        usize::MAX
    }

    /// Create a new `BitVector` with the given length. Can panic if this implementation
    /// does not support the specified length. Once created, the length cannot be changed.
    fn empty(len: usize) -> Self;

    /// Create a new `BitVector` which contains `items` specified in the given vector.
    fn from_ones(len: usize, items: Vec<usize>) -> Self {
        let mut bits = Self::empty(len);
        for i in items {
            bits.set(i, true);
        }
        bits
    }

    /// The number of elements stored in this `BitVector`.
    fn len(&self) -> usize;

    /// Get the boolean value at the given `index`.
    fn get(&self, index: usize) -> bool;

    /// Set the boolean `value` at the given `index`.
    fn set(&mut self, index: usize, value: bool);

    /// Invert the value at the given `index`.
    fn flip(&mut self, index: usize);

    /// Return a vector of the values in this `BitVector`.
    fn values(&self) -> Vec<bool> {
        (0..self.len()).map(|i| self.get(i)).collect()
    }

    /// A vector of the indices of this `BitVector` which are set.
    fn ones(&self) -> Vec<usize> {
        (0..self.len()).filter(|i| self.get(*i)).collect()
    }

    /// A vector of the indices of this `BitVector` which are *not* set.
    fn zeros(&self) -> Vec<usize> {
        (0..self.len()).filter(|i| !self.get(*i)).collect()
    }

    /// A helper method for `Display` trait implementations for all variants of `BitVector`. Please
    /// use this method (or an equivalent display format) for all `Display` implementations of
    /// `BitVector`s.
    ///
    /// If you wish to provide a custom display format, wrap the `BitVector` into some
    /// domain-specific struct and implement a different `Display` for this struct. By
    /// providing this default implementation, we are ensuring that all `BitVector`
    /// implementations are "visually indistinguishable" to the user.
    ///
    /// You are still free to provide your own domain-specific `Debug` display method though!
    fn display(&self, f: &mut Formatter<'_>) -> Result<(), std::fmt::Error> {
        write!(f, "BV({})[", self.len())?;
        let mut first = true;
        for i in 0..self.len() {
            if self.get(i) {
                if !first {
                    write!(f, " ")?;
                }
                write!(f, "{i}")?;
                first = false;
            }
        }
        write!(f, "]")?;
        Ok(())
    }

    /// A helper method for converting a vector of Booleans into a `BitVector`. Useful when
    /// implementing `From<Vec<bool>>`.
    fn from_bool_vector(items: Vec<bool>) -> Self {
        let mut bits = Self::empty(items.len());
        for (i, val) in items.iter().enumerate() {
            if *val {
                bits.set(i, true);
            }
        }
        bits
    }

    fn is_empty(&self) -> bool {
        self.len() == 0
    }
}

/// A `BitVector` implementation that uses the explicit implementation from the `bitvector` crate.
#[derive(Clone, PartialEq)]
pub struct ArrayBitVector {
    len: usize,
    values: bitvector::BitVector,
}

/// A `BitVector` implementation that uses `u64` as the underlying representation and
/// can therefore hold only up-to 58 values (remaining 6 bits store the vector length).
/// Should be pretty fast though.
///
/// `BitVector58` is also `Copy`, because it is small enough to pass by value.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct BitVector58(u64);
