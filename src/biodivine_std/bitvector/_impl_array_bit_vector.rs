use crate::biodivine_std::bitvector::{ArrayBitVector, BitVector};
use std::fmt::{Debug, Display, Formatter};

/* Not sure why bitvector::BitVector does not implement Eq, but we want to. */
impl Eq for ArrayBitVector {}

impl ArrayBitVector {
    /// **(internal)** Check if the given index is valid in this `BitVector` - panic otherwise.
    /// Only enabled when `shields_up` is set.
    fn check_access(&self, index: usize) {
        if cfg!(shields_up) && index >= self.len {
            panic!(
                "Accessing element {} in a BitVector of length {}.",
                index, self.len
            );
        }
    }
}

impl BitVector for ArrayBitVector {
    fn empty(len: usize) -> Self {
        return ArrayBitVector {
            len,
            values: bitvector::BitVector::new(len),
        };
    }

    fn len(&self) -> usize {
        return self.len;
    }

    fn get(&self, index: usize) -> bool {
        self.check_access(index);
        return self.values.contains(index);
    }

    fn set(&mut self, index: usize, value: bool) {
        self.check_access(index);
        if value {
            self.values.insert(index);
        } else {
            self.values.remove(index);
        }
    }

    fn flip(&mut self, index: usize) {
        self.check_access(index);
        if self.values.contains(index) {
            self.values.remove(index);
        } else {
            self.values.insert(index);
        }
    }

    fn ones(&self) -> Vec<usize> {
        // slightly more efficient than default implementation
        return self.values.iter().collect();
    }
}

impl Display for ArrayBitVector {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), std::fmt::Error> {
        return self.display(f);
    }
}

impl From<Vec<bool>> for ArrayBitVector {
    fn from(data: Vec<bool>) -> Self {
        return Self::from_bool_vector(data);
    }
}

impl Debug for ArrayBitVector {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), std::fmt::Error> {
        write!(f, "ArrayBitVector({})[", self.len)?;
        let mut first = true;
        for i in 0..self.len() {
            if self.get(i) {
                if !first {
                    write!(f, " ")?;
                }
                write!(f, "{}", i)?;
                first = false;
            }
        }
        write!(f, "]")?;
        return Ok(());
    }
}

#[cfg(test)]
mod tests {
    use crate::biodivine_std::bitvector::{ArrayBitVector, BitVector};

    #[test]
    fn test_array_bit_vector() {
        let mut bv = ArrayBitVector::empty(10);
        assert_eq!(vec![false; 10], bv.values());
        bv.set(2, true);
        bv.flip(6);
        assert!(bv.get(2));
        assert!(bv.get(6));
        assert_eq!(vec![2, 6], bv.ones());
        assert_eq!(vec![0, 1, 3, 4, 5, 7, 8, 9], bv.zeros());
        assert_eq!(bv, ArrayBitVector::from_ones(10, vec![2, 6]));
        assert_eq!(
            bv,
            ArrayBitVector::from(vec![
                false, false, true, false, false, false, true, false, false, false
            ])
        );
        println!("{:?} is displayed as {}", bv, bv);
        bv.set(6, false);
        assert!(!bv.get(6));
        bv.flip(2);
        assert!(!bv.get(2));
    }

    #[test]
    #[should_panic]
    #[cfg(shields_up)]
    fn test_array_bit_vector_invalid_access() {
        let mut b = ArrayBitVector::empty(80);
        b.flip(100);
    }
}
