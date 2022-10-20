use crate::trap_spaces::OptionalExtendedBoolean::{Any, One, Unknown, Zero};
use crate::trap_spaces::{ExtendedBoolean, OptionalExtendedBoolean, PartialSpace, Space};
use crate::{BooleanNetwork, VariableId};
use std::collections::HashSet;
use std::fmt::{Display, Formatter};
use std::ops::{Index, IndexMut};

impl Index<VariableId> for PartialSpace {
    type Output = OptionalExtendedBoolean;

    fn index(&self, index: VariableId) -> &Self::Output {
        &self.0[index.to_index()]
    }
}

impl IndexMut<VariableId> for PartialSpace {
    fn index_mut(&mut self, index: VariableId) -> &mut Self::Output {
        &mut self.0[index.to_index()]
    }
}

impl Display for PartialSpace {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        for x in &self.0 {
            write!(f, "{}", x)?;
        }
        Ok(())
    }
}

impl PartialSpace {
    pub fn new_unknown(network: &BooleanNetwork) -> PartialSpace {
        PartialSpace(vec![Unknown; network.num_vars()])
    }

    /// Create a `Space` object by fixing all "unknown" values (`?`) to "any" values (`*`).
    pub fn to_space(self) -> Space {
        Space(
            self.0
                .into_iter()
                .map(|it| match it {
                    Zero => ExtendedBoolean::Zero,
                    One => ExtendedBoolean::One,
                    Any | Unknown => ExtendedBoolean::Any,
                })
                .collect(),
        )
    }

    /// Try to convert this partial space to an exact space without performing any changes.
    /// (That is, the conversion succeeds if there are no unknown values in this space)
    pub fn try_as_space(&self) -> Option<Space> {
        if self.count_unknown() == 0 {
            Some(self.clone().to_space())
        } else {
            None
        }
    }

    /// Count the number of variables whose value is still "unknown" in this partial space.
    pub fn count_unknown(&self) -> usize {
        self.0.iter().filter(|it| **it == Unknown).count()
    }

    /// Create a collection of all variables that are still unknown in this space.
    pub fn unknown_variables(&self) -> HashSet<VariableId> {
        let mut result = HashSet::new();
        for i in 0..self.0.len() {
            if self.0[i] == Unknown {
                result.insert(VariableId::from_index(i));
            }
        }
        result
    }

    /// Perform constant propagation on all the "unknown" values in this `PartialSpace`.
    ///
    /// In particular, this can only "narrow down" the "unknown" values (`?`). It will not try to
    /// fix the "any" values (`*`), even if there is a constant the value would propagate to.
    ///
    /// Also note that while the result of such propagation is never empty, it is guaranteed
    /// to be a trap space only if the input is also a trap space.
    pub fn constant_propagation(mut self, network: &BooleanNetwork) -> PartialSpace {
        'propagation: loop {
            for var in network.variables() {
                if self[var] == Unknown {
                    if let Some(update) = network.get_update_function(var) {
                        let propagated = update.eval_in_partial_space(&self);
                        if propagated != Unknown {
                            self[var] = propagated;
                            continue 'propagation;
                        }
                    }
                }
            }

            return self;
        }
    }

    /// Check if this `PartialSpace` has a **conflict variable** that prevents it from specializing
    /// into a trap space (with respect to the given `BooleanNetwork`).
    ///
    /// A "conflict variable" is a specific BN variable that can always be updated, and where the
    /// update always leads outside of the given `Space`. In other words, from every state, one
    /// can escape this `Space` in a single step using this variable.
    ///
    /// Note that a space with a conflict variable cannot be a trap space. However, a space that
    /// is not a trap space may not have a single conflict variable, even if every state can
    /// escape this `Space` in one step.
    pub fn trap_conflict_variable(&self, network: &BooleanNetwork) -> Option<Space> {
        for var in network.variables() {
            let expected_value = self[var];
            if expected_value.is_fixed() {
                if let Some(update) = network.get_update_function(var) {
                    let actual_value = update.eval_in_partial_space(self);
                    if actual_value.is_fixed() && actual_value != expected_value {
                        let regulators = network.graph.regulators(var);
                        let mut conflict_space = self.clone().to_space();
                        for erase in network.variables() {
                            if erase == var {
                                // We also have to keep this intact.
                                continue;
                            }
                            if !regulators.contains(&erase) {
                                conflict_space[erase] = ExtendedBoolean::Any;
                            }
                        }
                        return Some(conflict_space);
                        //return Some(var);
                    } else {
                        // If actual value is "any", then *this* space is not a trap space, but
                        // the variable is not conflicting either. There can be a smaller
                        // *subspace* inside this space that is still a trap.
                    }
                } else {
                    // If the function is unknown, then this is also not a trap space, but
                    // it does not guarantee that the variable is conflicting---that depends
                    // on the eventually chosen function.
                }
            }
        }
        None
    }

    pub fn try_subtract(&mut self, space: &Space) -> bool {
        let mut subtract_on = None;
        for i in 0..self.0.len() {
            match (self.0[i], space.0[i]) {
                (_, ExtendedBoolean::Any) => (),
                (Zero, ExtendedBoolean::Zero) | (One, ExtendedBoolean::One) => (),
                (One, ExtendedBoolean::Zero) | (Zero, ExtendedBoolean::One) => return false,
                (Any, _) | (Unknown, _) => {
                    if subtract_on.is_some() {
                        return false;
                    }
                    subtract_on = Some(i);
                }
            }
        }
        if let Some(i) = subtract_on {
            if space.0[i] == ExtendedBoolean::One {
                self.0[i] = Zero
            } else {
                self.0[i] = One
            }

            true
        } else {
            false
        }
    }
}
