use std::hash::Hash;

/// A marker trait for anything that can be a state of a graph.
///
/// Currently, we require each state to be a `Copy` struct, i.e. it has to be
/// "small enough" so that it can be copied whenever needed. In the future, we might
/// lift this restriction if the need for more complex states arises. Meanwhile, one
/// can use dynamically indexed states.
pub trait State: Hash + Eq + Clone + Copy {}

/// A very basic implementation of a `State` which simply stores a single `usize` id.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct IdState(usize);
impl State for IdState {}
impl From<usize> for IdState {
    fn from(val: usize) -> Self {
        return IdState(val);
    }
}
impl Into<usize> for IdState {
    fn into(self) -> usize {
        return self.0;
    }
}

impl IdState {
    pub fn get_bit(self, bit: usize) -> bool {
        return (self.0 >> bit) & 1 == 1;
    }

    pub fn flip_bit(self, bit: usize) -> IdState {
        return IdState(self.0 ^ (1 << bit));
    }
}

/// `EvolutionOperator`s represent an evolution of non-deterministic dynamical system with
/// discrete time, i.e. given a current state, they provide possible states in the next time step.
pub trait EvolutionOperator {
    type State: State;
    type Iterator: Iterator<Item = Self::State>;
    fn step(&self, current: Self::State) -> Self::Iterator;
}

/// `Graph` is a dynamical system with finite state space which can be explored forward
/// and backward in time.
pub trait Graph {
    type State: State;
    type States: Iterator<Item = Self::State>;
    type FwdEdges: EvolutionOperator;
    type BwdEdges: EvolutionOperator;

    fn states(&self) -> Self::States;
    fn fwd(&self) -> Self::FwdEdges;
    fn bwd(&self) -> Self::BwdEdges;
}

/// `StateSet` is a collection of states.
pub trait StateSet {
    type State: State;
    type Iterator: Iterator<Item = Self::State>;

    fn iter(&self) -> Self::Iterator;
    fn contains(&self, state: &Self::State) -> bool;
}

pub mod param {
    use crate::biodivine_std::State;

    /// `Params` represents a set of parameter valuations and thus typically behaves like a
    /// normal set.
    ///
    /// However, notice that there is no complement method available. This is because the
    /// `unit` set of parameters can be different every time or completely completely. To
    /// implement complement, use `minus` with an appropriate `unit` set.
    ///
    /// Also notice that we do not assume anything about the members of the set, we can't
    /// iterate them or even retrieve them. This is because the sets might be uncountable
    /// or the elements might not be well representable.
    pub trait Params: Clone {
        fn union(&self, other: &Self) -> Self;
        fn intersect(&self, other: &Self) -> Self;
        fn minus(&self, other: &Self) -> Self;

        fn is_empty(&self) -> bool;
        fn is_subset(&self, other: &Self) -> bool;
    }

    /// A parametrised variant of an `EvolutionOperator`. For each state, a `Params` set is
    /// returned as well which gives the set of parameter valuations for which the transition
    /// is allowed.
    pub trait EvolutionOperator {
        type State: State;
        type Params: Params;
        // TODO: There could be a discussion whether iterator should own the params objects or not just reference them.
        type Iterator: Iterator<Item = (Self::State, Self::Params)>;
        fn step(&self, current: Self::State) -> Self::Iterator;
    }

    /// A parametrised variant of a `Graph`.
    pub trait Graph {
        type State: State;
        type Params: Params;
        type States: Iterator<Item = Self::State>;
        type FwdEdges: EvolutionOperator;
        type BwdEdges: EvolutionOperator;

        fn states(&self) -> Self::States;
        fn fwd(&self) -> Self::FwdEdges;
        fn bwd(&self) -> Self::BwdEdges;
    }

    /// A parametrised variant of a `StateSet`.
    pub trait StateSet {
        type State: State;
        type Params: Params;
        type Iterator: Iterator<Item = (Self::State, Self::Params)>;

        fn iter(&self) -> Self::Iterator;
        fn contains(&self, state: Self::State) -> &Self::Params;
    }
}
