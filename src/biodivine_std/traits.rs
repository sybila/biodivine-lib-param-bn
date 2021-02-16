/// Basic traits which are carried over from lib-biodivine_std for now.
///
/// In the future, these will be replaced by a more stable variants.
use std::hash::Hash;

/// **Deprecated** marker trait for anything that can be a state of a graph.
///
/// Currently, we require each state to be a `Copy` struct, i.e. it has to be
/// "small enough" so that it can be copied whenever needed. In the future, we might
/// lift this restriction if the need for more complex states arises. Meanwhile, one
/// can use dynamically indexed states.
pub trait State: Hash + Eq + Clone + Copy {}

/// A very basic set trait.
///
/// Notice that we do not assume anything about the members of the set, we can't
/// iterate them or even retrieve them. This is because the sets might be uncountable
/// or the elements might not be well representable.
///
/// Also notice that there is no complement method available. This is because the
/// `unit` set can be different every time or completely unknown. To
/// implement complement, use `minus` with an appropriate `unit` set.
pub trait Set: Clone {
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
    type Params: Set;
    type Iterator: Iterator<Item = (Self::State, Self::Params)>;
    fn step(&self, current: Self::State) -> Self::Iterator;
}

/// A variant of the `EvolutionOperator` that can be inverted.
///
/// This is useful if you have algorithms that need to follow edges in both directions but have
/// some "preferred" sense of direction. For example, a model checking algorithm can verify
/// formulas that mix past and future. It typically starts in "future" mode, but can switch
/// to "past" depending on the formula. If the operator is invertible, one can just
/// invert the evolution operator in the algorithm without caring whether we are working on
/// past or future. In other words, the sense of time is relative.
///
/// Technically, this can be also achieved by switching between `fwd` and `bwd` in the algorithm,
/// but that can be cumbersome because the sense of "direction" becomes diluted. In other words,
/// it is easy to lose track of what is going on if you see something like `let fwd = bwd;`...
pub trait InvertibleEvolutionOperator: EvolutionOperator {
    type InvertedOperator: EvolutionOperator<State = Self::State, Params = Self::Params>;
    fn invert(&self) -> Self::InvertedOperator;
}

/// A parametrised variant of a `Graph`.
pub trait Graph {
    type State: State;
    type Params: Set;
    type States: Iterator<Item = Self::State>;
    type FwdEdges: EvolutionOperator;
    type BwdEdges: EvolutionOperator;

    fn states(&self) -> Self::States;
    fn fwd(&self) -> Self::FwdEdges;
    fn bwd(&self) -> Self::BwdEdges;
}

pub trait InvertibleGraph: Graph {
    type FwdEdges: InvertibleEvolutionOperator;
    type BwdEdges: InvertibleEvolutionOperator;
}
