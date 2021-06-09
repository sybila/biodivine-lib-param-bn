//! **(internal)** This module implements functions for creating `Bdd`s corresponding
//! to the static constraints of the individual regulations of a `BooleanNetwork`.

use crate::bdd_params::BddParameterEncoder;
use crate::biodivine_std::structs::IdState;
use crate::{BooleanNetwork, FnUpdate, Monotonicity, Regulation, VariableId};
use biodivine_lib_bdd::{bdd, Bdd};
use std::ops::Range;

/// Build a `Bdd` which describes all valuations satisfying the static constraints
/// of the given `BooleanNetwork`.
pub fn build_static_constraints(bn: &BooleanNetwork, encoder: &BddParameterEncoder) -> Bdd {
    let mut condition = encoder.bdd_variables.mk_true();
    let ctx = Ctx::new(bn, encoder);
    for r in &bn.graph.regulations {
        if let Some(fun) = bn.get_update_function(r.target) {
            if r.monotonicity != None {
                let monotonicity = build_monotonicity_explicit(&ctx, r, fun);
                condition = bdd!(condition & monotonicity);
                if condition.is_false() {
                    println!(
                        "Regulation {} -> {} is not monotonous.",
                        bn.graph.get_variable(r.regulator).name,
                        bn.graph.get_variable(r.target).name
                    );
                    break;
                }
            }
            if r.observable {
                let observability = build_observability_explicit(&ctx, r, fun);
                condition = bdd!(condition & observability);
                if condition.is_false() {
                    println!(
                        "Regulation {} -> {} is not observable.",
                        bn.graph.get_variable(r.regulator).name,
                        bn.graph.get_variable(r.target).name
                    );
                    break;
                }
            }
        } else {
            if r.monotonicity != None {
                let monotonicity = build_monotonicity_implicit(&ctx, r);
                condition = bdd!(condition & monotonicity);
                if condition.is_false() {
                    println!(
                        "Regulation {} -> {} is not monotonous.",
                        bn.graph.get_variable(r.regulator).name,
                        bn.graph.get_variable(r.target).name
                    );
                    break;
                }
            }
            if r.observable {
                let observability = build_observability_implicit(&ctx, r);
                condition = bdd!(condition & observability);
                if condition.is_false() {
                    println!(
                        "Regulation {} -> {} is not observable.",
                        bn.graph.get_variable(r.regulator).name,
                        bn.graph.get_variable(r.target).name
                    );
                    break;
                }
            }
        }
    }
    condition
}

struct Ctx<'a> {
    bn: &'a BooleanNetwork,
    encoder: &'a BddParameterEncoder,
}

impl<'a> Ctx<'a> {
    pub fn new(bn: &'a BooleanNetwork, encoder: &'a BddParameterEncoder) -> Ctx<'a> {
        Ctx { bn, encoder }
    }

    /// Transform a table pair into pair of `Bdd`s assuming an update function is known.
    pub fn pair_explicit(&self, states: (IdState, IdState), fun: &'a FnUpdate) -> (Bdd, Bdd) {
        let (inactive, active) = states;
        let inactive = fun._symbolic_eval(inactive, self.encoder);
        let active = fun._symbolic_eval(active, self.encoder);
        (inactive, active)
    }

    /// Transform a table pair into a pair of `Bdd`s assuming an implicit update function.
    pub fn pair_implicit(&self, states: (IdState, IdState), variable: VariableId) -> (Bdd, Bdd) {
        let (inactive, active) = states;
        let inactive = self.encoder.get_implicit(inactive, variable);
        let active = self.encoder.get_implicit(active, variable);
        let inactive = self.encoder.bdd_variables.mk_var(inactive);
        let active = self.encoder.bdd_variables.mk_var(active);
        (inactive, active)
    }
}

fn build_monotonicity_implicit<'a>(ctx: &Ctx<'a>, regulation: &'a Regulation) -> Bdd {
    let mut condition = ctx.encoder.bdd_variables.mk_true();
    for states in InputStatesPairIterator::new(ctx.bn, regulation) {
        let (inactive, active) = ctx.pair_implicit(states, regulation.target);
        let monotonous =
            build_monotonicity_pair(&inactive, &active, regulation.monotonicity.unwrap());
        condition = bdd!(condition & monotonous);
    }
    condition
}

fn build_observability_implicit<'a>(ctx: &Ctx<'a>, regulation: &'a Regulation) -> Bdd {
    let mut condition = ctx.encoder.bdd_variables.mk_false();
    for states in InputStatesPairIterator::new(ctx.bn, regulation) {
        let (inactive, active) = ctx.pair_implicit(states, regulation.target);
        condition = bdd!(condition | (!(inactive <=> active)));
    }
    condition
}

fn build_monotonicity_explicit<'a>(
    ctx: &Ctx<'a>,
    regulation: &'a Regulation,
    update_function: &'a FnUpdate,
) -> Bdd {
    let mut condition = ctx.encoder.bdd_variables.mk_true();
    for states in InputStatesPairIterator::new(ctx.bn, regulation) {
        let (inactive, active) = ctx.pair_explicit(states, update_function);
        let monotonous =
            build_monotonicity_pair(&inactive, &active, regulation.monotonicity.unwrap());
        condition = bdd!(condition & monotonous);
    }
    condition
}

fn build_observability_explicit<'a>(
    ctx: &Ctx<'a>,
    regulation: &'a Regulation,
    update_function: &'a FnUpdate,
) -> Bdd {
    let mut condition = ctx.encoder.bdd_variables.mk_false();
    for states in InputStatesPairIterator::new(ctx.bn, regulation) {
        let (inactive, active) = ctx.pair_explicit(states, update_function);
        condition = bdd!(condition | (!(inactive <=> active)));
    }
    condition
}

/// **(internal)** Iterates over pairs of states where the first state has a particular regulator
/// variable set to zero while the second state has it set to one.
///
/// The pairs cover all possible inputs into an associated update function such that
/// the alternated variable is one of the inputs of the function.
struct InputStatesPairIterator {
    range: Range<usize>,
    mask: usize,
    regulators: Vec<VariableId>,
    variable: VariableId,
}

impl Iterator for InputStatesPairIterator {
    type Item = (IdState, IdState);

    fn next(&mut self) -> Option<Self::Item> {
        for next_index in &mut self.range {
            if next_index & self.mask != 0 {
                continue;
            } else {
                // this is an inactive index
                let state = extend_table_index_to_state(next_index, &self.regulators);
                return Some((state, state.flip_bit(self.variable.0)));
            }
        }
        None
    }
}

impl InputStatesPairIterator {
    pub fn new(bn: &BooleanNetwork, regulation: &Regulation) -> InputStatesPairIterator {
        let regulators = bn.graph.regulators(regulation.target);
        let regulator_index = regulators
            .iter()
            .position(|v| *v == regulation.regulator)
            .unwrap();
        let table_size = 1 << regulators.len();
        let mask = 1 << regulator_index; // select the regulator bit of the table index
        InputStatesPairIterator {
            regulators,
            variable: regulation.regulator,
            mask,
            range: (0..table_size),
        }
    }
}

/// **(internal)** Build a state which has the variables set exactly as in the `table_index` and
/// all other variables set to zero.
///
/// index: 0110, args: (0, 3, 5, 6) -> 0101000
/// index: abcd, args: (0, 3, 5, 6) -> dc0b00a
fn extend_table_index_to_state(table_index: usize, args: &[VariableId]) -> IdState {
    let mut state: usize = 0;
    for (i, regulator) in args.iter().enumerate() {
        if (table_index >> i) & 1 == 1 {
            // If we have one in the table index
            // then we also put one in the state,
            // but on the correct position.
            state |= 1 << regulator.0;
        }
    }
    IdState::from(state)
}

/// **(internal)** Builds a `Bdd` of parameters corresponding to valuations where the given
/// pair of function entries behaves monotonously.
fn build_monotonicity_pair(inactive: &Bdd, active: &Bdd, monotonicity: Monotonicity) -> Bdd {
    match monotonicity {
        // increasing: [f(0) = 1] => [f(1) = 1]
        Monotonicity::Activation => bdd!(inactive => active),
        // decreasing: [f(0) = 0] => [f(1) = 0] which is equivalent to [f(0) = 1] => [f(1) = 1]
        Monotonicity::Inhibition => bdd!(active => inactive),
    }
}
