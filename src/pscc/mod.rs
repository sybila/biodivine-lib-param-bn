/*
   Design principles: all sets are over a common BDD variable universe where we have
   parameter variables followed by state variables (this allows simple pivot selection).

   In color sets, the state variables are ignored (so a color set A is represented as `A x V`)
   and in vertex sets, the color variables are ignored (so `C x A`). This does not influence
   normal set operations.
*/

use crate::bdd_params::{build_static_constraints, BddParameterEncoder};
use crate::{BooleanNetwork, VariableId};
use biodivine_lib_bdd::{bdd, BddValuation};
use biodivine_lib_bdd::{
    Bdd, BddValuationIterator, BddVariable, BddVariableSet, BddVariableSetBuilder,
};
use biodivine_lib_std::IdState;
use rayon::prelude::*;
use std::io;
use std::io::Write;
use std::ops::Shl;

// higher = more verbose
const LOG_LEVEL: usize = 3;
const TRIM_CUTOFF: bool = false;

pub struct PsccContext {
    network: BooleanNetwork,
    /// All BDD variables representing the parameters and variables of the system.
    bdd_variables: BddVariableSet,
    state_variables: Vec<BddVariable>,
    /// Number of parameter variables.
    p_count: u16,
    /// For every update function, store !v <=> function (for faster analysis)
    update_function_cache: Vec<Bdd>,
    universe: Bdd,
}

impl PsccContext {
    pub fn new(bn: BooleanNetwork) -> PsccContext {
        let mut bdd = BddVariableSetBuilder::new();
        let mut explicit_function_tables: Vec<Vec<BddVariable>> = Vec::new();
        let mut implicit_function_tables: Vec<Vec<BddVariable>> = Vec::new();
        let mut state_variables: Vec<BddVariable> = Vec::new();
        let mut regulators: Vec<Vec<VariableId>> = Vec::new();

        // First, create variables for all the explicit parameters:
        for pid in bn.parameter_ids() {
            let p = bn.get_parameter(pid);
            // Here, we abuse BddValuationIterator to go over all possible valuations
            // of function inputs.

            let p_vars = BddValuationIterator::new(p.cardinality as u16)
                .map(|valuation| {
                    let bdd_name = format!("{}{}", p.name, valuation);
                    bdd.make_variable(&bdd_name)
                })
                .collect();

            explicit_function_tables.push(p_vars);
        }

        // Then create values for anonymous parameters:
        for vid in bn.graph.variable_ids() {
            let v = bn.graph.get_variable(vid);

            if let Some(_) = bn.get_update_function(vid) {
                regulators.push(Vec::new());
                implicit_function_tables.push(Vec::new());
            } else {
                let args = bn.graph.regulators(vid);
                let cardinality = args.len();
                regulators.push(args);

                // Note that if args are empty, one variable is still created because there is
                // an "empty" valuation.
                let p_vars = BddValuationIterator::new(cardinality as u16)
                    .map(|valuation| {
                        let bdd_name = format!("\\{{{}}}{}", v.name, valuation);
                        bdd.make_variable(&bdd_name)
                    })
                    .collect();

                implicit_function_tables.push(p_vars);
            }
        }

        // Now create values for state variables
        for v in &bn.graph.variables {
            let bdd_v = bdd.make_variable(&format!("{}", v.name));
            state_variables.push(bdd_v);
        }

        let bdd_variables = bdd.build();

        let fake_encoder = BddParameterEncoder {
            // since we first have params and then states, this works...
            bdd_variables: bdd_variables.clone(),
            regulators,
            explicit_function_tables: explicit_function_tables.clone(),
            implicit_function_tables: implicit_function_tables.clone(),
        };

        let universe = build_static_constraints(&bn, &fake_encoder);
        println!("BDD vars: {}", bdd_variables.num_vars());
        println!("State space size: {}", (1.shl(state_variables.len()) as f64));
        println!("Param. universe cardinality: {}", universe.cardinality() / (1.shl(state_variables.len()) as f64));

        let mut function_cache = Vec::new();
        for v in bn.graph.variable_ids() {
            let regulators = bn.graph.regulators(v);
            let mut function_is_one = bdd_variables.mk_true();
            if let Some(function) = bn.get_update_function(v) {
                // When there is an explicit update function, we have to eval it one valuation at a time:
                let valuations: Vec<BddValuation> = BddValuationIterator::new(regulators.len() as u16).collect();
                let row_bdds: Vec<Bdd> = valuations
                    .into_par_iter()
                    .map(|valuation| {
                        let valuation_vector = valuation.vector();
                        let valuation_bdd = Self::extend_valuation_to_bdd(
                            &bdd_variables,
                            &state_variables,
                            &valuation_vector,
                            &regulators,
                        );
                        let valuation_state =
                            Self::extend_valuation_to_id_state(&valuation_vector, &regulators);
                        let function_is_one_in_valuation: Bdd =
                            function._symbolic_eval(valuation_state, &fake_encoder);
                        bdd!(valuation_bdd => function_is_one_in_valuation)
                    })
                    .collect();
                function_is_one = par_intersect(row_bdds);
                /*for valuation in BddValuationIterator::new(regulators.len() as u16) {

                    function_is_one =
                        bdd!(function_is_one & (valuation_bdd => function_is_one_in_valuation));
                    if LOG_LEVEL > 0 { println!("(Partial) update function: {:?}", valuation_vector) }
                }*/
            } else {
                // When the update function is implicit, we just combine all (valuation => parameter):
                let table = &implicit_function_tables[v.0];
                let mut i = 0;
                for valuation in BddValuationIterator::new(regulators.len() as u16) {
                    let valuation_bdd = Self::extend_valuation_to_bdd(
                        &bdd_variables,
                        &state_variables,
                        &valuation.vector(),
                        &regulators,
                    );
                    let parameter = table[i];
                    let parameter_bdd = bdd_variables.mk_var(parameter);
                    function_is_one = bdd!(function_is_one & (valuation_bdd => parameter_bdd));
                    i += 1;
                }
            }
            let v_bdd_var = state_variables[v.0];
            let v_is_zero = bdd_variables.mk_not_var(v_bdd_var);
            function_cache.push(bdd!(v_is_zero <=> function_is_one));
            if LOG_LEVEL > 0 { println!("Update function ready: {:?}", v); }
        }

        /*for u in &update_functions {
            println!("Update function: ");
            println!("{}", u.to_dot_string(&bdd_variables, true));
        }*/

        return PsccContext {
            p_count: bdd_variables.num_vars() - (bn.graph.num_vars() as u16),
            network: bn,
            bdd_variables,
            state_variables,
            update_function_cache: function_cache,
            universe,
        };
    }

    fn extend_valuation_to_bdd(
        vars: &BddVariableSet,
        state_variables: &Vec<BddVariable>,
        valuation: &Vec<bool>,
        regulators: &Vec<VariableId>,
    ) -> Bdd {
        // valuation.len == regulators.len
        // variable_id \in state_variables.indices
        let mut bdd = vars.mk_true();
        for r_i in 0..regulators.len() {
            let r = regulators[r_i];
            let bdd_var_of_r = state_variables[r.0];
            let r_is_true = valuation[r_i];
            let r_bdd = if r_is_true {
                vars.mk_var(bdd_var_of_r)
            } else {
                vars.mk_not_var(bdd_var_of_r)
            };
            bdd = bdd.and(&r_bdd);
        }
        return bdd;
    }

    fn extend_valuation_to_id_state(
        valuation: &Vec<bool>,
        regulators: &Vec<VariableId>,
    ) -> IdState {
        let mut state = 0;
        for r_i in 0..regulators.len() {
            if valuation[r_i] {
                let r = regulators[r_i];
                state += (1 as usize).shl(r.0);
            }
        }
        return IdState::from(state);
    }

    pub fn empty_set(&self) -> ColorVertexSet {
        return ColorVertexSet {
            bdd: self.bdd_variables.mk_false(),
        }
    }

    pub fn empty_colours(&self) -> ColorSet {
        return ColorSet {
            bdd: self.bdd_variables.mk_false(),
        };
    }

    pub fn all_vertices(&self) -> ColorVertexSet {
        return ColorVertexSet {
            bdd: self.universe.clone(),
        };
    }

    pub fn color_projection(&self, set: &ColorVertexSet) -> ColorSet {
        return ColorSet {
            bdd: set.bdd.projection(self.p_count),
        };
    }

    pub fn pivots(&self, set: &ColorVertexSet) -> ColorVertexSet {
        return ColorVertexSet {
            bdd: set.bdd.extended_witness(self.p_count),
        };
    }

    pub fn colours_cardinality(&self, set: &ColorSet) -> f64 {
        return set.bdd.cardinality() / (1.shl(self.state_variables.len()) as f64);
    }

    pub fn _post_sequential(
        &self,
        frontier: &ColorVertexSet,
        universe: &ColorVertexSet,
    ) -> ColorVertexSet {
        let frontier = &frontier.bdd;
        let mut result = self.bdd_variables.mk_false();
        if LOG_LEVEL > 1 {
            print!("Post.")
        };
        for v_i in 0..self.network.graph.num_vars() {
            let v = self.state_variables[v_i];
            let apply_function = &self.update_function_cache[v_i];
            // This is equivalent to [frontier & ((v_is_one & function_is_zero) | (v_is_zero & function_is_one))]
            let can_perform_step: Bdd = bdd!(frontier & apply_function);
            let after_step_performed = can_perform_step.invert_input(v).and(&universe.bdd);
            result = bdd!(result | after_step_performed);
            if LOG_LEVEL > 2 {
                print!("{}.", v_i);
                io::stdout().flush().unwrap();
            }
        }
        if LOG_LEVEL > 1 {
            println!();
        }
        return ColorVertexSet { bdd: result };
    }

    pub fn post(&self, frontier: &ColorVertexSet, universe: &ColorVertexSet) -> ColorVertexSet {
        let frontier = &frontier.bdd;
        if LOG_LEVEL > 1 {
            print!("Post.")
        };
        let transition_post: Vec<Bdd> = (0..self.network.graph.num_vars())
            .into_par_iter()
            .map(|v_i| {
                let v = self.state_variables[v_i];
                let apply_function = &self.update_function_cache[v_i];
                // This is equivalent to [frontier & ((v_is_one & function_is_zero) | (v_is_zero & function_is_one))]
                let can_perform_step: Bdd = bdd!(frontier & apply_function);
                let after_step_performed = can_perform_step.invert_input(v).and(&universe.bdd);
                if LOG_LEVEL > 2 {
                    print!("{}.", v_i);
                    io::stdout().flush().unwrap();
                }
                after_step_performed
            })
            .collect();
        if LOG_LEVEL > 1 {
            println!();
        }
        return ColorVertexSet {
            bdd: par_union(transition_post)
            /*transition_post
                .into_iter()
                .fold(self.bdd_variables.mk_false(), |a, b| a.or(&b)),*/
        };
    }

    pub fn _pre_sequential(
        &self,
        frontier: &ColorVertexSet,
        universe: &ColorVertexSet,
    ) -> ColorVertexSet {
        let frontier = &frontier.bdd;
        let mut result = self.bdd_variables.mk_false();
        if LOG_LEVEL > 1 {
            print!("Pre.");
        }
        for v_i in 0..self.network.graph.num_vars() {
            let v = self.state_variables[v_i];
            let apply_function = &self.update_function_cache[v_i];
            let possible_predecessors = frontier.invert_input(v).and(&universe.bdd);
            let can_perform_step = bdd!(possible_predecessors & apply_function);
            result = bdd!(result | can_perform_step);
            if LOG_LEVEL > 2 {
                print!("{}.", v_i);
                io::stdout().flush().unwrap();
            }
        }
        if LOG_LEVEL > 1 {
            println!();
        }
        return ColorVertexSet { bdd: result };
    }

    pub fn pre(&self, frontier: &ColorVertexSet, universe: &ColorVertexSet) -> ColorVertexSet {
        let frontier = &frontier.bdd;
        if LOG_LEVEL > 1 {
            print!("Pre.")
        };
        let transition_post: Vec<Bdd> = (0..self.network.graph.num_vars())
            .into_par_iter()
            .map(|v_i| {
                let v = self.state_variables[v_i];
                let apply_function = &self.update_function_cache[v_i];
                let possible_predecessors = frontier.invert_input(v).and(&universe.bdd);
                let can_perform_step = bdd!(possible_predecessors & apply_function);
                if LOG_LEVEL > 2 {
                    print!("{}.", v_i);
                    io::stdout().flush().unwrap();
                }
                can_perform_step
            })
            .collect();
        if LOG_LEVEL > 1 {
            println!();
        }
        return ColorVertexSet {
            bdd: par_union(transition_post),
            /*transition_post
                .into_iter()
                .fold(self.bdd_variables.mk_false(), |a, b| a.or(&b)),*/
        };
    }

    /*pub fn has_successor(&self, universe: &ColorVertexSet) -> ColorVertexSet {
        let universe = &universe.bdd;
        let mut result = self.bdd_variables.mk_false();
        print!("Has successor.");
        for v_i in 0..self.network.graph.num_vars() {
            let v = self.state_variables[v_i];
            let cached = &self.update_function_cache[v_i];
            let can_do_transition = bdd!(universe & cached);
            let after_transition = universe.and(&can_do_transition.invert_input(v));
            let before_transition = after_transition.invert_input(v);
            result = result.or(&before_transition);
            print!("{}.", v_i);
            io::stdout().flush().unwrap();
        }
        println!();
        return ColorVertexSet { bdd: result };
    }*/

    /// Compute the vertex set of items which have no successor in the given universe.
    pub fn _sinks_sequential(&self, universe: &ColorVertexSet) -> ColorVertexSet {
        let mut sink_candidate = universe.bdd.clone();
        if LOG_LEVEL > 1 {
            print!("Sinks.");
        }
        for v_i in 0..self.network.graph.num_vars() {
            let v = self.state_variables[v_i];
            let cached = &self.update_function_cache[v_i];
            let can_do_transition = bdd!(sink_candidate & cached);
            // This has to be universe and not sink_candidate because that's where we look for successors.
            let after_transition = universe.bdd.and(&can_do_transition.invert_input(v));
            let before_transition = after_transition.invert_input(v);
            sink_candidate = sink_candidate.and_not(&before_transition);
            if LOG_LEVEL > 2 {
                print!("{}.", v_i);
                io::stdout().flush().unwrap();
            }
        }
        if LOG_LEVEL > 1 {
            println!();
        }
        return ColorVertexSet {
            bdd: sink_candidate,
        };
    }

    pub fn sinks(&self, universe: &ColorVertexSet) -> ColorVertexSet {
        let universe = &universe.bdd;
        if LOG_LEVEL > 1 {
            print!("Sinks.")
        };
        let not_sinks: Vec<Bdd> = (0..self.network.graph.num_vars())
            .into_par_iter()
            .map(|v_i| {
                let v = self.state_variables[v_i];
                let cached = &self.update_function_cache[v_i];
                let can_do_transition = bdd!(universe & cached);
                // This has to be universe and not sink_candidate because that's where we look for successors.
                let after_transition = universe.and(&can_do_transition.invert_input(v));
                let before_transition = after_transition.invert_input(v);
                if LOG_LEVEL > 2 {
                    print!("{}.", v_i);
                    io::stdout().flush().unwrap();
                }
                before_transition
            })
            .collect();
        if LOG_LEVEL > 1 {
            println!();
        }
        return ColorVertexSet {
            bdd: universe.and_not(&par_union(not_sinks))
                /*not_sinks
                .into_iter()
                .fold(universe.clone(), |a, b| a.and_not(&b)),*/
        };
    }

    /*pub fn has_predecessor(&self, universe: &ColorVertexSet) -> ColorVertexSet {
        let universe = &universe.bdd;
        let mut result = self.bdd_variables.mk_false();
        print!("Has predecessor.");
        for v_i in 0..self.network.graph.num_vars() {
            let v = self.state_variables[v_i];
            let cached = &self.update_function_cache[v_i];
            let possible_predecessors = universe.invert_input(v);
            let actual_predecessors = bdd!(possible_predecessors & cached);
            let predecessors_in_universe = universe.and(&actual_predecessors);
            let after_transition = predecessors_in_universe.invert_input(v);
            result = result.or(&after_transition);
            print!("{}.", v_i);
            io::stdout().flush().unwrap();
        }
        println!();
        return ColorVertexSet { bdd: result };
    }*/

    pub fn _sources_sequential(&self, universe: &ColorVertexSet) -> ColorVertexSet {
        let mut source_candidate = universe.bdd.clone();
        if LOG_LEVEL > 1 {
            print!("Sources.");
        }
        for v_i in 0..self.network.graph.num_vars() {
            let v = self.state_variables[v_i];
            let cached = &self.update_function_cache[v_i];
            let possible_predecessors = source_candidate.invert_input(v).and(&universe.bdd);
            let can_do_transition = bdd!(possible_predecessors & cached);
            let after_transition = can_do_transition.invert_input(v);
            source_candidate = source_candidate.and_not(&after_transition);
            if LOG_LEVEL > 2 {
                print!("{}.", v_i);
                io::stdout().flush().unwrap();
            }
        }
        if LOG_LEVEL > 1 {
            println!();
        }
        return ColorVertexSet {
            bdd: source_candidate,
        };
    }

    pub fn sources(&self, universe: &ColorVertexSet) -> ColorVertexSet {
        let universe = &universe.bdd;
        if LOG_LEVEL > 1 {
            print!("Sources.")
        };
        let not_sources: Vec<Bdd> = (0..self.network.graph.num_vars())
            .into_par_iter()
            .map(|v_i| {
                let v = self.state_variables[v_i];
                let cached = &self.update_function_cache[v_i];
                let possible_predecessors = universe.invert_input(v).and(&universe);
                let can_do_transition = bdd!(possible_predecessors & cached);
                let after_transition = can_do_transition.invert_input(v);
                if LOG_LEVEL > 2 {
                    print!("{}.", v_i);
                    io::stdout().flush().unwrap();
                }
                after_transition
            })
            .collect();
        if LOG_LEVEL > 1 {
            println!();
        }
        return ColorVertexSet {
            bdd: universe.and_not(&par_union(not_sources))
            /*not_sinks
                .into_iter()
                .fold(universe.clone(), |a, b| a.and_not(&b))*/,
        };
    }
}

fn par_union(items: Vec<Bdd>) -> Bdd {
    if items.len() == 1 { return items[0].clone(); }
    let join: Vec<Bdd> = items.into_par_iter()
        .chunks(2)
        .map(|chunk| {
            if chunk.len() == 2 {
                chunk[0].or(&chunk[1])
            } else {
                chunk[0].clone()
            }
        }).collect();
    return par_union(join);
}

fn par_intersect(items: Vec<Bdd>) -> Bdd {
    if items.len() == 1 { return items[0].clone(); }
    if LOG_LEVEL > 0 { println!("Par intersect: {:?}", items.len()); }
    let join: Vec<Bdd> = items.into_par_iter()
        .chunks(2)
        .map(|chunk| {
            if chunk.len() == 2 {
                chunk[0].and(&chunk[1])
            } else {
                chunk[0].clone()
            }
        }).collect();
    return par_intersect(join);
}


#[derive(Clone)]
pub struct ColorSet {
    bdd: Bdd,
}

impl ColorSet {
    /*
        Operations on color sets are just operations on BDDs since state variables are all erased
        and do not play any role.
    */

    pub fn union(&self, other: &Self) -> Self {
        return ColorSet {
            bdd: self.bdd.or(&other.bdd),
        };
    }

    pub fn minus(&self, other: &Self) -> Self {
        return ColorSet {
            bdd: self.bdd.and_not(&other.bdd),
        };
    }

    pub fn equals(&self, other: &Self) -> bool {
        return self.bdd.eq(&other.bdd);
    }
}

#[derive(Clone)]
pub struct ColorVertexSet {
    bdd: Bdd,
}

impl ColorVertexSet {
    pub fn is_empty(&self) -> bool {
        return self.bdd.is_false();
    }

    pub fn minus(&self, other: &ColorVertexSet) -> ColorVertexSet {
        return ColorVertexSet {
            bdd: self.bdd.and_not(&other.bdd),
        };
    }

    pub fn minus_colors(&self, other: &ColorSet) -> ColorVertexSet {
        return ColorVertexSet {
            bdd: self.bdd.and_not(&other.bdd),
        };
    }

    pub fn intersect_colors(&self, other: &ColorSet) -> ColorVertexSet {
        return ColorVertexSet {
            bdd: self.bdd.and(&other.bdd),
        };
    }

    pub fn union(&self, other: &ColorVertexSet) -> ColorVertexSet {
        return ColorVertexSet {
            bdd: self.bdd.or(&other.bdd),
        };
    }

    pub fn intersect(&self, other: &ColorVertexSet) -> ColorVertexSet {
        return ColorVertexSet {
            bdd: self.bdd.and(&other.bdd),
        };
    }

    pub fn cardinality(&self) -> f64 {
        return self.bdd.cardinality();
    }
}

pub fn trim(context: &PsccContext, universe: ColorVertexSet) -> ColorVertexSet {
    let start_cardinality = universe.cardinality();
    let mut result = universe;

    let to_trim = context.sinks(&result);
    result = result.minus(&to_trim);
    let mut test_next = context.pre(&to_trim, &result);
    while !test_next.is_empty() {
        let to_trim = context.sinks(&test_next);
        if LOG_LEVEL > 0 { println!("To trim: {}", to_trim.cardinality()); }
        result = result.minus(&to_trim);
        if TRIM_CUTOFF && to_trim.cardinality() < 0.001 * start_cardinality { break; }
        test_next = context.pre(&to_trim, &result);
    }

    let to_trim = context.sources(&result);
    result = result.minus(&to_trim);
    let mut test_next = context.post(&to_trim, &result);
    while !test_next.is_empty() {
        let to_trim = context.sources(&result);
        if LOG_LEVEL > 0 { println!("To trim: {}", to_trim.cardinality()); }
        result = result.minus(&to_trim);
        if TRIM_CUTOFF && to_trim.cardinality() < 0.001 * start_cardinality { break; }
        test_next = context.post(&to_trim, &result);
    }

    let trimmed = start_cardinality - result.bdd.cardinality();
    println!("Trimmed: {} ({}%)", trimmed, ((trimmed / start_cardinality) * 100.0) as usize);
    return result;
}

pub fn decomposition(context: &PsccContext, universe: ColorVertexSet) {
    if universe.is_empty() {
        return;
    }
    println!("Decomposition: {}", universe.cardinality());
    let universe = trim(context, universe);
    if universe.is_empty() {
        return;
    }
    let pivot = context.pivots(&universe);
    println!("Found pivot: {:?}", pivot.cardinality());
    //println!("{}", pivot.bdd.to_dot_string(&context.bdd_variables, true));

    let mut f = pivot.clone();
    let mut b = pivot.clone();
    let mut f_frontier = pivot.clone();
    let mut b_frontier = pivot.clone();
    let mut f_lock = context.empty_colours();
    let mut b_lock = context.empty_colours();

    let mut cont_f_frontier = context.empty_set();
    let mut cont_b_frontier = context.empty_set();
    let ref universe_colors = context.color_projection(&universe);
    while !f_lock.union(&b_lock).equals(universe_colors) {
        let ref new_f_frontier = context.post(&f_frontier, &universe.minus(&f));
        let ref new_b_frontier = context.pre(&b_frontier, &universe.minus(&b));
        f = f.union(new_f_frontier);
        b = b.union(new_b_frontier);
        let stopped_f_colors = context
            .color_projection(&f_frontier)
            .minus(&context.color_projection(&new_f_frontier));
        let stopped_b_colors = context
            .color_projection(&b_frontier)
            .minus(&context.color_projection(&new_b_frontier))
            .minus(&f_lock);
        f_lock = f_lock.union(&stopped_f_colors);
        b_lock = b_lock.union(&stopped_b_colors);
        f_frontier = new_f_frontier.minus_colors(&b_lock);
        b_frontier = new_b_frontier.minus_colors(&f_lock);
        cont_f_frontier = cont_f_frontier.union(&new_f_frontier.intersect_colors(&stopped_b_colors));
        cont_b_frontier = cont_b_frontier.union(&new_b_frontier.intersect_colors(&stopped_f_colors));
        if LOG_LEVEL > 0 {
            println!("Remaining: {}", context.colours_cardinality(universe_colors) - context.colours_cardinality(&f_lock.union(&b_lock)));
        }
        /*println!("Frontier (F):");
        println!("{}", new_f_frontier.bdd.to_dot_string(&context.bdd_variables, true));
        println!("{}", context.post(&new_f_frontier).bdd.to_dot_string(&context.bdd_variables, true));
        println!("Frontier (B):");
        println!("{}", new_b_frontier.bdd.to_dot_string(&context.bdd_variables, true));
        println!("Stopped f: {}, Stopped b: {}", context.colours_cardinality(&stopped_f_colors), context.colours_cardinality(&stopped_b_colors));*/
    }

    while !cont_f_frontier.intersect(&b).is_empty() {
        cont_f_frontier = context.post(&cont_f_frontier, &b.minus(&f));
        f = f.union(&cont_f_frontier);
    }

    while !cont_b_frontier.intersect(&f).is_empty() {
        cont_b_frontier = context.pre(&cont_b_frontier, &f.minus(&b));
        b = b.union(&cont_b_frontier);
    }

    let scc = f.intersect(&b);
    println!(
        "Found scc: {:?}; Non-trivial: {:?}",
        scc.cardinality(),
        scc.minus(&pivot).cardinality()
    );
    //println!("{}", scc.bdd.to_dot_string(&context.bdd_variables, true));

    let converged = f
        .intersect_colors(&f_lock)
        .union(&b.intersect_colors(&b_lock));

    rayon::join(
        || decomposition(context, universe.minus(&converged)),
        || decomposition(context, converged.minus(&scc)),
    );
}
