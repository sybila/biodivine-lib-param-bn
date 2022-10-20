use crate::ExtendedBoolean::Unknown;
use biodivine_lib_param_bn::biodivine_std::traits::Set;
use biodivine_lib_param_bn::symbolic_async_graph::{GraphColoredVertices, SymbolicAsyncGraph};
use biodivine_lib_param_bn::{BinaryOp, BooleanNetwork, FnUpdate, RegulatoryGraph, VariableId};
use std::collections::HashSet;
use std::fmt::{Debug, Display, Formatter};
use std::ops::{Index, IndexMut};
use ExtendedBoolean::{One, Star, Zero};

fn main() {
    let args = std::env::args().collect::<Vec<_>>();
    let buffer = std::fs::read_to_string(&args[1]).unwrap();

    let mut model = BooleanNetwork::try_from(buffer.as_str()).unwrap();
    // Fix inputs to true.
    for var in model.variables() {
        if model.get_update_function(var).is_none() {
            println!("Fix variable {:?}", var);
            model
                .set_update_function(var, Some(FnUpdate::Const(true)))
                .unwrap();
        }
    }

    let stg = SymbolicAsyncGraph::new(model.clone()).unwrap();

    //let initial = Subspace::new_unknown(&model);
    //println!("{:?}", initial);
    //let propagated = syntactic_propagation(&model, &initial).unwrap();
    //println!("{:?}", propagated);
    //let top_scc = find_minimal_top_scc(model.as_graph(), &propagated);
    //println!("Top SCC {}/{}", top_scc.len(), propagated.count_unknown());
    //let propagated = one_step_propagation(&stg, &Subspace::new_unknown(&model)).unwrap();
    //println!("{:?}", propagated);

    let result = model.minimal_trap_spaces(); //branch_scc_search(&stg, &Subspace::new_unknown(&model));
    for trap in result {
        println!("Found trap [{}]: {:?}", trap.count_any(), trap);
    }
}

fn branch_search(stg: &SymbolicAsyncGraph, candidate: Subspace) -> bool {
    /*
       0. Propagate constant values and check for conflicts.
       1. Check if unknown variables in the candidate space are strongly connected.
       2. No: Find the smallest top component. Set all remaining unknown values to *, and
          recursively obtain minimal trap spaces in this space. Then, for each minimal trap space,
          return the unknown values to the unknown status and recursively continue the search.
       3. Yes: Pick a (~minimum FVS) variable, set it to 0,1,* and recursively test all three options.
    */

    if let Some(candidate) = syntactic_propagation(stg.as_network(), &candidate) {
        let set = build_space_set(stg, &candidate);

        let mut trap_candidates = set.clone();
        for var in stg.as_network().variables().rev() {
            trap_candidates = trap_candidates.minus(&stg.var_can_post_out(var, &trap_candidates));
        }

        if trap_candidates.is_empty() {
            return false;
        }

        println!("Test[{}] {:?}", candidate.count_unknown(), candidate);

        if let Some(unknown) = pick_decision_variable(stg, &candidate) {
            //println!("Expand {:?}", unknown);
            let mut true_candidate = candidate.clone();
            true_candidate[unknown] = One;
            let mut false_candidate = candidate.clone();
            false_candidate[unknown] = Zero;
            let mut star_candidate = candidate.clone();
            star_candidate[unknown] = Star;

            println!("{:?} = 1", unknown);
            let has_true = branch_search(stg, true_candidate);
            println!("{:?} = 0", unknown);
            let has_false = branch_search(stg, false_candidate);
            println!("{:?} = *", unknown);
            let has_star = branch_search(stg, star_candidate);

            let has_inner = has_true || has_false || has_star;
            if has_inner {
                return true;
            } else {
                if stg.is_trap(&set) {
                    println!("Found trap: {:?}", candidate);
                    return true;
                } else {
                    return false;
                }
            }
        } else {
            if stg.is_trap(&set) {
                println!("Found fixed trap: {:?}", candidate);
                return true;
            } else {
                return false;
            }
        }
    } else {
        // No trap spaces here.
        return false;
    }
}

fn is_subspace(model: &BooleanNetwork, a: &Subspace, b: &Subspace) -> bool {
    for var in model.variables() {
        match (a[var], b[var]) {
            (Unknown, _) | (_, Unknown) => panic!("Subspace is not complete."),
            (One, Star) | (Zero, Star) | (One, One) | (Zero, Zero) | (Star, Star) => {
                /* Inclusion. Do nothing. */
            }
            (Star, Zero) | (Star, One) | (Zero, One) | (One, Zero) => {
                return false;
            }
        }
    }
    true
}

fn branch_scc_search(stg: &SymbolicAsyncGraph, candidate: &Subspace) -> Vec<Subspace> {
    //println!("Test [{}]{:?}", candidate.count_unknown(), candidate);
    let mut result = Vec::new();
    let initial_unknown = candidate.count_unknown();
    if let Some(candidate) = syntactic_propagation(stg.as_network(), candidate) {
        /*if candidate.count_unknown() != initial_unknown {
            println!("Percolated to: [{}]{:?}", candidate.count_unknown(), candidate);
        }*/

        if candidate.count_unknown() == 0 {
            // If everything is known, we just test if this is a trap.
            let set = build_space_set(stg, &candidate);
            if stg.is_trap(&set) {
                //println!("It is a trap.");
                result.push(candidate);
            } else {
                //println!("Done, but not a trap.")
            }
        } else {
            /*let set = build_space_set(stg, &candidate);

            let mut trap_candidates = set.clone();

            'fwd_closed: loop {
                for var in stg.as_network().variables().rev() {
                    let can_go_out = stg.var_can_post_out(var, &trap_candidates);
                    if !can_go_out.is_empty() {
                        trap_candidates = trap_candidates.minus(&can_go_out);
                        if trap_candidates.as_bdd().size() > 1_000_000 {
                            break 'fwd_closed;
                        }
                        continue 'fwd_closed;
                    }
                }
                println!("Trap computation done: {}/{}", trap_candidates.approx_cardinality(), set.approx_cardinality());
                break;
            }

            if trap_candidates.is_empty() {
                //println!("Symbolic elimination shows no trap.");
                return result;
            }*/

            /*for var in stg.as_network().variables().rev() {
                trap_candidates = trap_candidates.minus(&stg.var_can_post_out(var, &trap_candidates));
            }

            if trap_candidates.is_empty() {
                println!("Symbolic elimination shows no trap.");
                return result;
            }*/

            let top_scc = find_minimal_top_scc(stg.as_network().as_graph(), &candidate);
            //println!("Found top scc: {}/{}.", top_scc.len(), candidate.count_unknown());
            if top_scc.len() != candidate.count_unknown() {
                // The remaining regulations are not strongly connected.
                // We can do a decomposition search.

                // First, identify the remaining "bottom" variables.
                let bottom_variables = {
                    let mut set = HashSet::new();
                    for var in stg.as_network().variables() {
                        if candidate[var] == Unknown && !top_scc.contains(&var) {
                            set.insert(var);
                        }
                    }
                    set
                };

                // Fix all of the bottom variables to a star.
                let mut top_subspace = candidate.clone();
                // Erase unknown values except for the top variables.
                for var in &bottom_variables {
                    top_subspace[*var] = Star;
                }

                // Find minimal trap spaces in this restricted setting.
                println!(
                    "Explore SCC {}/{}.",
                    top_scc.len(),
                    candidate.count_unknown()
                );
                let trap_spaces_in_top_subspace = branch_scc_search(stg, &top_subspace);
                println!("Found {} partial traps.", trap_spaces_in_top_subspace.len());

                // And for each trap space, run the search again, this time with unknowns instead
                // of stars.
                for mut trap_candidate in trap_spaces_in_top_subspace {
                    for var in &bottom_variables {
                        trap_candidate[*var] = Unknown;
                    }
                    // We don't have to check for inclusion because for each subspace we have
                    // a different partial trap "seed".
                    result.append(&mut branch_scc_search(stg, &trap_candidate));
                }
            } else {
                // If the regulatory graph is strongly connected, then we need to find a variable
                // that we want to condition on and try all three assumptions:
                let decision_variable = pick_decision_variable(stg, &candidate).unwrap(); // Unwrap is safe because we know that there is at least one unknown variable.

                //println!("Condition on {}[{:?}]", stg.as_network().get_variable_name(decision_variable), decision_variable);

                let mut true_candidate = candidate.clone();
                let mut false_candidate = candidate.clone();
                let mut star_candidate = candidate.clone();
                true_candidate[decision_variable] = One;
                false_candidate[decision_variable] = Zero;
                star_candidate[decision_variable] = Star;

                for new_trap in branch_scc_search(stg, &true_candidate) {
                    let mut is_minimal = true;
                    for existing_trap in &result {
                        if is_subspace(stg.as_network(), existing_trap, &new_trap) {
                            is_minimal = false;
                        }
                    }

                    if is_minimal {
                        result.push(new_trap);
                    }
                }

                for new_trap in branch_scc_search(stg, &false_candidate) {
                    let mut is_minimal = true;
                    for existing_trap in &result {
                        if is_subspace(stg.as_network(), existing_trap, &new_trap) {
                            is_minimal = false;
                        }
                    }

                    if is_minimal {
                        result.push(new_trap);
                    }
                }

                for new_trap in branch_scc_search(stg, &star_candidate) {
                    let mut is_minimal = true;
                    for existing_trap in &result {
                        if is_subspace(stg.as_network(), existing_trap, &new_trap) {
                            is_minimal = false;
                        }
                    }

                    if is_minimal {
                        result.push(new_trap);
                    }
                }
            }
        }
    } else {
        // Syntactic conflict found - no trap spaces are possible with these assumptions.
        //println!("Constant elimination.");
    }
    result
}

fn find_minimal_top_scc(rg: &RegulatoryGraph, candidate_space: &Subspace) -> HashSet<VariableId> {
    let mut unknown_variables = HashSet::new();
    for var in rg.variables() {
        if candidate_space[var] == Unknown {
            unknown_variables.insert(var);
        }
    }

    let mut smallest_component = unknown_variables.clone();
    let mut unprocessed = unknown_variables.clone();

    while !unprocessed.is_empty() {
        let pivot = unprocessed.iter().next().cloned().unwrap();

        // Compute forward and backward reachable sets.

        let mut fwd = HashSet::new();
        fwd.insert(pivot);
        loop {
            let mut done = true;
            for var in fwd.clone() {
                for target in rg.targets(var) {
                    if !fwd.contains(&target) && unknown_variables.contains(&target) {
                        fwd.insert(target);
                        done = false;
                    }
                }
            }
            if done {
                break;
            }
        }

        let mut bwd = HashSet::new();
        bwd.insert(pivot);
        loop {
            let mut done = true;
            for var in bwd.clone() {
                for regulator in rg.regulators(var) {
                    if !bwd.contains(&regulator) && unknown_variables.contains(&regulator) {
                        bwd.insert(regulator);
                        done = false;
                    }
                }
            }
            if done {
                break;
            }
        }

        // Remove everything forward reachable from unprocessed.

        for var in &fwd {
            unprocessed.remove(var);
        }

        // If everything in BWD is also in FWD, the result is a top component.

        let mut is_top_component = true;
        for var in &bwd {
            is_top_component = is_top_component & fwd.contains(var);
        }

        // If it is smaller than the current best one, update it.

        if is_top_component && bwd.len() < smallest_component.len() {
            smallest_component = bwd;
        }
    }

    smallest_component
}

fn pick_decision_variable(
    stg: &SymbolicAsyncGraph,
    candidate_space: &Subspace,
) -> Option<VariableId> {
    fn find_top_scc(
        rg: &RegulatoryGraph,
        candidate_space: &Subspace,
        pivot: VariableId,
    ) -> Vec<VariableId> {
        assert_eq!(candidate_space[pivot], Unknown);
        let mut bwd = HashSet::new();
        bwd.insert(pivot);
        loop {
            let mut done = true;
            for var in bwd.clone() {
                for regulator in rg.regulators(var) {
                    if candidate_space[regulator] == Unknown {
                        if bwd.insert(regulator) {
                            done = false;
                        }
                    }
                }
            }
            if done {
                break;
            }
        }
        let mut fwd = HashSet::new();
        fwd.insert(pivot);
        loop {
            let mut done = true;
            for var in fwd.clone() {
                for target in rg.targets(var) {
                    if candidate_space[target] == Unknown {
                        if fwd.insert(target) {
                            done = false;
                        }
                    }
                }
            }
            if done {
                break;
            }
        }

        //let (fwd, bwd) = (bwd, fwd);

        for var in &bwd {
            if !fwd.contains(var) {
                // The component is not initial, because there is a variable that
                // is backwards reachable but not forwards. Restart from this variable.
                return find_top_scc(rg, candidate_space, *var);
            }
        }

        // Otherwise, everything that is backward reachable is also forward reachable and
        // we know the whole `bwd` is a top SCC.
        //println!("Non-top variables: {}/{}", candidate_space.count_unknown() - bwd.len(), candidate_space.count_unknown());
        bwd.into_iter().collect()
    }

    // First, find one of the initial SCCs of the remaining regulatory graph.
    let scc = if let Some(pivot) = candidate_space.first_unknown() {
        find_top_scc(stg.as_network().as_graph(), candidate_space, pivot)
    } else {
        return None;
    };

    //println!(" > Found a top SCC of size {}.", scc.len());

    if scc.len() == 1 {
        return scc.into_iter().next();
    }

    // Now, search for the shortest cycle(s) in that SCC and pick as the decision candidate
    // the variable with the highest out-degree.

    let rg = stg.as_network().as_graph();
    let mut min_cycle_lengths: Vec<(VariableId, usize, usize)> = Vec::new();
    'search: for var in &scc {
        assert_eq!(candidate_space[*var], Unknown);
        // Run BFS starting in `var` to detect the shortest cycle. We run the BFS backwards
        // because the results are equivalent but `RegulatoryGraph` is better at computing
        // predecessors than successors.
        let mut visited = HashSet::new();
        visited.insert(*var);
        let mut last_level = HashSet::new();
        last_level.insert(*var);
        let mut length = 0usize;
        loop {
            let mut new_level = HashSet::new();
            for x in last_level {
                for regulator in rg.regulators(x) {
                    if regulator == *var {
                        let out_degree = rg
                            .targets(*var)
                            .into_iter()
                            .filter(|it| candidate_space[*it] == Unknown)
                            .count();
                        min_cycle_lengths.push((*var, length + 1, out_degree));
                        continue 'search;
                    }
                    if candidate_space[regulator] == Unknown && !visited.contains(&regulator) {
                        visited.insert(regulator);
                        new_level.insert(regulator);
                    }
                }
            }
            // An empty search would mean this is not a non-trivial SCC.
            assert!(!new_level.is_empty());
            last_level = new_level;
            length += 1;
        }
    }

    // Take out the first element.
    let mut best: (VariableId, usize, usize) = min_cycle_lengths.iter().next().unwrap().clone();
    // And search for the best pick.
    for var in &min_cycle_lengths {
        if var.1 < best.1 || (var.1 == best.1 && var.2 > best.2) {
            best = var.clone();
        }
    }

    //println!(" > With {:?}/{} having a cycle of length {} and out-degree {}.", best.0, stg.as_network().get_variable_name(best.0), best.1, best.2);

    Some(best.0)
}

/// Represents a value of a variable in a partially known trap space. The difference between
/// `Star` and `Unknown` is that an `Unknown` value may be fixed later, but `Star` is required
/// to stay free.
#[derive(Copy, Clone, Eq, PartialEq, Hash)]
enum ExtendedBoolean {
    One,
    Zero,
    Star,
    Unknown,
}

impl Debug for ExtendedBoolean {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self)
    }
}

impl Display for ExtendedBoolean {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            One => write!(f, "1"),
            Zero => write!(f, "0"),
            Star => write!(f, "*"),
            Unknown => write!(f, "?"),
        }
    }
}

#[derive(Clone, Debug)]
struct Subspace(Vec<ExtendedBoolean>);

impl Index<VariableId> for Subspace {
    type Output = ExtendedBoolean;

    fn index(&self, index: VariableId) -> &Self::Output {
        &self.0[index.to_index()]
    }
}

impl IndexMut<VariableId> for Subspace {
    fn index_mut(&mut self, index: VariableId) -> &mut Self::Output {
        &mut self.0[index.to_index()]
    }
}

impl Subspace {
    pub fn new_unknown(bn: &BooleanNetwork) -> Subspace {
        Subspace(vec![Unknown; bn.num_vars()])
    }

    pub fn count_unknown(&self) -> usize {
        self.0.iter().filter(|it| **it == Unknown).count()
    }

    pub fn count_star(&self) -> usize {
        self.0.iter().filter(|it| **it == Star).count()
    }

    pub fn first_unknown(&self) -> Option<VariableId> {
        for i in 0..self.0.len() {
            if self.0[i] == Unknown {
                return Some(VariableId::from_index(i));
            }
        }
        None
    }
}

/// Partially evaluate the given update function in the given subspace.
///
/// The evaluation is defined such that the result is constant or star when guaranteed, and unknown
/// if an unknown value was involved in the decision making (i.e. unknown has higher "priority"
/// than star).
fn eval_fn_update(update: &FnUpdate, subspace: &Subspace) -> ExtendedBoolean {
    match update {
        FnUpdate::Const(bool) => {
            if *bool {
                One
            } else {
                Zero
            }
        }
        FnUpdate::Var(var) => subspace[*var],
        FnUpdate::Param(_, _) => {
            panic!("Parameters not supported.")
        }
        FnUpdate::Not(inner) => {
            let inner = eval_fn_update(inner, subspace);
            match inner {
                One => Zero,
                Zero => One,
                Star => Star,
                Unknown => Unknown,
            }
        }
        FnUpdate::Binary(op, left, right) => {
            let left = eval_fn_update(left, subspace);
            let right = eval_fn_update(right, subspace);
            match op {
                BinaryOp::And => {
                    match (left, right) {
                        // (0,0), (0,1), (0,*), (0,?) is 0.
                        (Zero, _) => Zero,
                        // (1,0), (*,0), (?,0) is 0.
                        (_, Zero) => Zero,
                        // (1,1) is 1.
                        (One, One) => One,
                        // (?,1), (?,*), (?,?) is ?
                        (Unknown, _) => Unknown,
                        // (1,?), (*,?) is ?
                        (_, Unknown) => Unknown,
                        // (*,1), (*,*) is *
                        (Star, _) => Star,
                        // (1,*) is *
                        (_, Star) => Star,
                    }
                }
                BinaryOp::Or => {
                    match (left, right) {
                        // (1,0), (1,1), (1,*), (1,?) is 1.
                        (One, _) => One,
                        // (0,1), (*,1), (?,1) is 1.
                        (_, One) => One,
                        // (0,0) is 0.
                        (Zero, Zero) => Zero,
                        // (?,0), (?,*), (?,?) is ?
                        (Unknown, _) => Unknown,
                        // (0,?), (*,?) is ?
                        (_, Unknown) => Unknown,
                        // (*,0), (*,*) is *
                        (Star, _) => Star,
                        // (0,*) is *
                        (_, Star) => Star,
                    }
                }
                _ => {
                    panic!("Other operators unsupported for now.")
                }
            }
        }
    }
}

/// Performs propagation of values based on abstract evaluation of the function expressions. Only
/// modifies the `Unknown` values within the given `space`.
///
/// The operation guarantees that any minimal trap space that is a concretization of the given
/// seed `space` is also preserved in the result. Returns `None` when the resulting space is empty,
/// i.e. there is no minimal trap that is a concretization of the given `space`.
fn syntactic_propagation(network: &BooleanNetwork, space: &Subspace) -> Option<Subspace> {
    let mut result = space.clone();
    'propagation: loop {
        for var in network.variables() {
            // Compute abstract evaluation of the update function. If the result is not unknown,
            // try to "improve" the subspace approximation, taking conflicts into account.
            let update = network.get_update_function(var).as_ref().unwrap();
            let value = eval_fn_update(update, &result);
            match (result[var], value) {
                // Unknown result cannot improve anything.
                (_, Unknown) => {}
                // Any unknown value can be improved.
                (Unknown, _) => {
                    result[var] = value;
                    continue 'propagation;
                }
                // If a fixed star can be improved to `One` or `Zero`, it means this space
                // may contain some minimal trap, but it cannot be created as a concretisation
                // of the given seed space.
                (Star, One) | (Star, Zero) => {} //return None,
                // A result that is already known.
                (One, One) | (Zero, Zero) | (Star, Star) => {}
                // A conflicting constant result.
                // The result is empty because all states can jump outside.
                (One, Zero) | (Zero, One) => return None,
                // A fixed value that evaluates to star. This only means the space itself is not
                // a trap, but otherwise may contain traps.
                (One, Star) | (Zero, Star) => {}
            }
        }

        return Some(result);
    }
}

/// Performs propagation of values based on actual states that are reachable in one step
/// from individual partial subspaces.
///
/// Note that this can be more effective than simple syntactic propagation because different
/// states in a subspace can be able to leave the space using different transitions which
/// would not be captured simply by syntactic propagation.
fn one_step_propagation(stg: &SymbolicAsyncGraph, space: &Subspace) -> Option<Subspace> {
    let mut result = space.clone();
    'propagation: loop {
        let mut space_set = build_space_set(stg, &result);
        if stg.is_trap(&space_set) {
            println!(">>>>> TRAP <<<<<<")
        }

        // First, remove all states that can go outside in one step. These cannot belong
        // to any trap space within the `result`.
        let trap_candidates = {
            let mut set = space_set.clone();
            for var in stg.as_network().variables().rev() {
                set = set.minus(&stg.var_can_post_out(var, &set));
            }
            set
        };

        println!(
            "Iteration ({}):",
            build_space_set(stg, &result).approx_cardinality()
        );
        println!("{:?}", result);
        println!("Trap candidates: {}", trap_candidates.approx_cardinality());

        // Every state in this space can leave in one step, so no minimal trap spaces are present.
        if trap_candidates.is_empty() {
            return None;
        }

        for var in stg.as_network().variables().rev() {
            if result[var] == One || result[var] == Zero {
                // We cannot further specify the value of this variable. Here, only the general
                // condition that `trap_candidates` mustn't be empty applies.
                continue;
            }

            if result[var] == Star {
                // If one of the sub-spaces is empty, there may be a minimal trap in this space,
                // but it cannot be a concretization of the initial space, because it swaps
                // a star for a one/zero.
                let true_trap = trap_candidates.fix_network_variable(var, true);
                let false_trap = trap_candidates.fix_network_variable(var, false);
                if true_trap.is_empty() || false_trap.is_empty() {
                    return None;
                }

                // Also note that if one of the spaces cannot jump into the other, there is
                // also no minimal trap space with a star, as a smaller space with a fixed
                // value would always be smaller.
                let true_jump = stg.var_can_post_out(var, &true_trap);
                let false_jump = stg.var_can_post_out(var, &false_trap);
                if true_jump.is_empty() || false_jump.is_empty() {
                    return None;
                }
            }

            if result[var] == Unknown {
                // Finally, if the result is completely unknown, we can try to fix it to any
                // of the three specific values.
                //
                // There are several ways we can try to achieve this, with varying degrees
                // of complexity.

                let mut true_trap = trap_candidates.fix_network_variable(var, true);
                let mut false_trap = trap_candidates.fix_network_variable(var, false);

                /*true_trap = true_trap.minus(&stg.var_can_post_out(var, &true_trap));
                false_trap = false_trap.minus(&stg.var_can_post_out(var, &false_trap));

                println!("in: {} / {}", true_trap.approx_cardinality(), false_trap.approx_cardinality());

                for var in stg.as_network().variables() {
                    true_trap = true_trap.minus(&stg.var_can_post_out(var, &true_trap));
                    false_trap = false_trap.minus(&stg.var_can_post_out(var, &false_trap));
                }

                println!("out: {} / {}", true_trap.approx_cardinality(), false_trap.approx_cardinality());

                /*if true_trap.is_empty() && false_trap.is_empty() {
                    // By fixing the variable to either value, we get a non-trap subspace. The only
                    // possible way this can be achieved is by having a star for this variable.
                    println!("Var {:?} is a `*`.", var);
                    result[var] = Star;
                    continue 'propagation;
                }*/

                if true_trap.is_empty() && !false_trap.is_empty() {
                    println!("Var {:?} is a `0`.", var);
                    result[var] = Zero;
                    continue 'propagation;
                }

                if !true_trap.is_empty() && false_trap.is_empty() {
                    println!("Var {:?} is a `1`.", var);
                    result[var] = One;
                    continue 'propagation;
                }

                // Else: the value stays unknown, there simply isn't that much to tell.
                 */
            }
        }
    }
}

fn build_space_set(stg: &SymbolicAsyncGraph, space: &Subspace) -> GraphColoredVertices {
    let mut constant_values = Vec::new();
    for var in stg.as_network().variables() {
        if space[var] == One {
            constant_values.push((var, true));
        }
        if space[var] == Zero {
            constant_values.push((var, false));
        }
    }
    stg.mk_subspace(&constant_values)
}
