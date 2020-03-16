use biodivine_lib_bdd::{Bdd, BddVariableSet, BddVariable};
use crate::{BooleanNetwork, FnUpdate, BinaryOp, VariableId};
use biodivine_lib_bdd::bdd;

pub struct SymbolicBN {
    pub network: BooleanNetwork,
    pub universe: BddVariableSet,
    pub bdd_vars: Vec<BddVariable>,
    pub functions: Vec<Bdd>
}

impl SymbolicBN {

    /// Create a new symbolic network with specific update functions
    pub fn new(network: BooleanNetwork) -> Result<SymbolicBN, String> {
        // make variables with the same names as in the network (easier debugging)
        let universe = BddVariableSet::new(network.graph.variables.iter().map(|v| v.name.as_str()).collect());
        let bdd_vars = universe.variables();
        let functions: Vec<Bdd> = network.update_functions.iter().filter_map(|f| {
            f.as_ref().and_then(|f| f.to_bdd(&universe, &bdd_vars))
        }).collect();
        if functions.len() != network.graph.num_vars() {
            return Err("Not all variables have explicit update functions".to_string());
        }
        return Ok(SymbolicBN { network, universe, bdd_vars, functions });
    }

    pub fn all_states(&self) -> Bdd {
        return self.universe.mk_true();
    }

    pub fn sinks(&self) -> Bdd {
        let mut sinks: Bdd = self.universe.mk_true();
        for variable in self.network.graph().variable_ids() {
            let v = self.universe.mk_var(self.bdd_vars[variable.0]);
            let fn_bdd = &self.functions[variable.0];
            sinks = bdd!(sinks & (v <=> fn_bdd));
        }
        return sinks;
    }

    /// Compute Bdd with successors of the given states when perturbing the given variable.
    pub fn post(&self, states: &Bdd, variable: VariableId) -> Bdd {
        let not_v = self.universe.mk_not_var(self.bdd_vars[variable.0]);
        let fn_bdd = &self.functions[variable.0];
        let fn_enabled: Bdd = bdd!(states & (not_v <=> fn_bdd));
        let fn_post = fn_enabled.invert_input(self.bdd_vars[variable.0]);
        return fn_post;
    }

    /// Compute Bdd with predecessors of the given states when perturbing the given variable.
    pub fn pre(&self, states: &Bdd, variable: VariableId) -> Bdd {
        let not_v = self.universe.mk_not_var(self.bdd_vars[variable.0]);
        let fn_bdd = &self.functions[variable.0];
        let possible_pre = states.invert_input(self.bdd_vars[variable.0]);
        let fn_pre = bdd!(possible_pre & (not_v <=> fn_bdd));
        return fn_pre;
    }

    /// Compute successors for all given states in all variables.
    pub fn post_all(&self, states: &Bdd) -> Bdd {
        let mut result = self.universe.mk_false();
        for v in self.network.graph.variable_ids() {
            let v_post = self.post(states, v);
            result = result.or(&v_post);
        }
        return result;
    }

    /// Compute predecessors for all given states in all variables.
    pub fn pre_all(&self, states: &Bdd) -> Bdd {
        let mut result = self.universe.mk_false();
        for v in self.network.graph.variable_ids() {
            let v_pre = self.pre(states, v);
            result = result.or(&v_pre);
        }
        return result;
    }

}

impl FnUpdate {

    fn to_bdd(&self, universe: &BddVariableSet, bdd_vars: &Vec<BddVariable>) -> Option<Bdd> {
        return Some(match self {
            FnUpdate::Const(bool) => if *bool { universe.mk_true() } else { universe.mk_false() },
            FnUpdate::Var(id) => universe.mk_var(bdd_vars[id.0]),
            FnUpdate::Param(_, _) => return None,
            FnUpdate::Not(inner) => inner.to_bdd(universe, bdd_vars).map(|b| b.not())?,
            FnUpdate::Binary(op, l, r) => {
                let l = l.to_bdd(universe, bdd_vars)?;
                let r = r.to_bdd(universe, bdd_vars)?;
                match op {
                    BinaryOp::And => l.and(&r),
                    BinaryOp::Or => l.or(&r),
                    BinaryOp::Imp => l.imp(&r),
                    BinaryOp::Iff => l.iff(&r),
                    BinaryOp::Xor => l.xor(&r),
                }
            }
        })
    }

}

#[cfg(test)]
mod tests {
    use super::*;
    use std::convert::TryFrom;

    #[test]
    fn test_symbolic_post_small() {
        // A very simple model with one sink state and one transient loop.
        let network = BooleanNetwork::try_from("
            A -> B
            A -> A
            B -> B
            B -> A
            $A: B & !A
            $B: B & !A
        ").unwrap();
        let var_a = network.graph.find_variable("A").unwrap();
        let var_b = network.graph.find_variable("B").unwrap();
        let symbolic = SymbolicBN::new(network).unwrap();

        let a = symbolic.universe.mk_var_by_name("A");
        let b = symbolic.universe.mk_var_by_name("B");
        let oo: Bdd = bdd!((!a) & (!b));
        let oi: Bdd = bdd!((!a) & b);
        let io: Bdd = bdd!(a & (!b));
        let ii: Bdd = bdd!(a & b);

        // There are no transitions from state 00
        assert!(symbolic.post(&oo, var_a).is_false());
        assert!(symbolic.post(&oo, var_b).is_false());

        // From 10, we can only go to 00
        assert_eq!(oo, symbolic.post(&io, var_a));
        assert!(symbolic.post(&io, var_b).is_false());

        // From 11, we can go to 10 and 01
        assert_eq!(oi, symbolic.post(&ii, var_a));
        assert_eq!(io, symbolic.post(&ii, var_b));

        // From 01, we can only go to 11
        assert_eq!(ii, symbolic.post(&oi, var_a));
        assert!(symbolic.post(&oi, var_b).is_false());

        // a quick test for graph diameter:
        let mut states = oi;
        states = states.or(&symbolic.post_all(&states));
        assert!(!states.is_true());
        states = states.or(&symbolic.post_all(&states));
        assert!(!states.is_true());
        states = states.or(&symbolic.post_all(&states));
        assert!(states.is_true());

    }

    #[test]
    fn test_symbolic_pre_small() {
        // A very simple model with one sink state and one transient loop.
        let network = BooleanNetwork::try_from("
            A -> B
            A -> A
            B -> B
            B -> A
            $A: B & !A
            $B: B & !A
        ").unwrap();
        let var_a = network.graph.find_variable("A").unwrap();
        let var_b = network.graph.find_variable("B").unwrap();
        let symbolic = SymbolicBN::new(network).unwrap();

        let a = symbolic.universe.mk_var_by_name("A");
        let b = symbolic.universe.mk_var_by_name("B");
        let oo: Bdd = bdd!((!a) & (!b));
        let oi: Bdd = bdd!((!a) & b);
        let io: Bdd = bdd!(a & (!b));
        let ii: Bdd = bdd!(a & b);

        // I can get to 00 from 10
        assert_eq!(io, symbolic.pre(&oo, var_a));
        assert!(symbolic.pre(&oo, var_b).is_false());

        // To 10 I can go from 11
        assert!(symbolic.pre(&io, var_a).is_false());
        assert_eq!(ii, symbolic.pre(&io, var_b));

        // To 11 I can go from 01
        assert_eq!(oi, symbolic.pre(&ii, var_a));
        assert!(symbolic.pre(&ii, var_b).is_false());

        // To 01 I can go from 11
        assert_eq!(ii, symbolic.pre(&oi, var_a));
        assert!(symbolic.pre(&oi, var_b).is_false());

        // a quick test for graph diameter:
        let mut states = oo;
        states = states.or(&symbolic.pre_all(&states));
        assert!(!states.is_true());
        states = states.or(&symbolic.pre_all(&states));
        assert!(!states.is_true());
        states = states.or(&symbolic.pre_all(&states));
        assert!(states.is_true());

    }

}