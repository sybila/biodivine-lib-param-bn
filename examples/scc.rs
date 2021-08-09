use biodivine_lib_bdd::{Bdd, BddValuation, BddVariableSet};
use biodivine_lib_param_bn::BooleanNetwork;
use std::convert::TryFrom;
use std::io::Read;

fn main() {
    todo!()
    /*let mut buffer = String::new();
    std::io::stdin().read_to_string(&mut buffer).unwrap();

    let model = BooleanNetwork::try_from(buffer.as_str()).unwrap();
    println!("Model: {}", model);
    println!("Model vars: {}", model.as_graph().num_vars());

    let symbolic = SymbolicBN::new(model).unwrap();

    let sinks = symbolic.sinks();
    println!("Sinks: {}", sinks.cardinality());

    let all = symbolic.all_states();
    let mut can_reach_sink = sinks;
    let mut frontier = symbolic.pre_all(&can_reach_sink);
    can_reach_sink = can_reach_sink.or(&frontier);
    while !frontier.is_false() {
        frontier = symbolic.pre_all(&frontier).and_not(&can_reach_sink);
        can_reach_sink = can_reach_sink.or(&frontier);
        println!(
            "Next frontier: {} Can reach sink: {} Remaining: {}",
            frontier.cardinality(),
            can_reach_sink.cardinality(),
            all.cardinality() - can_reach_sink.cardinality()
        );
    }
    /*let mut remaining = symbolic.all_states();
    while !remaining.is_false() {
        println!("Remaining: {}", remaining.cardinality());

        let pivot = valuation_to_bdd(&remaining.sat_witness().unwrap(), &symbolic.universe);

        let mut frontier = pivot;
        while !frontier.is_false() {
            remaining = remaining.and_not(&frontier);
            frontier = symbolic.post_all(&frontier).and(&remaining);
            println!("Next frontier: {} Remaining: {}", frontier.cardinality(), remaining.cardinality());
        }
    }*/

     */
}

pub fn valuation_to_bdd(val: &BddValuation, variables: &BddVariableSet) -> Bdd {
    let vars = variables.variables();
    let mut result = variables.mk_true();
    for v in vars {
        if val.value(v) {
            result = result.and(&variables.mk_var(v))
        } else {
            result = result.and(&variables.mk_not_var(v))
        }
    }
    return result;
}
