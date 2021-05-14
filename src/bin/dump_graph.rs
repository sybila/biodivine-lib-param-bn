use biodivine_lib_bdd::{BddValuation, BddValuationIterator};
use biodivine_lib_param_bn::async_graph::AsyncGraph;
use biodivine_lib_param_bn::bdd_params::BddParameterEncoder;
use biodivine_lib_param_bn::biodivine_std::traits::{EvolutionOperator, Graph};
use biodivine_lib_param_bn::BooleanNetwork;
use std::convert::TryFrom;
use std::io::Read;

/// Dump aeon model from stdin as explicit coloured graph to stdout.
/// Provides extra debug info on stderr...
fn main() {
    let mut buffer = String::new();
    std::io::stdin().read_to_string(&mut buffer).unwrap();

    let model = BooleanNetwork::try_from(buffer.as_str()).unwrap();

    let encoder = &BddParameterEncoder::new(&model);
    let graph = &AsyncGraph::new(model).unwrap();
    let all_colors = graph.unit_params().clone().into_bdd();

    // Compute all actually valid valuations
    eprintln!("Graph loaded...");
    println!("Vertices: {}", graph.num_states());
    println!("Colors: {}", all_colors.cardinality());
    let p_num_vars = encoder.bdd_variables.num_vars();
    let valid_valuations: Vec<BddValuation> = BddValuationIterator::new(p_num_vars)
        .filter(|v| all_colors.eval_in(v))
        .collect();

    let fwd = graph.fwd();
    for s in graph.states() {
        for (t, p) in fwd.step(s) {
            let s: usize = s.into();
            let t: usize = t.into();
            let p = p.into_bdd();
            if !(p.and(&all_colors)).is_false() {
                println!("{} -> {}", s, t);
                let mut first = true;
                for (i, valuation) in valid_valuations.iter().enumerate() {
                    if p.eval_in(valuation) {
                        if !first {
                            print!("|");
                        }
                        print!("{}", i);
                        first = false;
                    }
                }
                println!();
            }
        }
    }
}
