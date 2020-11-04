use biodivine_lib_bdd::{BddValuation, BddValuationIterator};
use biodivine_lib_param_bn::async_graph::AsyncGraph;
use biodivine_lib_param_bn::bdd_params::BddParameterEncoder;
use biodivine_lib_param_bn::BooleanNetwork;
use biodivine_lib_std::param_graph::{EvolutionOperator, Graph};
use std::convert::TryFrom;
use std::io::Read;

/// Dump aeon model from stdin as explicit coloured graph to stdout.
/// Provides extra debug info on stderr...
fn main() {
    let mut buffer = String::new();
    std::io::stdin().read_to_string(&mut buffer).unwrap();

    let model = BooleanNetwork::try_from(buffer.as_str()).unwrap();

    let ref encoder = BddParameterEncoder::new(&model);
    let ref graph = AsyncGraph::new(model).unwrap();
    let all_colors = graph.unit_params().clone().into_bdd();

    // Compute all actually valid valuations
    eprintln!("Graph loaded...");
    eprintln!("Vertices: {}", graph.num_states());
    eprintln!("Colors: {}", all_colors.cardinality());
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
            if !p.is_false() {
                println!("{} -> {}", s, t);
                let mut first = true;
                for i in 0..valid_valuations.len() {
                    if p.eval_in(&valid_valuations[i]) {
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
