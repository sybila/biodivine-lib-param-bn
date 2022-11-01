/*
   See notes in `check_nfvs.rs`.
*/

use biodivine_lib_param_bn::Sign::Negative;
use biodivine_lib_param_bn::{BooleanNetwork, SdGraph};

fn main() {
    let args = std::env::args().collect::<Vec<_>>();
    let model = BooleanNetwork::try_from_file(args[1].as_str()).unwrap();

    // First, compute the feedback vertex set.
    let n_fvs = model.as_graph().parity_feedback_vertex_set(Negative);
    println!("nFVS size: {}", n_fvs.len());

    let graph = SdGraph::from(model.as_graph());
    let mut restriction = graph.mk_all_vertices();
    for x in &n_fvs {
        restriction.remove(x);
    }

    // Finally, for every variable, we check that there are indeed no negative cycles.
    for x in model.variables() {
        if restriction.contains(&x) {
            assert!(graph
                .shortest_parity_cycle(&restriction, x, Negative, usize::MAX)
                .is_none());
        }
    }
}
