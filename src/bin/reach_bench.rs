use biodivine_lib_param_bn::biodivine_std::traits::Set;
use biodivine_lib_param_bn::symbolic_async_graph::SymbolicAsyncGraph;
use biodivine_lib_param_bn::BooleanNetwork;
use std::convert::TryFrom;

// A very basic benchmark for testing the performance of reachability procedures.

fn main() {
    let args = std::env::args().collect::<Vec<_>>();
    let buffer = std::fs::read_to_string(&args[1]).unwrap();

    let model = BooleanNetwork::try_from_bnet(buffer.as_str()).unwrap();
    let stg = SymbolicAsyncGraph::new(model.clone()).unwrap();

    let mut universe = stg.mk_unit_colored_vertices();
    while !universe.is_empty() {
        let mut set = universe.pick_vertex();
        // Reach back
        'bwd: loop {
            //if set.symbolic_size() > 1_000 {
            println!(
                "BWD progress: {} {}",
                set.symbolic_size(),
                set.approx_cardinality()
            );
            //}
            for var in model.variables().rev() {
                //let step = stg.var_pre(var, &set).minus(&set);
                let step = stg.var_pre_out(var, &set);
                if !step.is_empty() {
                    set = set.union(&step);
                    continue 'bwd;
                }
            }
            break 'bwd;
        }
        // Reach front
        'fwd: loop {
            //if set.symbolic_size() > 1_000 {
            println!(
                "FWD progress: {} {}",
                set.symbolic_size(),
                set.approx_cardinality()
            );
            //}
            for var in model.variables().rev() {
                //let step = stg.var_post(var, &set).minus(&set);
                let step = stg.var_post_out(var, &set);
                if !step.is_empty() {
                    set = set.union(&step);
                    continue 'fwd;
                }
            }
            break 'fwd;
        }
        universe = universe.minus(&set);
        println!("Remaining: {}", universe.approx_cardinality());
    }
}
