/*
   This is a very simple binary intended as an integration test for the fixed point
   detection algorithms. We can run this on the BBM dataset to see if the algorithms produces
   the expected results. It is not included in normal tests because it needs to be compiled
   with optimizations and generally we don't really want to run it every time we test.

   It also prints basic performance metrics su that we see how the algorithms compare to
   each other. However, since it always runs all algorithms, it is only applicable to models
   where all algorithms terminate in a reasonable amount of time (also it relies on the naive
   symbolic algorithm for correctness).
*/

use biodivine_lib_param_bn::biodivine_std::traits::Set;
use biodivine_lib_param_bn::fixed_points::FixedPoints;
use biodivine_lib_param_bn::symbolic_async_graph::SymbolicAsyncGraph;
use biodivine_lib_param_bn::BooleanNetwork;
use std::time::SystemTime;

fn main() {
    let args = std::env::args().collect::<Vec<_>>();

    let model = BooleanNetwork::try_from_file(args[1].as_str()).unwrap();
    let model = model.inline_inputs(true, true);
    println!(
        "Loaded model with {} variables and {} parameters/inputs.",
        model.num_vars(),
        model.num_parameters()
    );
    let stg = SymbolicAsyncGraph::new(model).unwrap();

    let start = SystemTime::now();
    println!("Search for fixed-point colors...");
    let colors = FixedPoints::symbolic_colors(&stg, stg.unit_colored_vertices());
    println!(
        "Finished `colors` in {}ms.",
        start.elapsed().unwrap().as_millis()
    );
    println!(
        "{}/{} colors have fixed-points.",
        colors.approx_cardinality(),
        stg.unit_colors().approx_cardinality()
    );

    let start = SystemTime::now();
    println!("Search for fixed-point vertices...");
    let vertices = FixedPoints::symbolic_vertices(&stg, stg.unit_colored_vertices());
    println!(
        "Finished `vertices` in {}ms.",
        start.elapsed().unwrap().as_millis()
    );
    println!(
        "{}/{} vertices have fixed-points.",
        vertices.approx_cardinality(),
        stg.unit_colored_vertices().vertices().approx_cardinality()
    );

    let start = SystemTime::now();
    println!("Search for fixed-points (symbolic)...");
    let symbolic = FixedPoints::symbolic(&stg, stg.unit_colored_vertices());
    println!(
        "Finished `symbolic` in {}ms.",
        start.elapsed().unwrap().as_millis()
    );

    let symbolic_vertices = symbolic.vertices();
    let symbolic_colors = symbolic.colors();

    println!(
        "Found {} fixed-point combinations, consisting of {} vertices and {} colors.",
        symbolic.approx_cardinality(),
        symbolic_vertices.approx_cardinality(),
        symbolic_colors.approx_cardinality(),
    );

    // Projections of the full result must be the same as the results of the projected algorithms.
    assert!(vertices.is_subset(&symbolic_vertices));
    assert!(symbolic_vertices.is_subset(&vertices));

    assert!(colors.is_subset(&symbolic_colors));
    assert!(symbolic_colors.is_subset(&colors));

    let start = SystemTime::now();
    println!("Search for fixed-points (naive)...");
    let naive = FixedPoints::naive_symbolic(&stg, stg.unit_colored_vertices());
    println!(
        "Finished `naive` in {}ms.",
        start.elapsed().unwrap().as_millis()
    );
    println!(
        "Found {} fixed-point combinations.",
        naive.approx_cardinality()
    );

    // Symbolic and naive must be the same.
    assert!(symbolic.is_subset(&naive));
    assert!(naive.is_subset(&symbolic));

    println!("All checks have passed.");
}
