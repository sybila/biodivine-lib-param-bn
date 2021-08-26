use biodivine_lib_param_bn::biodivine_std::traits::Set;
use biodivine_lib_param_bn::symbolic_async_graph::{GraphColoredVertices, SymbolicAsyncGraph};
use biodivine_lib_param_bn::BooleanNetwork;
use std::convert::TryFrom;

fn main() {
    let mut args = std::env::args();
    args.next();
    let input_file = args.next().unwrap();
    let model = std::fs::read_to_string(input_file).unwrap();

    let model = BooleanNetwork::try_from(model.as_str()).unwrap();
    for v in model.variables() {
        println!("{:?} is {}", v, model.get_variable_name(v));
    }

    let graph = SymbolicAsyncGraph::new(model).unwrap();
    fwd_saturation(
        &graph,
        graph.unit_colored_vertices(),
        graph.unit_colored_vertices().pick_vertex(),
    );

    let ids = graph.as_network().variables().collect::<Vec<_>>();
    let mut fwd = graph.unit_colored_vertices().pick_vertex();
    loop {
        let mut can_post = graph
            .as_network()
            .variables()
            .filter(|v| graph.as_network().targets(*v).len() != 0)
            .map(|v| {
                (
                    v,
                    graph.as_network().get_variable_name(v),
                    graph.var_post(v, &fwd).minus(&fwd).approx_cardinality(),
                )
            })
            .filter(|(_, _, x)| *x != 0.0)
            .collect::<Vec<_>>();
        can_post.sort_by(|(_, _, x), (_, _, y)| x.partial_cmp(y).unwrap());

        println!("FWD: {}; {}", fwd.as_bdd().size(), fwd.approx_cardinality());
        /*println!("Can post: {:?}", can_post);
        let mut line = String::new();
        std::io::stdin().read_line(&mut line).unwrap();
        if let Ok(id) = line.trim().parse::<usize>() {
            fwd = fwd.union(&graph.var_post(ids[id], &fwd));
        }*/
        let (var, _, _) = can_post.pop().unwrap();
        fwd = fwd.union(&graph.var_post(var, &fwd));
    }
}

fn fwd_saturation(
    graph: &SymbolicAsyncGraph,
    universe: &GraphColoredVertices,
    mut fwd: GraphColoredVertices,
) -> GraphColoredVertices {
    'fwd: loop {
        //if fwd.as_bdd().size() > 100_000 {
        println!(
            "FWD: {}; {}/{}",
            fwd.as_bdd().size(),
            fwd.approx_cardinality(),
            universe.approx_cardinality()
        );
        //}
        if fwd.as_bdd().size() > 100_000 {
            return fwd;
        }
        for var in graph.as_network().variables().rev() {
            let successors = graph.var_post(var, &fwd).intersect(universe);

            if !successors.is_subset(&fwd) {
                fwd = fwd.union(&successors);
                continue 'fwd;
            }
        }
        return fwd;
    }
}
