use crate::biodivine_std::traits::Set;
use crate::symbolic_async_graph::{GraphColoredVertices, SymbolicAsyncGraph};

pub fn stepped_coloured_scc<F>(graph: &SymbolicAsyncGraph, callback: F)
where
    F: Fn(GraphColoredVertices) -> (),
{
    fn fwd_step(
        graph: &SymbolicAsyncGraph,
        set: &GraphColoredVertices,
        universe: &GraphColoredVertices,
    ) -> GraphColoredVertices {
        for var in graph.as_network().variables().rev() {
            let stepped = graph.var_post(var, set).minus(set).intersect(universe);

            if !stepped.is_empty() {
                return stepped;
            }
        }
        graph.mk_empty_vertices()
        /*let mut result = graph.mk_empty_vertices();
        for var in graph.as_network().variables().rev() {
            let stepped = graph
                .var_post(var, &set.minus_colors(&result.colors()))
                .minus(set)
                .intersect(universe);

            result = result.union(&stepped);
            //if !stepped.is_empty() {
            //    return stepped;
            //}
        }
        result*/
        //return graph.mk_empty_vertices();
        //graph.post(set)
    }

    fn bwd_step(
        graph: &SymbolicAsyncGraph,
        set: &GraphColoredVertices,
        universe: &GraphColoredVertices,
    ) -> GraphColoredVertices {
        for var in graph.as_network().variables().rev() {
            let stepped = graph.var_pre(var, set).minus(set).intersect(universe);

            if !stepped.is_empty() {
                return stepped;
            }
        }
        graph.mk_empty_vertices()
        /*let mut result = graph.mk_empty_vertices();
        for var in graph.as_network().variables().rev() {
            let stepped = graph
                .var_pre(var, &set.minus_colors(&result.colors()))
                .minus(set)
                .intersect(universe);

            result = result.union(&stepped);
            //if !stepped.is_empty() {
            //    return stepped;
            //}
        }
        result*/
        //return graph.mk_empty_vertices();
        //graph.pre(set)
    }

    let mut universe = graph.mk_unit_colored_vertices();

    while !universe.is_empty() {
        println!(
            "Remaining universe: {} ({} states)",
            universe.approx_cardinality(),
            universe.vertices().approx_cardinality()
        );
        let pivot = universe.pick_vertex();
        println!("Picked pivot: {}", pivot.colors().approx_cardinality());

        let mut fwd = pivot.clone();
        let mut bwd = pivot.clone();

        let mut locked_colors = graph.mk_empty_colors();
        loop {
            for _ in 0..graph.as_network().num_vars() {
                let fwd_stepped = fwd_step(graph, &fwd.minus_colors(&locked_colors), &universe);
                let bwd_stepped = bwd_step(graph, &bwd.minus_colors(&locked_colors), &universe);

                fwd = fwd.union(&fwd_stepped);
                bwd = bwd.union(&bwd_stepped);
            }

            //let locked_fwd = fwd.colors().minus( &graph.can_post(&fwd).colors());//&fwd_stepped.colors());
            //let locked_bwd = bwd.colors().minus(&graph.can_pre(&bwd).colors());//&bwd_stepped.colors());

            let mut locked_fwd = graph.mk_unit_colors();
            for var in graph.as_network().variables().rev() {
                let stepped = graph.var_post(var, &fwd).minus(&fwd).intersect(&universe);
                locked_fwd = locked_fwd.minus(&stepped.colors());
            }

            let mut locked_bwd = graph.mk_unit_colors();
            for var in graph.as_network().variables().rev() {
                let stepped = graph.var_pre(var, &bwd).minus(&bwd).intersect(&universe);
                locked_bwd = locked_bwd.minus(&stepped.colors());
            }

            locked_colors = locked_fwd.union(&locked_bwd); //locked_colors.union(&locked_fwd).union(&locked_bwd);

            let remaining =
                graph.unit_colors().approx_cardinality() - locked_colors.approx_cardinality();
            println!(
                "Remaining: {}, Node count: {} {}",
                remaining,
                fwd.as_bdd().size(),
                bwd.as_bdd().size()
            );

            if pivot.colors().minus(&locked_colors).is_empty() {
                break;
            }
        }

        let mut locked_fwd = graph.mk_unit_colors();
        for var in graph.as_network().variables().rev() {
            let stepped = graph.var_post(var, &fwd).minus(&fwd).intersect(&universe);
            locked_fwd = locked_fwd.minus(&stepped.colors());
        }

        let mut locked_bwd = graph.mk_unit_colors();
        for var in graph.as_network().variables().rev() {
            let stepped = graph.var_pre(var, &bwd).minus(&bwd).intersect(&universe);
            locked_bwd = locked_bwd.minus(&stepped.colors());
        }

        loop {
            let fwd_stepped = fwd_step(graph, &fwd.minus_colors(&locked_fwd), &bwd);
            if !fwd_stepped.is_empty() {
                fwd = fwd.union(&fwd_stepped);
                println!("FWD count: {}", fwd.as_bdd().size());
            } else {
                break;
            }
        }

        loop {
            let bwd_stepped = bwd_step(graph, &bwd.minus_colors(&locked_bwd), &fwd);
            if !bwd_stepped.is_empty() {
                bwd = bwd.union(&bwd_stepped);
                println!("BWD count: {}", bwd.as_bdd().size());
            } else {
                break;
            }
        }

        let scc = fwd.intersect(&bwd);
        universe = universe.minus(&scc);
        callback(scc);
    }
}

pub fn coloured_scc<F>(graph: &SymbolicAsyncGraph, callback: F)
where
    F: Fn(GraphColoredVertices) -> (),
{
    let mut universe = graph.mk_unit_colored_vertices();

    while !universe.is_empty() {
        let pivot = universe.pick_vertex();
        println!("Picked pivot: {}", pivot.approx_cardinality());

        let mut fwd = pivot.clone();
        let mut bwd = pivot.clone();
        let mut fwd_frontier = pivot.clone();
        let mut bwd_frontier = pivot.clone();
        let mut fwd_lock = graph.mk_empty_colors();
        let mut bwd_lock = graph.mk_empty_colors();

        let mut continue_fwd_frontier = graph.mk_empty_vertices();
        let mut continue_bwd_frontier = graph.mk_empty_vertices();
        let all_colors = universe.colors();
        while !all_colors.minus(&fwd_lock.union(&bwd_lock)).is_empty() {
            let new_fwd_frontier = graph.post(&fwd_frontier).intersect(&universe).minus(&fwd);
            let new_bwd_frontier = graph.pre(&bwd_frontier).intersect(&universe).minus(&bwd);
            fwd = fwd.union(&new_fwd_frontier);
            bwd = bwd.union(&new_bwd_frontier);
            let stopped_fwd_colors = fwd_frontier.colors().minus(&new_fwd_frontier.colors());
            let stopped_bwd_colors = bwd_frontier.colors().minus(&new_bwd_frontier.colors());

            fwd_lock = fwd_lock.union(&stopped_fwd_colors);
            bwd_lock = bwd_lock.union(&stopped_bwd_colors);

            fwd_frontier = new_fwd_frontier.minus_colors(&bwd_lock);
            bwd_frontier = new_bwd_frontier.minus_colors(&fwd_lock);

            continue_fwd_frontier = continue_fwd_frontier
                .union(&new_fwd_frontier.intersect_colors(&stopped_bwd_colors));
            continue_bwd_frontier = continue_bwd_frontier
                .union(&new_bwd_frontier.intersect_colors(&stopped_fwd_colors));

            let remaining =
                all_colors.approx_cardinality() - fwd_lock.union(&bwd_lock).approx_cardinality();
            println!(
                "Remaining: {}, Node count: {} {}",
                remaining,
                fwd.as_bdd().size(),
                bwd.as_bdd().size()
            );
        }

        while !continue_fwd_frontier.intersect(&bwd).is_empty() {
            continue_fwd_frontier = graph
                .post(&continue_fwd_frontier)
                .intersect(&bwd)
                .minus(&fwd);
            fwd = fwd.union(&continue_fwd_frontier);
            println!("FWD Node count: {}", fwd.as_bdd().size());
        }

        while !continue_bwd_frontier.intersect(&fwd).is_empty() {
            continue_bwd_frontier = graph
                .pre(&continue_bwd_frontier)
                .intersect(&fwd)
                .minus(&bwd);
            bwd = bwd.union(&continue_bwd_frontier);
            println!("BWD Node count: {}", bwd.as_bdd().size());
        }

        let scc = fwd.intersect(&bwd);
        universe = universe.minus(&scc);
        callback(scc);

        //let converged = fwd
        //    .intersect_colors(&fwd_lock)
        //    .union(&bwd.intersect_colors(&bwd_lock));
    }

    /*

    let converged = f
        .intersect_colors(&f_lock)
        .union(&b.intersect_colors(&b_lock));

    iterations.fetch_add(1, Ordering::SeqCst);

    rayon::join(
        || decomposition(context, universe.minus(&converged), iterations),
        || decomposition(context, converged.minus(&scc), iterations),
    );

     */
}
