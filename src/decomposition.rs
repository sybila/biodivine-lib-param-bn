#![allow(unused)]

use crate::biodivine_std::traits::Set;
use crate::symbolic_async_graph::{GraphColoredVertices, GraphColors, SymbolicAsyncGraph};
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::Mutex;

pub fn baseline_fwd_bwd_parallel<F>(graph: &SymbolicAsyncGraph, callback: F)
where
    F: Fn(GraphColoredVertices),
{
    //let result = Mutex::new(Counter::new(graph));
    let result = AtomicU64::new(0);
    rayon::scope(|s| {
        s.spawn(|_| parallel_recursion(graph, graph.mk_unit_colored_vertices(), &result));
    });
    println!("Counted: {}", result.load(Ordering::SeqCst));
    //let result = result.lock().unwrap();
    //for scc in result.iter() {
    //    counter.push(&scc.colors());
    //}
    //let counter = result.into_inner().unwrap();
    //counter.print();
}

const CUT_OFF: f64 = 10_000.0;

fn parallel_recursion(
    graph: &SymbolicAsyncGraph,
    universe: GraphColoredVertices,
    result: &AtomicU64,
) {
    let universe = &trim(graph, universe);
    if universe.is_empty() {
        println!("NO SCC.");
        return;
    }

    let pivot = universe.pick_vertex();
    //let fwd = fwd_normal(graph, &universe,pivot.clone());
    let fwd = fwd_saturation(graph, universe, pivot.clone());
    //let bwd = bwd_normal(graph, &universe, pivot.clone());
    let bwd = bwd_saturation(graph, universe, pivot.clone());

    let scc = fwd.intersect(&bwd);

    if scc.minus(&pivot).vertices().approx_cardinality() >= CUT_OFF {
        //let push = scc.minus(&pivot).colors();
        println!(
            "SCC: {} in {}",
            scc.approx_cardinality(),
            universe.approx_cardinality()
        );
        result.fetch_add(1, Ordering::SeqCst);
        //let mut result = result.lock().unwrap();
        //result.push(&push);
    }

    rayon::scope(|s| {
        let below = fwd.minus(&scc);
        if below.vertices().approx_cardinality() > CUT_OFF {
            s.spawn(|_| parallel_recursion(graph, below, result));
        }
        let above = bwd.minus(&scc);
        if above.vertices().approx_cardinality() > CUT_OFF {
            s.spawn(|_| parallel_recursion(graph, above, result));
        }
        let rest = universe.minus(&fwd.union(&bwd));
        if rest.vertices().approx_cardinality() > CUT_OFF {
            s.spawn(|_| parallel_recursion(graph, rest, result));
        }
    });
}

pub fn baseline_fwd_bwd<F>(graph: &SymbolicAsyncGraph, callback: F)
where
    F: Fn(GraphColoredVertices),
{
    let mut counter = Counter::new(graph);
    let mut universes = vec![graph.mk_unit_colored_vertices()];

    while let Some(universe) = universes.pop() {
        //let ref universe = trim_saturating(graph, universe);
        let universe = &trim(graph, universe);
        if universe.is_empty() {
            println!("NO SCC.");
            continue;
        }

        let pivot = universe.pick_vertex();
        //let fwd = fwd_normal(graph, &universe,pivot.clone());
        let fwd = fwd_saturation(graph, universe, pivot.clone());
        //let bwd = bwd_normal(graph, &universe, pivot.clone());
        let bwd = bwd_saturation(graph, universe, pivot.clone());

        let scc = fwd.intersect(&bwd);

        println!("SCC: {}", scc.approx_cardinality());

        let below = fwd.minus(&scc);
        if !below.is_empty() {
            universes.push(below);
        }

        let above = bwd.minus(&scc);
        if !above.is_empty() {
            universes.push(above);
        }

        let rest = universe.minus(&fwd.union(&bwd));
        if !rest.is_empty() {
            universes.push(rest);
        }

        counter.push(&scc.minus(&pivot).colors());
        callback(scc);

        let remaining: f64 = universes.iter().map(|it| it.approx_cardinality()).sum();
        println!("REMAINING: {}; UNIVERSES: {}", remaining, universes.len());
    }

    counter.print();
}

fn fwd_saturation(
    graph: &SymbolicAsyncGraph,
    universe: &GraphColoredVertices,
    mut fwd: GraphColoredVertices,
) -> GraphColoredVertices {
    'fwd: loop {
        if fwd.as_bdd().size() > 100_000 {
            println!(
                "FWD: {}; {}/{}",
                fwd.as_bdd().size(),
                fwd.approx_cardinality(),
                universe.approx_cardinality()
            );
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

fn bwd_saturation(
    graph: &SymbolicAsyncGraph,
    universe: &GraphColoredVertices,
    mut bwd: GraphColoredVertices,
) -> GraphColoredVertices {
    'bwd: loop {
        if bwd.as_bdd().size() > 100_000 {
            println!(
                "BWD: {}; {}/{}",
                bwd.as_bdd().size(),
                bwd.approx_cardinality(),
                universe.approx_cardinality()
            );
        }
        for var in graph.as_network().variables().rev() {
            let predecessors = graph.var_pre(var, &bwd).intersect(universe);

            if !predecessors.is_subset(&bwd) {
                bwd = bwd.union(&predecessors);
                continue 'bwd;
            }
        }
        return bwd;
    }
}

fn fwd_normal(
    graph: &SymbolicAsyncGraph,
    universe: &GraphColoredVertices,
    mut fwd: GraphColoredVertices,
) -> GraphColoredVertices {
    loop {
        let successors = graph.post(&fwd).intersect(universe);
        println!(
            "FWD: {}; {}/{}",
            fwd.as_bdd().size(),
            fwd.approx_cardinality(),
            universe.approx_cardinality()
        );
        if successors.is_subset(&fwd) {
            // fixpoint done
            return fwd;
        }
        fwd = fwd.union(&successors);
    }
}

fn bwd_normal(
    graph: &SymbolicAsyncGraph,
    universe: &GraphColoredVertices,
    mut bwd: GraphColoredVertices,
) -> GraphColoredVertices {
    loop {
        let predecessors = graph.pre(&bwd).intersect(universe);
        println!(
            "BWD: {}; {}/{}",
            bwd.as_bdd().size(),
            bwd.approx_cardinality(),
            universe.approx_cardinality()
        );
        if predecessors.is_subset(&bwd) {
            // fixpoint done
            return bwd;
        }
        bwd = bwd.union(&predecessors);
    }
}

fn trim_outside(
    graph: &SymbolicAsyncGraph,
    mut universe: GraphColoredVertices,
) -> GraphColoredVertices {
    todo!()
}

fn trim_saturating(
    graph: &SymbolicAsyncGraph,
    mut universe: GraphColoredVertices,
) -> GraphColoredVertices {
    'trim: loop {
        for var in graph.as_network().variables().rev() {
            // All vertices in universe with var-predecessor in universe:
            let candidates = graph.var_post(var, &universe).intersect(&universe);

            let can_go_fwd = graph
                .pre(&graph.post(&candidates).intersect(&universe))
                .intersect(&universe);

            let remove = candidates.minus(&can_go_fwd);
            if !remove.is_empty() {
                println!(
                    "TRIM: {}; {}",
                    universe.as_bdd().size(),
                    universe.approx_cardinality()
                );
                universe = universe.minus(&remove);
                continue 'trim;
            }
        }
        return universe;
    }
}

fn trim(graph: &SymbolicAsyncGraph, mut universe: GraphColoredVertices) -> GraphColoredVertices {
    loop {
        let can_go_fwd = graph
            .pre(&graph.post(&universe).intersect(&universe))
            .intersect(&universe);

        let can_go_bwd = graph
            .post(&graph.pre(&universe).intersect(&universe))
            .intersect(&universe);
        let can_step = can_go_fwd.intersect(&can_go_bwd);
        if universe.as_bdd().size() > 100_000 {
            println!(
                "TRIM: {}; {}",
                universe.as_bdd().size(),
                universe.approx_cardinality()
            );
        }
        if universe.is_subset(&can_step) {
            // universe == can_step
            return can_step;
        }
        universe = can_step;
    }
}

pub struct Counter<'a> {
    graph: &'a SymbolicAsyncGraph,
    // Index is the number of components
    items: Vec<GraphColors>,
}

impl Counter<'_> {
    pub fn new(graph: &SymbolicAsyncGraph) -> Counter {
        Counter {
            graph,
            items: vec![graph.mk_unit_colors()],
        }
    }

    pub fn push_count(&mut self, colors: &GraphColors, count: usize) {
        let mut colors = colors.clone();
        for i in (0..self.items.len()).rev() {
            if self.items[i].is_empty() {
                continue;
            }
            let move_up = self.items[i].intersect(&colors);
            if !move_up.is_empty() {
                colors = colors.minus(&move_up);
                self.safe_union(i + count, &move_up);
            }
            self.items[i] = self.items[i].minus(&move_up);
            if colors.is_empty() {
                return;
            }
        }
    }

    pub fn push(&mut self, colors: &GraphColors) {
        let mut colors = colors.clone();
        for i in (0..self.items.len()).rev() {
            if self.items[i].is_empty() {
                continue;
            }
            let move_up = self.items[i].intersect(&colors);
            if !move_up.is_empty() {
                colors = colors.minus(&move_up);
                self.safe_union(i + 1, &move_up);
            }
            self.items[i] = self.items[i].minus(&move_up);
            if colors.is_empty() {
                return;
            }
        }
    }

    fn safe_union(&mut self, position: usize, colors: &GraphColors) {
        while self.items.len() <= position {
            self.items.push(self.graph.mk_empty_colors());
        }
        self.items[position] = self.items[position].union(colors);
    }

    pub fn merge(&mut self, other: &Counter) {
        for (i, set) in other.items.iter().enumerate() {
            if i != 0 && !set.is_empty() {
                //println!("PUSH!");
                self.push_count(set, i as usize);
            }
        }
    }

    pub fn print(&self) {
        println!("Classification output:");
        for i in 0..self.items.len() {
            if self.items[i].approx_cardinality() != 0.0 {
                println!("{} SCCs: {}", i, self.items[i].approx_cardinality());
            }
        }
    }

    pub fn len(&self) -> usize {
        self.items.len() - 1
    }

    pub fn is_empty(&self) -> bool {
        self.items.len() == 1
    }
}
