use std::{os, usize};

use biodivine_lib_bdd::{Bdd, BddVariableSet};
use biodivine_lib_param_bn::biodivine_std::traits::Set;
use biodivine_lib_param_bn::BooleanNetwork;
use biodivine_lib_param_bn::symbolic_async_graph::SymbolicAsyncGraph;
use num_bigint::BigInt;

#[derive(Clone)]
enum ApproxResult {
    Exact(Bdd),
    OverUnder(Bdd, Bdd),
}

impl ApproxResult {
    pub fn is_exact(&self) -> bool {
        match self {
            ApproxResult::Exact(_) => true,
            ApproxResult::OverUnder(over, under) => over == under
        }
    }

    pub fn size(&self) -> (usize, usize) {
        match self {
            ApproxResult::Exact(bdd) => (bdd.size(), bdd.size()),
            ApproxResult::OverUnder(over, under) => (over.size(), under.size()),
        }
    }

    pub fn cardinality(&self) -> (f64, f64) {
        match self {
            ApproxResult::Exact(bdd) => {
                let c = bdd.cardinality();
                (c, c)
            }
            ApproxResult::OverUnder(over, under) => (over.cardinality(), under.cardinality()),
        }
    }

    pub fn exact_cardinality(&self) -> (BigInt, BigInt) {
        match self {
            ApproxResult::Exact(bdd) => {
                let c = bdd.exact_cardinality();
                (c.clone(), c)
            }
            ApproxResult::OverUnder(over, under) => (over.exact_cardinality(), under.exact_cardinality()),
        }
    }

    pub fn assert(self) -> Self {
        if let ApproxResult::OverUnder(over, under) = &self {
            assert!(over.imp(under).is_true())
        }
        self
    }

    pub fn approx_to_size(&self, size: usize) -> ApproxResult {
        match self {
            ApproxResult::Exact(exact) => {
                if exact.size() <= size {
                    ApproxResult::Exact(exact.clone())
                } else {
                    //let over = exact.overapproximate_to_size(size);
                    //let under = exact.underapproximate_to_size(size);
                    let over = overapproximate_to_size(exact, size);
                    let under = underapproximate_to_size(exact, size);
                    ApproxResult::OverUnder(over, under)
                }
            },
            ApproxResult::OverUnder(over, under) => {
                //let new_over = over.overapproximate_to_size(size);
                //let new_under = under.underapproximate_to_size(size);
                let new_over = overapproximate_to_size(over, size);
                let new_under = underapproximate_to_size(under, size);
                ApproxResult::OverUnder(new_over.clone(), new_under.clone())
            },
        }
    }

    pub fn and(left: &ApproxResult, right: &ApproxResult) -> ApproxResult {
        match (left, right) {
            (ApproxResult::OverUnder(over_l, under_l), ApproxResult::OverUnder(over_r, under_r)) => {
                ApproxResult::OverUnder(
                    over_l.and(over_r), 
                    under_l.and(under_r)
                )
            }            
            (ApproxResult::Exact(exact), ApproxResult::OverUnder(over, under)) | 
            (ApproxResult::OverUnder(over, under), ApproxResult::Exact(exact)) => {
                ApproxResult::OverUnder(
                    over.and(exact), 
                    under.and(exact)
                )
            },
            (ApproxResult::Exact(left), ApproxResult::Exact(right)) => {
                ApproxResult::Exact(left.and(right))
            }
        }        
    }
}

fn recursive_merge(
    items: &[ApproxResult],
    target_size: usize
) -> ApproxResult {
    /*println!(
        "Merging: {:?}",
        items.iter().map(|x| x.size()).collect::<Vec<_>>()
    );*/
    if items.len() == 1 {
        return items[0].clone();
    }
    let mut merged = Vec::new();
    for i in 0..items.len() / 2 {
        merged.push(ApproxResult::and(&items[2*i], &items[2*i + 1]).approx_to_size(target_size));
    }
    if items.len() % 2 == 1 {
        merged.push(items[items.len() - 1].clone());
    }
    return recursive_merge(&merged, target_size);
}

fn greedy_merge(
    bdd: &BddVariableSet,
    items: &[ApproxResult],
    target_size: usize
) -> ApproxResult {
    let mut to_merge = Vec::from_iter(items.iter().cloned());
    let mut result = ApproxResult::Exact(bdd.mk_true());

    while !to_merge.is_empty() {
        let mut best_result = ApproxResult::Exact(bdd.mk_true());
        let mut best_result_index = usize::MAX;
        let mut best_result_size = usize::MAX;

        // Iterate 
        let mut iteration_order = Vec::from_iter(0..to_merge.len());
        iteration_order.sort_by_cached_key(|x| to_merge[*x].size().0);
        iteration_order.reverse();

        for i in iteration_order {
            let merge = ApproxResult::and(&result, &to_merge[i]);
            if merge.size().0 < best_result_size {
                best_result_size = merge.size().0;
                best_result_index = i;
                best_result = merge;
            }
        }
        
        assert_ne!(best_result_size, usize::MAX);
        result = best_result.approx_to_size(target_size);
        //println!("Merged {:?} into {:?}. Remaining {}.", to_merge[best_result_index].size(), result.size(), to_merge.len() - 1);
        to_merge.remove(best_result_index);
    }

    result
}

fn main() {
    let args = Vec::from_iter(std::env::args());
    if args.len() < 3 {
        eprintln!("Usage: {} <target_size> <model_file>", args[0]);
        std::process::exit(2);
    }
    let path = &args[2];
    let target_size = args[1].parse::<usize>().unwrap();
    let model =
        BooleanNetwork::try_from_file(path).expect("Failed to load Boolean network from file");
    let model = model.inline_inputs(true, true);

    /*println!(
        "Loaded model with {} variables and {} parameters.",
        model.num_vars(),
        model.num_parameters()
    );*/

    let stg = SymbolicAsyncGraph::new(&model).unwrap();
    let restriction = stg.mk_unit_colored_vertices();

    let to_merge: Vec<ApproxResult> = stg
            .variables()
            .map(|var| {
                let can_step = stg.var_can_post(var, stg.unit_colored_vertices());
                let is_stable = restriction.minus(&can_step);
                ApproxResult::Exact(is_stable.into_bdd())
            })
            .collect();

    //let fixed_points = recursive_merge(&to_merge, target_size);
    let fixed_points = greedy_merge(stg.symbolic_context().bdd_variable_set(), &to_merge, target_size);

    /*println!(
        "Fixed-points[{}]: {:?}[nodes:{:?}]",
        fixed_points.is_exact(),
        fixed_points.exact_cardinality(),
        fixed_points.size()
    );*/

    let (o_card, u_card) = fixed_points.exact_cardinality();
    let (o_size, u_size) = fixed_points.size();
    println!("{}\t{}\t{}\t{}\t{}", target_size, o_card, u_card, o_size, u_size);

    if fixed_points.is_exact() {
        println!("Exact. Done.");
        std::process::exit(2);
    }

    /*let expected = recursive_merge(&to_merge, 100_000);
    if let ApproxResult::Exact(good_result) = expected {
        println!(
            "Good result: {:?}[nodes:{:?}]",
            good_result.exact_cardinality(),
            good_result.size()
        );
        let fixed_points = recursive_merge(&to_merge, target_size);

        println!(
            "Fixed-points: {:?}[nodes:{:?}]",
            fixed_points.exact_cardinality(),
            fixed_points.size()
        );

        if let ApproxResult::OverUnder(over, under) = fixed_points {
            println!("{} {} {}", under.imp(&over).is_true(), good_result.imp(&over).is_true(), under.imp(&good_result).is_true());
            assert!(under.imp(&over).is_true());
            assert!(good_result.imp(&over).is_true());
            assert!(under.imp(&good_result).is_true());            
        }
    }*/
}

pub fn underapproximate_to_size(bdd: &Bdd, target_size: usize) -> Bdd {
    if target_size >= bdd.size() {
        return bdd.clone();
    }

    let to_cut = bdd.size() - target_size + 1;
    assert!(to_cut > 0 && to_cut < bdd.size());

    // Compute the number of valuations going through each node and sort them.
    let mut weights = bdd
        .node_valuation_weights()
        .into_iter()
        .zip(bdd.pointers())
        .collect::<Vec<_>>();
    weights.sort_by(|(x, px), (y, py)| {
        // Smallest weights go first; if equal, biggest pointers go last.
        x.cmp(y).then(px.cmp(py).reverse())
    });
    let weights = Vec::from_iter(weights.into_iter().take(to_cut).map(|(_, x)| x));

    bdd.underapproximate(&weights)
}

pub fn overapproximate_to_size(bdd: &Bdd, target_size: usize) -> Bdd {
    let negation = bdd.not();
    let under_negation = underapproximate_to_size(&negation, target_size);
    under_negation.not()
}