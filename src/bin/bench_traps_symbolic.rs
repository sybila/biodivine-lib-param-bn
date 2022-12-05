use biodivine_lib_param_bn::biodivine_std::bitvector::BitVector;
use biodivine_lib_param_bn::fixed_points::FixedPoints;
use biodivine_lib_param_bn::solver_context::BnSolverContext;
use biodivine_lib_param_bn::trap_spaces::dual_symbolic_encoding::SymbolicMostPermissiveGraph;
use biodivine_lib_param_bn::trap_spaces::solver_iterator::SolverIterator;
use biodivine_lib_param_bn::trap_spaces::Space;
use biodivine_lib_param_bn::{BooleanNetwork, FnUpdate};

fn main() {
    let args = Vec::from_iter(std::env::args());
    let path = &args[1];
    let mut model = BooleanNetwork::try_from_file(path).unwrap();

    for var in model.variables() {
        if model.get_update_function(var).is_none() {
            model
                .set_update_function(var, Some(FnUpdate::Const(false)))
                .unwrap();
        }
    }

    //let model = model.inline_inputs();

    println!(
        "Loaded model with {} variables and {} parameters.",
        model.num_vars(),
        model.num_parameters()
    );

    let graph = SymbolicMostPermissiveGraph::new(model.clone()).unwrap();
    graph.fixed_points();
}
