use biodivine_lib_param_bn::BooleanNetwork;
use std::convert::TryFrom;
use biodivine_lib_param_bn::symbolic_async_graph::SymbolicAsyncGraph;
use std::path::Path;

fn main() {
    let bench_dir = "./benchmark-base";
    let bench_out = "./benchmark-generated";

    if !Path::new(bench_out).exists() {
        std::fs::create_dir(bench_out).unwrap();
    }

    let dir_contents = std::fs::read_dir(bench_dir).unwrap();
    for model in dir_contents {
        let model = model.unwrap();
        let name = model.file_name().to_str().unwrap().to_string();
        if name.ends_with(".aeon") {
            let model_file_contents = std::fs::read_to_string(model.path()).unwrap();
            let mut model = BooleanNetwork::try_from(model_file_contents.as_str()).unwrap();
            clear_inputs(&mut model);
            write_model(bench_out, &name, &model);
            clear_fn2(&mut model);
            write_model(bench_out, &name, &model);
            clear_fn3(&mut model);
            write_model(bench_out, &name, &model);
        }
    }
}

fn write_model(bench_out: &str, name: &str, model: &BooleanNetwork) {
    let graph = SymbolicAsyncGraph::new(model.clone()).unwrap();

    let problem_size = graph.unit_colored_vertices().approx_cardinality();
    let magnitude = problem_size.log2().ceil() as usize;
    if magnitude >= 20 && magnitude <= 100 {
        let path = format!("{}/{}_{}", bench_out, magnitude, name);
        let out_path = Path::new(path.as_str());
        std::fs::write(out_path, model.to_string()).unwrap();
    }
}

/// Mark input nodes as parameters.
fn clear_inputs(network: &mut BooleanNetwork) {
    for var in network.variables() {
        if network.regulators(var).is_empty() {
            network.set_update_function(var, None).unwrap();
        }
    }
}

fn clear_fn2(network: &mut BooleanNetwork) {
    for var in network.variables() {
        if network.regulators(var).len() == 2 {
            network.set_update_function(var, None).unwrap();
        }
    }
}

fn clear_fn3(network: &mut BooleanNetwork) {
    for var in network.variables() {
        if network.regulators(var).len() == 2 {
            network.set_update_function(var, None).unwrap();
        }
    }
}