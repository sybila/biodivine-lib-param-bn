use biodivine_lib_param_bn::BooleanNetwork;

fn main() {
    let benchmarks = std::fs::read_dir("./sbml_models/real_world").unwrap();

    for bench_dir in benchmarks {
        let bench_dir = bench_dir.unwrap();
        if !bench_dir.file_type().unwrap().is_dir() {
            eprintln!("SKIP: {} is not a directory.", bench_dir.path().display());
            continue;
        }

        let readme_path = bench_dir.path().join("model.txt");
        if !readme_path.exists() {
            eprintln!("ERROR: Missing README in {}.", bench_dir.path().display());
        }

        let sbml_model_path = bench_dir.path().join("model.sbml");
        let model_string = std::fs::read_to_string(sbml_model_path).unwrap();
        let model = BooleanNetwork::from_sbml(&model_string);
        let model = match model {
            Err(err) => {
                eprintln!(
                    "ERROR: Invalid SBML model in {}.",
                    bench_dir.path().display()
                );
                eprintln!("{}", err);
                continue;
            }
            Ok((model, _)) => model,
        };

        let aeon_model_path = bench_dir.path().join("model.aeon");
        std::fs::write(aeon_model_path, model.to_string()).unwrap();
    }
}