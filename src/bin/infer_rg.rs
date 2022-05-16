use biodivine_lib_param_bn::BooleanNetwork;

/// A simple binary that runs through a source directory (first arg), reads all `.aeon` files
/// from the directory, infers new regulatory graph for each network and then dumps the new
/// networks into a target directory (second arg).
fn main() {
    let args = std::env::args().collect::<Vec<_>>();
    let source_dir = args[1].clone();
    let target_dir = args[2].clone();

    for file in std::fs::read_dir(source_dir).unwrap() {
        let file = file.unwrap();
        let file_name = file.file_name();
        let file_name = file_name.to_str().unwrap();
        if file_name.ends_with(".aeon") {
            println!("Processing: {file_name}");

            let model_string = std::fs::read_to_string(file.path()).unwrap();
            let model = BooleanNetwork::try_from(model_string.as_str()).unwrap();
            let inferred = model.infer_valid_graph().unwrap();
            std::fs::write(format!("{target_dir}/{file_name}"), inferred.to_string()).unwrap();
        }
    }
}
