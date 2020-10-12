use std::io::Read;
use biodivine_lib_param_bn::BooleanNetwork;
use biodivine_lib_param_bn::pscc::{PsccContext, decomposition};
use std::convert::TryFrom;

fn main() {
    let mut buffer = String::new();
    std::io::stdin().read_to_string(&mut buffer).unwrap();

    let model = BooleanNetwork::try_from(buffer.as_str()).unwrap();
    println!("Model: {}", model);
    println!("Model vars: {}", model.graph().num_vars());

    let context = PsccContext::new(model);

    decomposition(&context, context.all_vertices());
}