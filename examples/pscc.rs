use biodivine_lib_param_bn::pscc::{decomposition, PsccContext};
use biodivine_lib_param_bn::BooleanNetwork;
use std::convert::TryFrom;
use std::io::Read;
use std::sync::atomic::{AtomicU32, Ordering};

fn main() {
    let mut buffer = String::new();
    std::io::stdin().read_to_string(&mut buffer).unwrap();

    let model = BooleanNetwork::try_from(buffer.as_str()).unwrap();
    println!("Model: {}", model);
    println!("Model vars: {}", model.graph().num_vars());

    let context = PsccContext::new(model);

    let iterations = AtomicU32::new(0);
    decomposition(&context, context.all_vertices(), &iterations);

    println!("Iterations: {}", iterations.fetch_add(1, Ordering::SeqCst));
}
