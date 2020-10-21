# Biodivine PBN Library (Symbolic SCC)

Rust library for working with parametrised Boolean networks. 

This branch contains code for analysing coloured SCCs of a 
PBN using fully symbolic algorithms.

To execute the SCC decomposition algorithms, run:

```
cargo run --release --exmaple pscc < path/to/model.aeon
```

Example benchmark models can be found in the `benchmarks`
directory.

Currently, we only print the size of the SCCs as they 
are discovered.

You can also build the binary using `cargo build --release --example pscc`,
 the executable will be located in `target/release/example/pscc`.