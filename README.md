# Biodivine Parametrised Boolean Networks
Rust library for working with parametrised Boolean networks. Work in progress.

## PBN to colour graph dump

To analyse (very) small networks, it can be useful to 
dump them as explicit coloured graphs. There is a binary for that.

First, run `cargo build --release`.

You can then find the binary in `target/release/dump-graph`. 
The binary takes `.aeon` model on standard input and dumps
the graph to standard output. So to convert a PBN to its 
coloured asynchronous transition
graph, simply call `dump-graph < ~/path/to/model.aeon > graph_file.txt`.

Since the graph is explicit, expect the output size to be unmanageable
for PBNs with roughly >10 variables and >1000 valid parametrisations 
(with parametrisations being the bigger problem).

You can test the functionality on `aeon_models/g2a_*.aeon` models which
should all be sufficiently small.   