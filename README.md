[![Crates.io](https://img.shields.io/crates/v/biodivine-lib-param-bn?style=flat-square)](https://crates.io/crates/biodivine-lib-param-bn) [![Api Docs](https://img.shields.io/badge/docs-api-yellowgreen?style=flat-square)](https://docs.rs/biodivine-lib-param-bn/) [![Continuous integration](https://img.shields.io/github/workflow/status/sybila/biodivine-lib-param-bn/build?style=flat-square)](https://github.com/sybila/biodivine-lib-param-bn/actions?query=workflow%3Abuild) [![Coverage](https://img.shields.io/codecov/c/github/sybila/biodivine-lib-param-bn?style=flat-square)](https://codecov.io/gh/sybila/biodivine-lib-param-bn) [![GitHub issues](https://img.shields.io/github/issues/sybila/biodivine-lib-param-bn?style=flat-square)](https://github.com/sybila/biodivine-lib-param-bn/issues) [![Dev Docs](https://img.shields.io/badge/docs-dev-orange?style=flat-square)](https://biodivine.fi.muni.cz/docs/biodivine-lib-param-bn/latest/) [![GitHub last commit](https://img.shields.io/github/last-commit/sybila/biodivine-lib-param-bn?style=flat-square)](https://github.com/sybila/biodivine-lib-param-bn/commits/master) [![Crates.io](https://img.shields.io/crates/l/biodivine-lib-param-bn?style=flat-square)](https://github.com/sybila/biodivine-lib-param-bn/blob/master/LICENSE)

# Biodivine Parametrised Boolean Networks

Rust library for working with parametrised Boolean networks. Supports: 
 - Read/Write Boolean network models from `.aeon` and `.sbml` formats.
 - Basic static analysis, like monotonicity checking or network decomposition.
 - Network parameters and partially unknown update functions.
 - Fully symbolic asynchronous transition graphs.
 - (Legacy) semi-symbolic asynchronous transition graphs.

To learn more, check out the documentation in our [tutorial module](https://docs.rs/biodivine-lib-param-bn/latest/biodivine_lib_param_bn/tutorial/index.html). 

#### PBN to colour graph dump

To analyse (very) small networks, it can be useful to 
dump them as explicit coloured graphs. There is a binary for that as well.

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