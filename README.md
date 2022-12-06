[![Crates.io](https://img.shields.io/crates/v/biodivine-lib-param-bn?style=flat-square)](https://crates.io/crates/biodivine-lib-param-bn) [![Api Docs](https://img.shields.io/badge/docs-api-yellowgreen?style=flat-square)](https://docs.rs/biodivine-lib-param-bn/) [![Continuous integration](https://img.shields.io/github/workflow/status/sybila/biodivine-lib-param-bn/build?style=flat-square)](https://github.com/sybila/biodivine-lib-param-bn/actions?query=workflow%3Abuild) [![Coverage](https://img.shields.io/codecov/c/github/sybila/biodivine-lib-param-bn?style=flat-square)](https://codecov.io/gh/sybila/biodivine-lib-param-bn) [![GitHub issues](https://img.shields.io/github/issues/sybila/biodivine-lib-param-bn?style=flat-square)](https://github.com/sybila/biodivine-lib-param-bn/issues) [![Dev Docs](https://img.shields.io/badge/docs-dev-orange?style=flat-square)](https://biodivine.fi.muni.cz/docs/biodivine-lib-param-bn/latest/) [![GitHub last commit](https://img.shields.io/github/last-commit/sybila/biodivine-lib-param-bn?style=flat-square)](https://github.com/sybila/biodivine-lib-param-bn/commits/master) [![Crates.io](https://img.shields.io/crates/l/biodivine-lib-param-bn?style=flat-square)](https://github.com/sybila/biodivine-lib-param-bn/blob/master/LICENSE)

# Biodivine Parametrised Boolean Networks

Rust library for working with parametrised Boolean networks. Supports: 
 - Read/Write Boolean network models from `.aeon`, `.bnet`, and `.sbml` formats.
 - Basic static analysis, like monotonicity checking or network decomposition.
 - Network parameters and partially unknown update functions.
 - Fully symbolic asynchronous transition graphs.
 - (Legacy) semi-symbolic asynchronous transition graphs.

To learn more, check out the documentation in our [tutorial module](https://docs.rs/biodivine-lib-param-bn/latest/biodivine_lib_param_bn/tutorial/index.html). 

### Utility binaries

Aside from the main library, there are a few basic binaries that are used for
testing or benchmarking the functionality of the main library. At the moment,
these binaries are not a part of the automated testing process as they need
to be compiled with optimizations and generally utilize a completely different
workflow than standard Cargo tests. In the future, these should be included
as separate workflows, but for now, you can use them for manual testing in
case you change something in the associated algorithms.

In general, all of these binaries assume a single argument and that is 
a path to a Boolean network file in any of the supported formats (however,
`.bnet` is not recommended for tests that involve regulation monotonicity).
As such, you can run the following command to execute any of the tests 
(using your desired `BINARY_NAME`):

```bash
cargo run --release --bin BINARY_NAME --features print-progress -- MODEL_PATH
```

> Some algorithms can print intermediate progress when the `print-progress`
> feature flag is active. If you don't want this behaviour, remove 
> `--features print-progress` from the command.

#### Testing feedback-vertex-set and independent-cycles

> Feedback vertex set problem asks to compute the set of vertices such that
> without these vertices, the graph becomes acyclic. A *minimum* such set is
> typically desired.

> Independent cycles problem asks to compute the set of non-intersecting 
> cycles such that once removed, the graph becomes acyclic (i.e. every
> other cycle intersects with a member of this independent set). A *maximum* such
> set is typically desired.

There are four binaries related to this feature: `check_fvs`, `check_ic`,
`check_nfvs`, and `check_nic`. The first two test greedy optimizing search
for feedback vertex sets and independent cycles. The other two then test
the negative variant of the problem (we don't test the positive variant
as functionally it is symmetrical to the negative case). Every binary
checks the validity of basic invariants that should hold for any 
correct result.

As these are greedy, non-optimal algorithms, you should expect
the algorithms to finish even for very large networks (e.g. >1000 variables).
In particular, every model in the BBM benchmark can be processed in less than
a second without issues.

#### Testing fixed-points and projected fixed-points

> Fixed-point problem asks to identify every vertex (or combination of 
> parametrisation and vertex for parametrised networks) with no outgoing 
> transitions.

> Projected fixed-points problem asks to identify valuations of the desired
> subset of variables for which there exists at least one fixed-point. In 
> particular, fixed-point vertex `x` is a vertex for which there exists a
> color `c` (parameter valuation) such that `x` is a fixed-point in `c`.
> Symmetrically, color `c` is a fixed-point color if there exists a vertex
> `x` such that `x` is a fixed-point in `c`.

There is one test binary `check_fixed_points` which compares the results of
several algorithms to ensure correctness. Additionally, there is 
`bench_fixed_points_naive`, `bench_fixed_points_symbolic`, `bench_fixed_points_solver`, 
`bench_fixed_points_symbolic_vertices`, and 
`bench_fixed_points_symbolic_colors` which independently test the performance
of each algorithm.

Note that the naive algorithm often runs out of memory on non-trivial models.
As such, `check_fixed_points` can fail once the network is large or has many 
parameters. That's why benchmarks are separated into individual binaries: 
because some algorithms can and will time out or OOM.

#### PBN to colour graph dump

To analyse (very) small networks, it can be useful to 
dump them as explicit coloured graphs. There is a binary called `dump-graph`
that does exactly this:

```bash
cargo build --release
./target/release/dump-graph MODEL_PATH > graph_edges.txt
```
The binary takes a path to a model file as the first argument, and dumps
the graph to standard output.

Since the graph is explicit, expect the output size to be unmanageable
for PBNs with roughly >10 variables and >1000 valid parametrizations 
(with parametrizations being the bigger bottleneck).

You can test the functionality on `aeon_models/g2a_*.aeon` models which
should all be sufficiently small.   