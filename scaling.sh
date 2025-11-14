#!/bin/bash

set -e

/usr/bin/time -f "\t%e\t%M" ./target/release/bench_fixed_points_naive 128 $1
/usr/bin/time -f "\t%e\t%M" ./target/release/bench_fixed_points_naive 256 $1
/usr/bin/time -f "\t%e\t%M" ./target/release/bench_fixed_points_naive 512 $1
/usr/bin/time -f "\t%e\t%M" ./target/release/bench_fixed_points_naive 1024 $1
/usr/bin/time -f "\t%e\t%M" ./target/release/bench_fixed_points_naive 2048 $1
/usr/bin/time -f "\t%e\t%M" ./target/release/bench_fixed_points_naive 4096 $1
/usr/bin/time -f "\t%e\t%M" ./target/release/bench_fixed_points_naive 8192 $1
/usr/bin/time -f "\t%e\t%M" ./target/release/bench_fixed_points_naive 16384 $1
/usr/bin/time -f "\t%e\t%M" ./target/release/bench_fixed_points_naive 32768 $1
/usr/bin/time -f "\t%e\t%M" ./target/release/bench_fixed_points_naive 65536 $1
/usr/bin/time -f "\t%e\t%M" ./target/release/bench_fixed_points_naive 131072 $1
/usr/bin/time -f "\t%e\t%M" ./target/release/bench_fixed_points_naive 262144 $1
/usr/bin/time -f "\t%e\t%M" ./target/release/bench_fixed_points_naive 524288 $1
/usr/bin/time -f "\t%e\t%M" ./target/release/bench_fixed_points_naive 1048576 $1
/usr/bin/time -f "\t%e\t%M" ./target/release/bench_fixed_points_naive 2097152 $1
/usr/bin/time -f "\t%e\t%M" ./target/release/bench_fixed_points_naive 4194304 $1
/usr/bin/time -f "\t%e\t%M" ./target/release/bench_fixed_points_naive 8388608 $1
/usr/bin/time -f "\t%e\t%M" ./target/release/bench_fixed_points_naive 16777216 $1
/usr/bin/time -f "\t%e\t%M" ./target/release/bench_fixed_points_naive 33554432 $1
/usr/bin/time -f "\t%e\t%M" ./target/release/bench_fixed_points_naive 67108864 $1
/usr/bin/time -f "\t%e\t%M" ./target/release/bench_fixed_points_naive 134217728 $1
/usr/bin/time -f "\t%e\t%M" ./target/release/bench_fixed_points_naive 268435456 $1
/usr/bin/time -f "\t%e\t%M" ./target/release/bench_fixed_points_naive 536870912 $1
/usr/bin/time -f "\t%e\t%M" ./target/release/bench_fixed_points_naive 1073741824 $1
/usr/bin/time -f "\t%e\t%M" ./target/release/bench_fixed_points_naive 2147483648 $1