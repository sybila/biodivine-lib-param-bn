import sys
import os
import re
import time
from shlex import quote

RE_TIME = re.compile("\\s*real\\s*(\\d+\\.?\\d*)\\s*")

print(">>>>>>>>>> COMPILE RUST BINARIES")

os.system("cargo build --release --examples")

print(">>>>>>>>>> START BENCHMARK RUN")

CUT_OFF = sys.argv[1]
print("Timeout:", CUT_OFF)
BENCH_DIR = sys.argv[2]
print("Benchmark directory:", BENCH_DIR)
ALGORITHM = sys.argv[3]
print("Algorithm:", ALGORITHM)
INTERACTIVE = False
if len(sys.argv) > 4:
	INTERACTIVE = sys.argv[4] == '-i'
print("Interactive:", INTERACTIVE)

# Set binary based on algorithm (also setup so that an input file can be appended there).
BINARY = ""
# Basic forward/backward xie-beerel algorithm.
if ALGORITHM == "BASIC":
	BINARY = "./target/release/examples/algo_base < "
# Fwd/bwd but with saturation.
if ALGORITHM == "BASIC-SATURATION":
    BINARY = "./target/release/examples/algo_base_saturation < "
# Not really lockstep, but computes reachability using saturation and
# only finishes the "symbolically smaller" set. However, it does not consider
# between each parametrisation separately in lockstep reach, so the logic is simpler.
if ALGORITHM == "LOCKSTEP-ASYNC":
    BINARY = "./target/release/examples/algo_lockstep_async < "

if BINARY == "":
	print("ERROR: Unknown algorithm", ALGORITHM)
	exit()

# Set timeout binary based on OS
TIMEOUT = 'none'

if TIMEOUT == 'none':
	code = os.system('timeout --help > /dev/null 2>&1')
	if code == 0:
		TIMEOUT = 'timeout'
		print("Timeout utility ok.")

if TIMEOUT == 'none':
	code = os.system('gtimeout --help > /dev/null 2>&1')
	if code == 0:
		TIMEOUT = 'gtimeout'
		print("Timeout utility ok.")

if TIMEOUT == 'none':
	print('ERROR: No timeout utility found.')
	exit()


# Utility function to check if a given path is a benchmark model.
def is_bench(benchmark):
    return benchmark.endswith(".aeon")

# Create output directory
OUT_DIR = BENCH_DIR + "_run_" + ALGORITHM + "_" + str(int(time.time()))
os.mkdir(OUT_DIR)

# Create output stats file
TIMES = open(OUT_DIR + "/" + BENCH_DIR + "_" + ALGORITHM + "_times.csv", "w")
TIMES.write("Benchmark, Time[s]\n")

# Create an aggregated stats file
AGGREGATION = open(OUT_DIR + "/" + BENCH_DIR + "_" + ALGORITHM + "_aggregated.csv", "w")
AGGREGATION.write("Time[s], No. Completed\n")

# Here, save all runtimes.
AGGREGATION_LIST = []

BENCHMARKS = filter(is_bench, os.listdir(BENCH_DIR))
BENCHMARKS = sorted(BENCHMARKS)

for bench in BENCHMARKS:
	print(">>>>>>>>>> START MODEL", bench)
	if INTERACTIVE:
		print("Write 'skip' to go to next benchmark, 'abort' to end the run, or press enter key to continue...")
		skip = sys.stdin.readline()
		if skip.startswith("skip"):
			print("Skipped!")
			continue
		if skip.startswith("abort"):
			print("Aborted!")
			break
	# Filename without extension
	name = os.path.splitext(bench)[0]
	input_file = BENCH_DIR + "/" + bench
	output_file = OUT_DIR + "/" + name + "_out.txt"
	command = TIMEOUT + " " + CUT_OFF + " time -p " + BINARY + input_file + " > " + output_file + " 2>&1"
	print(command)
	os.system(command)
	with open(output_file, 'r') as f:
		lines = f.read().splitlines()
		if len(lines) > 3:
			time_line = lines[-3]
			last_line = lines[-4]
			is_valid = last_line.startswith("Counted")
			if RE_TIME.match(time_line) and is_valid:
				time = str(RE_TIME.match(time_line).group(1))
				print("Success. Elapsed: ", time)
				TIMES.write(name + ", " + time + "\n")
				AGGREGATION_LIST.append(float(time))
				#for i in range(len(AGGREGATION_LIST)):
				#	if (i + 1) > (5*time):	# 5 entries per second
				#		AGGREGATION_LIST[i] += 1
			else:
				print("Fail. Last line of output:")
				print(lines[-1])
				TIMES.write(name + ", " + "fail" + "\n")
		elif len(lines) > 0:
			print("Fail. Last line of output:")
			print(lines[-1])
			TIMES.write(name + ", " + "fail" + "\n")
		else:
			print("Fail. No output found.")
			TIMES.write(name + ", " + "fail" + "\n")
	TIMES.flush()

AGGREGATION_LIST = sorted(AGGREGATION_LIST)

for i in range(len(AGGREGATION_LIST)):
	AGGREGATION.write(str(AGGREGATION_LIST[i]) + ", " + str(i+1) + "\n")

AGGREGATION.write("3600, " + str(len(AGGREGATION_LIST)) + "\n")

TIMES.close()
AGGREGATION.close()