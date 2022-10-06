#!/usr/bin/python3

from multiprocessing import Pool
import os
import subprocess
import json
import argparse

parser = argparse.ArgumentParser(description='Compile design and execute tests')
parser.add_argument('-i', '--isa', dest='isa', action='store',
                    default='rv32imc',
                    help='ISA of design comfiguration')

parser.add_argument('-c', '--conf', dest='conf', action='store',
                    default='standard',
                    help="Configuration of design : tiny, small, standard, big, giant")
parser.add_argument('-t', '--testcase', dest='testcase', action='store',
                    default='testcase',
                    help="Testcase of run")
parser.add_argument('-k', '--kanata', dest="katana", action='store_true',
                    default=False, help="Generate Katana Log file")
parser.add_argument('-j', dest="parallel", action='store',
                    default=1, help="Num of Parallel Jobs")
parser.add_argument('-d', dest="debug", action="store_true",
                    default=False, help="Generate FST Dump File")
parser.add_argument('--cycle', dest="cycle", action="store",
                    default=100000000, help="Cycle Limitation")

args = parser.parse_args()

isa = args.isa
conf = args.conf

rv_xlen = 0
rv_flen = 0
isa_ext = isa[4:9]
testcase = args.testcase
parallel = int(args.parallel)
fst_dump = args.debug
cycle    = args.cycle

if not (isa[0:4] == "rv32" or isa[0:4] == "rv64") :
    print ("isa option need to start from \"rv32\" or \"rv64\"")
    exit
else:
    rv_xlen = int(isa[2:4])
    print(isa_ext)
    if "d" in isa_ext :
        rv_flen = 64
    elif "f" in isa_ext :
        rv_flen = 32

## Build verilator binary
build_command = ["make", "rv" + str(rv_xlen) + "_build", "CONF=" + conf,  "ISA=" + isa_ext, "RV_XLEN=" + str(rv_xlen), "RV_FLEN=" + str(rv_flen)]
if fst_dump :
    build_command += ["DEBUG=on"]
else:
    build_command += ["DEBUG=off"]


print(build_command)
build_result = subprocess.run(build_command)

if build_result.returncode != 0 :
    exit()

test_table = json

if rv_xlen == 32 :
    json_open = open('rv32-tests.json', 'r')
    test_table = json.load(json_open)
elif rv_xlen == 64 :
    rv64_tests_fp = open('rv64-tests.json', 'r')
    test_table = json.load(rv64_tests_fp)
    rv64_bench_fp = open('rv64-bench.json', 'r')
    test_table += json.load(rv64_bench_fp)

select_test = list(filter(lambda x: ((x["name"] == testcase) or
                                     (testcase in x["group"]) and
                                     (x["skip"] != 1 if "skip" in x else True)) , test_table))
# max_length = max(map(lambda x: len(x["name"]), select_test))

show_stdout = len(select_test) == 1

base_dir = "sim_" + isa + "_" + conf
os.makedirs(base_dir, exist_ok=True)
os.makedirs(base_dir + "/" + testcase, exist_ok=True)

def execute_test(test):
    output_file = os.path.basename(test["name"]) + "." + isa + "." + conf + ".log"
    command_str = "../../msrh_tb_" + isa + "_" + conf
    if fst_dump :
        command_str += "-debug -d "
    command_str += " -c " + str(cycle)
    command_str += " -e "
    command_str += test["elf"]
    command_str += " -o " + output_file
    # print (command_str)
    subprocess.run(command_str, shell=True, capture_output=not show_stdout, cwd=base_dir + '/' + testcase)
    result_stdout = subprocess.check_output(["cat", output_file], cwd=base_dir + '/' + testcase)

    print (test["name"] + "\t: ", end='')
    if "SIMULATION FINISH : FAIL (CODE=100)" in result_stdout.decode('utf-8') :
        print ("ERROR")
    elif "SIMULATION FINISH : FAIL" in result_stdout.decode('utf-8') :
        print ("MATCH")
    elif "SIMULATION FINISH : PASS" in result_stdout.decode('utf-8') :
        print ("PASS")
    elif "COMMIT DEADLOCKED" in result_stdout.decode('utf-8') :
        print ("DEADLOCK")
    else :
        print ("UNKNOWN")

with Pool(parallel) as pool:
    pool.map(execute_test, select_test)
