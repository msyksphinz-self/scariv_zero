#!/usr/bin/python3

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

args = parser.parse_args()

isa = args.isa
conf = args.conf

rv_xlen = 0
rv_flen = 0
isa_ext = isa[4:9]
testcase = args.testcase

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
print(build_command)
subprocess.call(build_command)

test_table = json

if rv_xlen == 32 :
    json_open = open('rv32-tests.json', 'r')
    test_table = json.load(json_open)
elif rv_xlen == 64 :
    rv64_tests_fp = open('rv64-tests.json', 'r')
    test_table = json.load(rv64_tests_fp)
    rv64_bench_fp = open('rv64-bench.json', 'r')
    test_table += json.load(rv64_bench_fp)

select_test = list(filter(lambda x: x["name"] == testcase, test_table))

output_file = os.path.basename(select_test[0]["elf"]) + "." + isa + "." + conf + ".log"
command_str = "./msrh_tb_" + isa + "_" + conf + "-debug -d -e " + "../tests/" + select_test[0]["elf"] + " -o " + output_file + " "
subprocess.call(command_str.split(" "))

print (select_test[0]["name"] + "\t: ")
result_stdout = subprocess.check_output(["cat", output_file])

if "SIMULATION FINISH : FAIL (CODE=100)" in result_stdout.decode('utf-8') :
    print ("ERROR\n")
elif "SIMULATION FINISH : FAIL" in result_stdout.decode('utf-8') :
    print ("MATCH\n")
elif "SIMULATION FINISH : PASS" in result_stdout.decode('utf-8') :
    print ("PASS\n")
else :
    print ("UNKNOWN\n")
