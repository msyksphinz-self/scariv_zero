#!/usr/bin/python3

from multiprocessing import Pool, Manager
import os
import sys
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
parser.add_argument('--dump_start', dest="dump_start", action="store",
                    default=0, help="FST Dump Start Time")
parser.add_argument('--cycle', dest="cycle", action="store",
                    default=100000000, help="Cycle Limitation")
parser.add_argument('--docker', dest="docker", action="store_true",
                    default=False, help="Use Docker environment")

args = parser.parse_args()

isa = args.isa
conf = args.conf

rv_xlen = 0
rv_flen = 0
rv_amo  = 0
isa_ext = isa[4:10]
testcase = args.testcase
parallel = int(args.parallel)
fst_dump = args.debug
dump_start_time = args.dump_start
cycle    = args.cycle
use_docker = args.docker

if not (isa[0:4] == "rv32" or isa[0:4] == "rv64") :
    print ("isa option need to start from \"rv32\" or \"rv64\"")
    exit
else:
    rv_xlen = int(isa[2:4])
    if "d" in isa_ext :
        rv_flen = 64
    elif "f" in isa_ext :
        rv_flen = 32
    if "a" in isa_ext :
        rv_amo = 1

## Build verilator binary
build_command = ["make",
                 "rv" + str(rv_xlen) + "_build",
                 "CONF=" + conf,
                 "ISA=" + isa_ext,
                 "RV_XLEN=" + str(rv_xlen),
                 "RV_FLEN=" + str(rv_flen),
                 "RV_AMO=" + str(rv_amo)]

current_dir = os.path.abspath("../")
user_id    = os.getuid()
group_id   = os.getgid()
env = os.environ.copy()
if use_docker:
    env["CCACHE_DIR"] = "/work/scariv/ccache"

if use_docker:
    command = ["docker",
               "run",
               "--cap-add=SYS_PTRACE",
               "--security-opt=seccomp=unconfined",
               "--rm",
               "-it",
               "-v",
               current_dir + ":/work/scariv",
               "--user", str(user_id) + ":" + str(group_id),
               "-w",
               "/work/scariv/verilator_sim",
               "msyksphinz/scariv:run_env"] + build_command
else:
    command = build_command

build_result = subprocess.Popen(command, env=env, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)

for line in iter(build_result.stdout.readline, ""):
    print(line, end='\r\n')

    with open("build_" + isa + "_" + conf + ".log", 'a') as f:
        f.write(line)

build_result.wait()

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
    rv64_aapg_fp = open('../tests/rv64-aapg.json', 'r')
    test_table += json.load(rv64_aapg_fp)

select_test = list(filter(lambda x: ((x["name"] == testcase) or
                                     (testcase in x["group"]) and
                                     (x["skip"] != 1 if "skip" in x else True)) , test_table))
# max_length = max(map(lambda x: len(x["name"]), select_test))

show_stdout = len(select_test) == 1

base_dir = "sim_" + isa + "_" + conf
os.makedirs(base_dir, exist_ok=True)
os.makedirs(base_dir + "/" + testcase, exist_ok=True)

manager = Manager()
result_dict = manager.dict({'pass': 0, 'match': 0, 'error': 0, 'deadlock': 0, 'unknown': 0})

def execute_test(test):
    output_file = os.path.basename(test["name"]) + "." + isa + "." + conf + ".log"
    run_command = ["../../scariv_tb_" + isa + "_" + conf]
    if fst_dump :
        run_command += ["--dump"]
        run_command += ["--dump_start", str(dump_start_time)]

    run_command += ["-c", str(cycle)]
    run_command += ["-e", test["elf"]]
    run_command += ["-o", output_file]

    command_log_fp = open(base_dir + '/' + testcase + '/sim.cmd', mode='w')
    command_log_fp.write (" ".join(run_command))
    command_log_fp.close()

    if use_docker:
        command = ["docker",
                   "run",
                   "--cap-add=SYS_PTRACE",
                   "--security-opt=seccomp=unconfined",
                   "--rm",
                   "-it",
                   "-v",
                   current_dir + ":/work/scariv",
                   "--user", str(user_id) + ":" + str(group_id),
                   "-w",
                   "/work/scariv/verilator_sim/" + base_dir + "/" + testcase,
                   "msyksphinz/scariv:run_env"] + run_command
    else:
        command = run_command

    if use_docker:
        run_process = subprocess.Popen(command, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, bufsize=0, text=True)
    else:
        run_process = subprocess.Popen(command, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, bufsize=0, text=True,
                                       cwd=base_dir + '/' + testcase)

    for line in iter(run_process.stdout.readline, ""):
        sys.stdout.write(line)
        sys.stdout.flush()

    try:
        run_process.wait()
    except KeyboardInterrupt:
        run_process.send_signal(subprocess.signal.SIGINT)
        run_process.wait()

    result_stdout = subprocess.check_output(["cat", output_file], cwd=base_dir + '/' + testcase)

    print (test["name"] + "\t: ", end='')
    if "SIMULATION FINISH : FAIL (CODE=100)" in result_stdout.decode('utf-8') :
        print ("ERROR")
        result_dict['error'] += 1
    elif "SIMULATION FINISH : FAIL" in result_stdout.decode('utf-8') :
        print ("MATCH")
        result_dict['match'] += 1
    elif "SIMULATION FINISH : PASS" in result_stdout.decode('utf-8') :
        print ("PASS")
        result_dict['pass'] += 1
    elif "COMMIT DEADLOCKED" in result_stdout.decode('utf-8') :
        print ("DEADLOCK")
        result_dict['deadlock'] += 1
    else :
        print ("UNKNOWN")
        result_dict['unknown'] += 1

with Pool(maxtasksperchild=parallel) as pool:
    pool.map(execute_test, select_test)

print (result_dict)
with open(base_dir + '/result.json', 'w') as f:
    json.dump(result_dict, f, default=str)
