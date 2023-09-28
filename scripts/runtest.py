#!/usr/bin/python3

from enum import Enum
import math
import re
import docker
from multiprocessing import Pool, Manager
import multiprocessing
import os
import sys
import subprocess
import json
import argparse

class BuildResult(Enum):
    SUCCESS = 0
    FAIL = 1


class verilator_sim:

    manager = Manager()
    result_dict = manager.dict({'pass': 0, 'match': 0, 'timeout': 0, 'error': 0, 'deadlock': 0, 'unknown': 0, 'cycle_deleg' : 0})
    result_detail_dict = manager.dict()
    test_count = manager.Value('i', 0)

    def build_sim(self, sim_conf):
        # Make spike-dpi
        build_command = ["make",
                         "-C", "../spike_dpi"]

        current_dir = os.path.abspath("../")
        user_id    = os.getuid()
        group_id   = os.getgid()

        if sim_conf["use_docker"]:
            cli = docker.from_env()
            build_result = cli.containers.run(image="msyksphinz/scariv:run_env",
                                              auto_remove=True,
                                              user=user_id,
                                              volumes={current_dir: {'bind': '/work/scariv', 'mode': 'rw'}},
                                              working_dir="/work/scariv/verilator_sim/",
                                              detach=True,
                                              tty=True,
                                              command=build_command)
            for line in build_result.logs(stream=True):
                # message = line.decode('utf-8').strip()
                message = line.decode('utf-8')
                if message:
                    print(message, end='')
            build_result.wait()
        else:
            # build_result = subprocess.Popen(build_command, stdout=subprocess.STDOUT, stderr=subprocess.STDOUT, text=True)
            build_result = subprocess.Popen(build_command, text=True)
            build_result.wait()
            # for line in iter(build_result.stdout.readline, ""):
            #     print(line, end="\r")

            if build_result.returncode != 0:
                return BuildResult.FAIL

        ## Build verilator binary
        build_command = ["make",
                         "rv" + str(sim_conf["xlen"]) + "_build",
                         "CONF="        +     sim_conf["conf"],
                         "ISA="         +     sim_conf["isa_ext"],
                         "RV_XLEN="     + str(sim_conf["xlen"]),
                         "RV_FLEN="     + str(sim_conf["flen"]),
                         "EXT_ISA="      + str(sim_conf["amo"]),
                         "RV_BITMANIP=" + str(sim_conf["bitmanip"])]

        current_dir = os.path.abspath("../")
        user_id    = os.getuid()
        group_id   = os.getgid()
        docker_env = dict()

        if sim_conf["use_docker"]:
            build_result = cli.containers.run(image="msyksphinz/scariv:run_env",
                                              auto_remove=True,
                                              user=user_id,
                                              volumes={current_dir: {'bind': '/work/scariv', 'mode': 'rw'}},
                                              working_dir="/work/scariv/verilator_sim/",
                                              detach=True,
                                              tty=True,
                                              command=build_command)

            for line in build_result.logs(stream=True):
                # message = line.decode('utf-8').strip()
                message = line.decode('utf-8')
                if message:
                    print(message, end='')
        else:
            build_result = subprocess.Popen(build_command, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)

            for line in iter(build_result.stdout.readline, ""):
                print(line, end="\r")

                with open("build_" + sim_conf["isa"] + "_" + sim_conf["conf"] + ".log", 'a') as f:
                    f.write(line)

            build_result.wait()

        if build_result.returncode != 0:
            return BuildResult.FAIL

    def execute_test(self, sim_conf, show_stdout, base_dir, testcase, test):
        output_file = os.path.basename(test["name"]) + "." + sim_conf["isa"] + "." + sim_conf["conf"] + ".log"
        run_command = ["../../scariv_tb_" + sim_conf["isa"] + "_" + sim_conf["conf"]]
        if sim_conf["fst_dump"] :
            run_command += ["--dump"]
            run_command += ["--dump_start", str(sim_conf["dump_start_time"])]

        if sim_conf["kanata"] :
            run_command += ["-k"]
        run_command += ["-c", str(sim_conf["cycle"])]
        run_command += ["-e", test["elf"]]
        run_command += ["-o", output_file]

        command_log_fp = open(base_dir + '/' + testcase + '/sim.cmd', mode='w')
        command_log_fp.write (" ".join(run_command))
        command_log_fp.close()

        current_dir = os.path.abspath("../")
        user_id    = os.getuid()
        group_id   = os.getgid()
        env = os.environ.copy()

        if sim_conf["use_docker"]:
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
                       ] + run_command
        else:
            command = run_command

        if sim_conf["use_docker"]:
            cli = docker.from_env()
            run_process = cli.containers.run(image="msyksphinz/scariv:run_env",
                                             auto_remove=True,
                                             user=user_id,
                                             volumes={current_dir: {'bind': '/work/scariv', 'mode': 'rw'}},
                                             working_dir="/work/scariv/verilator_sim/" + base_dir + "/" + testcase,
                                             detach=True,
                                             tty=True,
                                             command=run_command)
            if show_stdout:
                for line in run_process.logs(stream=True):
                    # message = line.decode('utf-8').strip()
                    message = line.decode('utf-8')
                    if message:
                        print(message, end='')
            else:
                run_process.wait()
        else:
            if show_stdout:
                subprocess.call(command, bufsize=0, text=True, cwd=base_dir + '/' + testcase)
            else:
                run_process = subprocess.Popen(command, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, bufsize=0, text=True,
                                           cwd=base_dir + '/' + testcase)
                # for line in iter(run_process.stdout.readline, ""):
                #     print(line, end="")
                #     sys.stdout.flush()
                run_process.wait()

        result_stdout = subprocess.check_output(["cat", output_file], cwd=base_dir + '/' + testcase)
        if "expected_time" in test and \
           sim_conf["conf"] in test["expected_time"] :
            expected_time = test["expected_time"][sim_conf["conf"]]
        else:
            expected_time = 0

        self.show_results(test["name"], result_stdout, expected_time)

    def show_results(self, testname, result_stdout, expected_time):
        self.test_count.value += 1
        print ("%*d / %d : %-*s : " % (int(math.log10(self.test_length)+1), self.test_count.value, self.test_length, self.max_testname_length, testname), end="")
        if "SIMULATION FINISH : FAIL (CODE=100)" in result_stdout.decode('utf-8') :
            print ("ERROR", end="\r\n")
            self.result_detail_dict[testname] = "error"
            self.result_dict['error'] += 1
        elif "SIMULATION FINISH : FAIL" in result_stdout.decode('utf-8') :
            print ("MATCH", end="\r\n")
            self.result_detail_dict[testname] = "match"
            self.result_dict['match'] += 1
        elif "SIMULATION TIMEOUT" in result_stdout.decode('utf-8') :
            print ("TIMEOUT", end="\r\n")
            self.result_detail_dict[testname] = "timeout"
            self.result_dict['timeout'] += 1
        elif "SIMULATION FINISH : PASS" in result_stdout.decode('utf-8') :
            if expected_time != 0:
                match = re.search(r'RUNNING TIME : (\d+)', result_stdout.decode('utf-8'))
                if not match:
                    print ("\nRUNNING TIME can't be get\n")
                    print ("UNKNOWN", end="\r\n")
                    self.result_detail_dict[testname] = "unknown"
                    self.result_dict['unknown'] += 1
                else:
                    rtl_time = int(match.group(1))
                    exp_time = int(expected_time)
                    if (float(abs(rtl_time - exp_time)) / float(rtl_time) > 0.05) :
                        print ("CYCLE DEGRADED", end="\r\n")
                        print ("\nERROR : Expected Cycle Different. RTL = %d, EXPECTED = %d. Diff = %.2f%%\n" % (rtl_time, exp_time, float(abs(rtl_time - exp_time)) / float(rtl_time) * 100.0))
                        self.result_detail_dict[testname] = "cycle_deleg"
                        self.result_dict['cycle_deleg'] += 1
                    else:
                        print ("PASS", end="\r\n")
                        self.result_detail_dict[testname] = "pass"
                        self.result_dict['pass'] += 1
            else:
                print ("PASS", end="\r\n")
                self.result_detail_dict[testname] = "pass"
                self.result_dict['pass'] += 1
        elif "COMMIT DEADLOCKED" in result_stdout.decode('utf-8') :
            print ("DEADLOCK", end="\r\n")
            self.result_detail_dict[testname] = "deadlock"
            self.result_dict['deadlock'] += 1
        else :
            print ("UNKNOWN", end="\r\n")
            self.result_detail_dict[testname] = "unknown"
            self.result_dict['unknown'] += 1

    def execute_test_wrapper (self, args):
        return self.execute_test(*args)

    def run_sim(self, sim_conf, testcase):
        test_table = json
        if sim_conf["xlen"] == 32 :
            json_open = open('rv32-tests.json', 'r')
            test_table = json.load(json_open)
        elif sim_conf["xlen"] == 64 :
            rv64_tests_fp = open('rv64-tests.json', 'r')
            test_table = json.load(rv64_tests_fp)
            rv64_bench_fp = open('rv64-bench.json', 'r')
            test_table += json.load(rv64_bench_fp)
            rv64_rvv_fp = open('rv64-rvv-tests.json', 'r')
            test_table += json.load(rv64_rvv_fp)
            rv64_aapg_fp = open('../tests/rv64-aapg.json', 'r')
            test_table += json.load(rv64_aapg_fp)

        select_test = list(filter(lambda x: ((x["name"] == testcase) or
                                             (testcase in x["group"]) and
                                             (x["skip"] != 1 if "skip" in x else True)) , test_table))
        self.max_testname_length = max(map(lambda x: len(x["name"]), select_test))
        self.test_length = len(select_test)

        show_stdout = len(select_test) == 1

        base_dir = "sim_" + sim_conf["isa"] + "_" + sim_conf["conf"]
        os.makedirs(base_dir, exist_ok=True)
        os.makedirs(base_dir + "/" + testcase, exist_ok=True)

        if len(select_test) == 1:
            args_list = (sim_conf, show_stdout, base_dir, testcase, select_test[0])
            self.execute_test_wrapper (args_list)
        else:
            process = multiprocessing.current_process()
            if process.daemon:
                for t in select_test:
                    args_list = (sim_conf, show_stdout, base_dir, testcase, t)
                    self.execute_test_wrapper (args_list)

            else:
                with Pool(maxtasksperchild=sim_conf["parallel"]) as pool:
                    try:
                        args_list = [(sim_conf, show_stdout, base_dir, testcase, t) for t in select_test]
                        pool.map(self.execute_test_wrapper, args_list)
                    except KeyboardInterrupt:
                        print("Caught KeyboardInterrupt, terminating workers", end="\r\n")
                        pool.terminate()
                        pool.join()

        print (self.result_dict)
        with open(base_dir + '/' + testcase + '/result.json', 'w') as f:
            json.dump(self.result_detail_dict.copy(), f, indent=4)
        with open(base_dir + '/' + testcase + '/result.json', 'a') as f:
            json.dump(self.result_dict.copy(), f, indent=4)
        print ("Result : " + base_dir + '/' + testcase + '/result.json')
        if len(select_test) == 1:
            output_file = os.path.basename(select_test[0]["name"]) + "." + sim_conf["isa"] + "." + sim_conf["conf"] + ".log"
            print("Detail log : " + base_dir + '/' + select_test[0]["name"] + '/' + output_file)

def main():
    parser = argparse.ArgumentParser(description='Compile design and execute tests')
    parser.add_argument('-i', '--isa', dest='isa', action='store',
	                default='rv32imc',
	                help='ISA of design comfiguration')
    parser.add_argument('--vlen', dest='vlen', action='store',
	                default=128,
	                help='Defalut Vector Length')
    parser.add_argument('-c', '--conf', dest='conf', action='store',
	                default='standard',
	                help="Configuration of design : tiny, small, standard, big, giant")
    parser.add_argument('-t', '--testcase', dest='testcase', action='store',
	                default='testcase',
	                help="Testcase of run")
    parser.add_argument('-k', '--kanata', dest="kanata", action='store_true',
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

    sim_conf = dict()
    sim_conf["isa"] = args.isa
    sim_conf["conf"] = args.conf

    testcase = args.testcase
    sim_conf["isa_ext"]         = sim_conf["isa"][4:]
    sim_conf["vlen"]            = args.vlen
    sim_conf["parallel"]        = int(args.parallel)
    sim_conf["fst_dump"]        = args.debug
    sim_conf["dump_start_time"] = args.dump_start
    sim_conf["cycle"]           = args.cycle
    sim_conf["kanata"]          = args.kanata
    sim_conf["use_docker"]      = args.docker


    if not (sim_conf["isa"][0:4] == "rv32" or sim_conf["isa"][0:4] == "rv64") :
        print ("isa option need to start from \"rv32\" or \"rv64\"")
        exit
    else:
        sim_conf["xlen"] = int(sim_conf["isa"][2:4])
        if "d" in sim_conf["isa_ext"] :
            sim_conf["flen"] = 64
        elif "f" in sim_conf["isa_ext"] :
            sim_conf["flen"] = 32
        else:
            sim_conf["flen"] = 0
        if "a" in sim_conf["isa_ext"] :
            sim_conf["amo"] = 1
        else:
            sim_conf["amo"] = 0
        if "b" in sim_conf["isa_ext"] :
            sim_conf["bitmanip"] = 1
        else:
            sim_conf["bitmanip"] = 0

    sim = verilator_sim()

    if sim.build_sim(sim_conf) == BuildResult.FAIL:
        return
    sim.run_sim(sim_conf, testcase)

if __name__ == "__main__":
    main()
