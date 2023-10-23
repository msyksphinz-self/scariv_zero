#!/usr/bin/python3

from multiprocessing import Pool, Manager
import os
import datetime
import sys
import subprocess
import json
import argparse
import runtest

def run_regress_wrapper (args):
    return run_regress(*args)

def main():
    parser = argparse.ArgumentParser(description='Compile design and execute tests')
    parser.add_argument('-j', dest="parallel", action='store',
                        default=1, help="Num of Parallel Jobs")
    parser.add_argument('-c', '--conf', dest="conf_yaml", action='store',
                        required=True, help="Config File")
    parser.add_argument('-n', dest="num_tests", action='store',
                        default=100, help="Num of Tsets")
    # parser.add_argument('--priv', dest="priv_mode", action='store',
    #                     default="m", help="Running Mode (m/s/u)")

    args = parser.parse_args()

    sim_conf = dict()

    sim_conf["parallel"] = int(args.parallel)
    sim_conf["fst_dump"] = False
    sim_conf["cycle"] = 100000000

    t_delta = datetime.timedelta(hours=9)
    JST = datetime.timezone(t_delta, 'JST')
    dir_name = "generated/" + datetime.datetime.now(JST).strftime('%Y%m%d%H%M')
    num_tests = int(args.num_tests)

    # config_name = "config_priv_" + args.priv_mode
    config_file = args.conf_yaml

    build_command = ["make",
                     "-C", "../tests/aapg",
                     "DIR=" + dir_name,
                     "NUM_GEN=" + str(num_tests),
                     "CONFIG_YAML=" + os.path.realpath(config_file),
                     "ISA=rv64imafdc",
                     "ABI=lp64"]
    build_result = subprocess.Popen(build_command, text=True)
    build_result.wait()
    if build_result.returncode != 0:
        return BuildResult.FAIL

    sim_conf["isa"] = "rv64imafdc"
    sim_conf["isa_ext"] = sim_conf["isa"][4:10]
    sim_conf["xlen"] = int(sim_conf["isa"][2:4])
    if "d" in sim_conf["isa"] :
        sim_conf["flen"] = 64
    elif "f" in sim_conf["isa"] :
        sim_conf["flen"] = 32
    else:
        sim_conf["flen"] = 0
    if "a" in sim_conf["isa"] :
        sim_conf["amo"] = 1
    else:
        sim_conf["amo"] = 0
    if "b" in sim_conf["isa"] :
        sim_conf["bitmanip"] = 1
    else:
        sim_conf["bitmanip"] = 0
    sim_conf["use_docker"] = False
    sim_conf["parallel"] = sim_conf['parallel']
    sim_conf["conf"] = "standard"
    sim_conf["kanata"] = False


    sim = runtest.verilator_sim()
    sim.build_sim(sim_conf)

    # Generate test case json list
    json_testlist = []
    base_dir = "sim_" + sim_conf["isa"] + "_" + sim_conf["conf"]
    group_name = os.path.splitext(os.path.basename(config_file))[0] + "_" + dir_name
    json_testlist_name = base_dir + '/' + group_name + '/' + group_name + ".json"

    sim_conf["testlist"] = [json_testlist_name]

    bin_files = os.listdir("../tests/aapg/" + dir_name + "/bin/")

    os.makedirs(base_dir + '/' + group_name)
    with open(json_testlist_name, 'w') as f:
        for bin in bin_files:
            json_testlist += [{"name": bin.replace('.riscv',''),
                               "group": [group_name],
                               "elf": "../../../tests/aapg/" + dir_name + "/bin/" +  bin,
                               "xlen": 64}]
        f.write(json.dumps(json_testlist, indent=0))

    sim.run_sim(sim_conf, group_name)

if __name__ == "__main__":
    main()
