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


def run_regress(sim_conf):
    sim = runtest.verilator_sim()
    sim.build_sim(sim_conf)
    sim.run_sim(sim_conf, "aapg")

def main():
    parser = argparse.ArgumentParser(description='Compile design and execute tests')
    parser.add_argument('-j', dest="parallel", action='store',
                        default=1, help="Num of Parallel Jobs")
    parser.add_argument('-n', dest="num_tests", action='store',
                        default=100, help="Num of Tsets")
    parser.add_argument('--priv', dest="priv_mode", action='store',
                        default="m", help="Running Mode (m/s/u)")

    args = parser.parse_args()

    sim_conf = dict()

    sim_conf["parallel"] = int(args.parallel)
    sim_conf["fst_dump"] = False
    sim_conf["cycle"] = 1000000

    t_delta = datetime.timedelta(hours=9)
    JST = datetime.timezone(t_delta, 'JST')
    dir_name = datetime.datetime.now(JST).strftime('%Y%m%d%H%M')
    num_tests = int(args.num_tests)

    config_name = "config_priv_" + args.priv_mode

    build_command = ["make",
                     "-C", "../tests/aapg",
                     "DIR=" + dir_name,
                     "NUM_GEN=" + str(num_tests),
                     "CONFIG_YAML=" + config_name + ".yaml"]
    build_result = subprocess.Popen(build_command, text=True)
    build_result.wait()
    if build_result.returncode != 0:
        return BuildResult.FAIL

    # Generate test case json list
    json_testlist = []
    with open("aapg_" + dir_name + ".json", 'w') as f:
        for i in range(num_tests):
            json_testlist += [{"name": "config_{:05d}".format(i),
                              "group": ["aapg"],
                              "elf": "../../../tests/aapg/" + dir_name + "/bin/out_" + config_name + "_{:05d}.riscv".format(i),
                              "xlen": 64}]
        f.write(json.dumps(json_testlist, indent=0))

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
    sim_conf["testlist"] = ["aapg_" + dir_name + ".json"]
    run_regress(sim_conf)

if __name__ == "__main__":
    main()
