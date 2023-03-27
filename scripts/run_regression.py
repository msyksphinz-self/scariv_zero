#!/usr/bin/python3

from multiprocessing import Pool, Manager
import os
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
    sim.run_sim(sim_conf, "sanity")

def main():
    parser = argparse.ArgumentParser(description='Compile design and execute tests')
    parser.add_argument('-j', dest="parallel", action='store',
                        default=1, help="Num of Parallel Jobs")

    args = parser.parse_args()

    isa_list=["rv32imc",  "rv32imfc",  "rv32imfdc",
              "rv32imac", "rv32imafc", "rv32imafdc",
              "rv64imc",  "rv64imfc",  "rv64imfdc",
              "rv64imac", "rv64imafc", "rv64imafdc"]
    config_list=["tiny", "small", "standard", "big", "giant"]

    sim_conf = dict()

    sim_conf["parallel"] = int(args.parallel)
    sim_conf["fst_dump"] = False
    sim_conf["cycle"] = 1000000

    for isa in isa_list:
        with Pool(maxtasksperchild=sim_conf["parallel"]) as pool:
            try:
                args_list = [sim_conf.copy() for _ in range(len(config_list))]
                for (a, c) in zip(args_list, config_list):
                    a["isa"] = isa
                    a["isa_ext"] = isa[4:10]
                    a["xlen"] = int(isa[2:4])
                    if "d" in isa :
                        a["flen"] = 64
                    elif "f" in isa :
                        a["flen"] = 32
                    else:
                        a["flen"] = 0
                    if "a" in isa :
                        a["amo"] = 1
                    else:
                        a["amo"] = 0
                    a["use_docker"] = True
                    a["conf"] = c
                pool.map(run_regress, args_list)
            except KeyboardInterrupt:
                print("Caught KeyboardInterrupt, terminating workers", end="\r\n")
                pool.terminate()
                pool.join()

if __name__ == "__main__":
    main()
