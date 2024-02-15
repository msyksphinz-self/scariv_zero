#!/usr/bin/python3

import heapq
import argparse
import re

def read_file(file_path):
    # Open file and return generator to read files as needed.
    with open(file_path, 'r') as file:
        for line in file:
            yield line

def parse_line(line):
    # Analyze line and generate information
    return re.findall(r'^(\d+) : (\d+) : PC=\[([0-9A-Fa-f]+)\] (\(.+\)) [0-9A-Fa-f]+ (.+)$', line)

def compare_files (file0, file1, max_diff):
    fp0 = open(file0, 'r')
    fp1 = open(file1, 'r')

    prev_cycle0 = 0
    prev_cycle1 = 0

    max_ten = []

    region_rank = []

    lines0 = read_file(file0)
    lines1 = read_file(file1)

    region_start_cycle0 = 0
    region_start_cycle1 = 0

    for line0 in lines0:
        m0 = parse_line(line0)
        if len(m0) != 0:
            # Match log0 instruction commit info
            for line1 in lines1:
                m1 = parse_line(line1)
                if len(m1) != 0:
                    # --------------
                    # Start compare
                    # --------------
                    if m0[0][2] != m1[0][2]:
                        print("Warning! log0 PC=%x, log1 PC=%x" % (int(m0[0][2]), int(m1[0][2])))
                        exit
                    # if m0[0][1] != m1[0][1]:
                    # to    print("Warning! log0 count=%d, log1 count=%d" % (int(m0[0][1]), int(m1[0][1])))

                    cycle0 = int(m0[0][0])
                    cycle1 = int(m1[0][0])

                    diff_cycle0 = cycle0 - prev_cycle0
                    diff_cycle1 = cycle1 - prev_cycle1

                    out_str = "cycle[%d,%d] inst[%d,%d] PC=%s %s,%s %-40s cycle %d, %d" % \
                        (int(m0[0][0]), int(m1[0][0]),
                         int(m0[0][1]), int(m1[0][1]),
                         m0[0][2],
                         m0[0][3], m1[0][3],
                         m0[0][4],
                         cycle0, cycle1)
                    print (out_str, end='')

                    if diff_cycle0 != diff_cycle1:
                        print(" | Cycle Different! +%d, +%d" % (diff_cycle0, diff_cycle1))
                    else:
                        print("")

                    prev_cycle0 = cycle0
                    prev_cycle1 = cycle1

                    diff_cycle01 = diff_cycle0 - diff_cycle1

                    if len(max_ten) < max_diff:
                        heapq.heappush(max_ten, (diff_cycle01, out_str))
                    elif diff_cycle01 > max_ten[0][0]:
                        heapq.heapreplace(max_ten, (diff_cycle01, out_str))

                    if int(m0[0][1]) % 1000 == 0:
                        diff_region_cycle = (cycle0 - region_start_cycle0) - (cycle1 - region_start_cycle1)
                        if len(region_rank) < 10:
                            heapq.heappush(region_rank, (diff_cycle01, int(m0[0][1])))
                        elif diff_region_cycle > region_rank[0][0]:
                            heapq.heapreplace(region_rank, (diff_region_cycle, int(m0[0][1])))
                        region_start_cycle0 = cycle0
                        region_start_cycle1 = cycle1


                    break


    print("----------------------------")
    print("Top ranked different cycles")
    print("----------------------------")
    for diff, info in sorted(max_ten, reverse=True):
        print("diff=%d : %s" % (diff, info))
    print("----------------------------")


    print("----------------------------")
    print("Top ranked different region")
    print("----------------------------")
    for diff, info in sorted(region_rank, reverse=True):
        print("diff=%d : %d - %d" % (diff, info, info + 1000))
    print("----------------------------")

def main():
    parser = argparse.ArgumentParser(description='log1 log2')

    parser.add_argument('log0', type=str, help="cycle log file 0")
    parser.add_argument('log1', type=str, help="cycle log file 1")
    parser.add_argument('-n', type=int, default=10, help="Maximal Ranked diff")
    args = parser.parse_args()

    compare_files (args.log0, args.log1, args.n)


if __name__ == "__main__":
    main()
