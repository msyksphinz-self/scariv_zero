#!/usr/bin/python3

import heapq
import argparse
import re

#    for line0 in fp0.read().split('\n'):
#        print (line0)
#        print ("M")
#    for line1 in fp1.read().split('\n'):
#        print(line1)
#        print("H")

def extract_and_compare (file0, file1, max_diff):
    fp0 = open(file0, 'r')
    fp1 = open(file1, 'r')

    prev_cycle0 = 0
    prev_cycle1 = 0

    max_ten = []

    line0 = fp0.readline()
    while line0:
        m0 = re.findall(r'^(\d+) : (\d+) : PC=\[([0-9A-Fa-f]+)\] \(.+\) [0-9A-Fa-f]+ (.+)$', line0)
        if len(m0) != 0:
            # Match log0 instruction commit info
            line1 = fp1.readline()
            while line1:
                m1 = re.findall(r'^(\d+) : (\d+) : PC=\[([0-9A-Fa-f]+)\] \(.+\) [0-9A-Fa-f]+ (.+)$', line1)
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

                    out_str = "inst[%d,%d] PC=%s %-40s cycle %d, %d" % \
                        (int(m0[0][1]), int(m1[0][1]),
                         m0[0][2],
                         m0[0][3],
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

                    break
                line1 = fp1.readline()

        line0 = fp0.readline()

    print("----------------------------")
    print("Top ranked different cycles")
    print("----------------------------")
    for diff, info in sorted(max_ten, reverse=True):
        print("diff=%d : %s" % (diff, info))
    print("----------------------------")

def main():
    parser = argparse.ArgumentParser(description='log1 log2')

    parser.add_argument('log0', type=str, help="cycle log file 0")
    parser.add_argument('log1', type=str, help="cycle log file 1")
    parser.add_argument('-n', type=int, default=10, help="Maximal Ranked diff")
    args = parser.parse_args()

    extract_and_compare (args.log0, args.log1, args.n)


if __name__ == "__main__":
    main()
