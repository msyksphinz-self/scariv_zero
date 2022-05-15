#!/usr/bin/python3

import test_rv32

import argparse

parser = argparse.ArgumentParser(description='Compile design and execute tests')
parser.add_argument('-i', '--isa', dest='isa', action='store',
                    default='rv32imc',
                    help='ISA of design comfiguration')

parser.add_argument('-c', '--conf', dest='conf', action='store',
                    default='standard',
                    help="Configuration of design : tiny, small, standard, big, giant")
parser.add_argument('-t', '--testcase', dest='test', action='store',
                    default='testcase',
                    help="Testcase of run")
parser.add_argument('-k', '--kanata', dest="katana", action='store_true',
                    default=False, help="Generate Katana Log file")

args = parser.parse_args()

print(args)

isa = args.isa

rv_xlen = 0
rv_flen = 0
isa_ext = isa.slice[4:8]

if not (isa.slice[0:3] == "rv32" or isa.slice[0:3] == "rv64") :
    print ("isa option need to start from \"rv32\" or \"rv64\"")
    exit
else:
    rv_xlen = isa.slice[2:3]
    if isa.include('d') :
        rv_flen = "64"
    elif isa.include('f') :
        rv_flen = "32"
    else :
        rv_flen = "0"


## Build verilator binary
command_build = "make rv#{rv_xlen}_build CONF=#{conf} ISA=#{isa_ext} RV_XLEN=#{rv_xlen} RV_FLEN=#{rv_flen}"
print (command_build)
system("#{command_build}")

select_test = test_table.select{ |test| (test["name"] == testcase) }
if select_test.size != 1 :
    print ("Selected Test are not valid. " + select_test.to_s)
    exit


output_file = File.basename(select_test[0]["elf"], ".*") + "." + isa + "." + conf + ".log"
command_str = "./msrh_tb_#{isa}_#{conf}-debug -d -e " + "../tests/" + select_test[0]["elf"].to_s + " -o #{output_file}" + " " + options
system("#{command_str}")

print select_test[0]["name"] + "\t: "
result_stdout = `cat #{output_file}`
if result_stdout.include?("SIMULATION FINISH : FAIL (CODE=100)") :
    print ("ERROR\n")
elif result_stdout.include?("SIMULATION FINISH : FAIL") :
    print ("MATCH\n")
elif result_stdout.include?("SIMULATION FINISH : PASS") :
    print ("PASS\n")
else :
    print ("UNKNOWN\n")
