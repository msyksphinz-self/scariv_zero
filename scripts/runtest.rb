#!/usr/bin/env ruby
# coding: utf-8

require "json"
require "fileutils"
require "optparse"

isa = ""
conf = ""
testcase = ""
opt = OptionParser.new

options = ""
opt.on('--isa VAL') { |v| isa = v }
opt.on('-c VAL', '--conf VAL') { |v| conf = v }
opt.on('-t VAL', '--testcase VAL') { |v| testcase = v}
opt.on('-k', '--kanata') { |v| options += "-k"}

opt.parse!(ARGV)

rv_xlen = 0
rv_flen = 0
isa_ext = isa.slice(4..8)

if not (isa.slice(0..3) == "rv32" or
        isa.slice(0..3) == "rv64") then
  print "isa option need to start from \"rv32\" or \"rv64\""
  exit
else
  rv_xlen = isa.slice(2..3)
  if isa.include?('d') then
    rv_flen = "64"
  elsif isa.include?('f') then
    rv_flen = "32"
  else
    rv_flen = "0"
  end
end

## Build verilator binary
command_build = "make rv#{rv_xlen}_build CONF=#{conf} ISA=#{isa_ext} RV_XLEN=#{rv_xlen} RV_FLEN=#{rv_flen}"
system("#{command_build}")
if $? != 0 then
  exit
end

if rv_xlen == "32" then
  File.open("rv32-tests.json") do |file|
    $test_table = JSON.load(file)
  end
elsif rv_xlen == "64" then
  File.open("rv64-tests.json") do |file|
    $test_table = JSON.load(file)
  end
  File.open("rv64-bench.json") do |file|
    $test_table += JSON.load(file)
  end
end
# $test_table += JSON.load("rv64-bench.json")

select_test = $test_table.select{ |test| (test["name"] == testcase) }
if select_test.size != 1 then
  print "Selected Test are not valid. " + select_test.to_s
  exit
end

output_file = File.basename(select_test[0]["elf"], ".*") + "." + isa + "." + conf + ".log"
command_str = "./msrh_tb_#{isa}_#{conf}-debug -d -e " + "../tests/" + select_test[0]["elf"].to_s + " -o #{output_file}" + " " + options
puts "#{command_str}"
unless system("#{command_str}")
  puts "Got an interupt?"
  exit 0
end

print select_test[0]["name"] + "\t: "
result_stdout = `cat #{output_file}`
if result_stdout.include?("SIMULATION FINISH : FAIL (CODE=100)")
  print "ERROR\n"
elsif result_stdout.include?("SIMULATION FINISH : FAIL")
  print "MATCH\n"
elsif result_stdout.include?("SIMULATION FINISH : PASS")
  print "PASS\n"
else
  print "UNKNOWN\n"
end
