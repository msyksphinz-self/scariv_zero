#!/usr/bin/env ruby
# coding: utf-8

require "json"
require "fileutils"

veri_sim_binary = ARGV[0]
if veri_sim_binary.include?("rv32") then
  test_json_file = "rv32-tests.json"
elsif veri_sim_binary.include?("rv64") then
  test_json_file = "rv64-tests.json"
else
  puts "Invalid Verilator binary specified. Exit"
  exit
end


File.open(test_json_file) do |file|
  $test_table = JSON.load(file)
end

log_dir = 'log/'

FileUtils.mkdir_p(log_dir)

test_num = 0
pass_num = 0

$test_table.each{ |test|
  if test.key?("skip") and test["skip"] == 1 then
    next
  end
  output_file = log_dir + File.basename(test["elf"], ".*") + ".log"
  command_str = "./" + ARGV[0] + " -e " + "../tests/" + test["elf"] + " -o " + output_file
  system("#{command_str} 2> /dev/null 1> /dev/null")
  print test["name"] + "\t: "
  result_stdout = `cat #{output_file}`
  if result_stdout.include?("SIMULATION FINISH : FAIL")
    print "ERROR\n"
  elsif result_stdout.include?("SIMULATION FINISH : PASS")
    print "PASS\n"
    pass_num = pass_num + 1
  else
    print "UNKNOWN\n"
  end
  test_num = test_num +1
}

printf("============================\n")
printf("PASS / TOTAL = %d / %d\n", pass_num, test_num)
printf("============================\n")
