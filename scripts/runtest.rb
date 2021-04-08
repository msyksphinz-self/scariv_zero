#!/usr/bin/env ruby
# coding: utf-8

require "json"
require "fileutils"

File.open("tests.json") do |file|
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
  command_str = "./" + ARGV[0] + " -e " + "../tests/" + test["elf"]
  stdout_txt = log_dir + "stdout_" + test["name"] + ".txt"
  stderr_txt = log_dir + "stderr_" + test["name"] + ".txt"
  system("#{command_str} 2> #{stderr_txt} 1> #{stdout_txt}")
  print test["name"] + "\t: "
  result_stdout = `cat #{stdout_txt}`
  if result_stdout.include?("SIMULATION FINISH : PASS")
    print "PASS\n"
    pass_num = pass_num + 1
  elsif result_stdout.include?("SIMULATION FINISH : FAIL")
    print "ERROR\n"
  else
    print "UNKNOWN\n"
  end
  test_num = test_num +1
}

printf("============================\n")
printf("PASS / TOTAL = %d / %d\n", pass_num, test_num)
printf("============================\n")
