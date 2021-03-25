#!/usr/bin/env ruby
# coding: utf-8

require "json"
require "fileutils"

File.open("tests.json") do |file|
  $test_table = JSON.load(file)
end

log_dir = 'log/'

FileUtils.mkdir_p(log_dir)

$test_table.each{ |test|
  command_str = "./msrh_tb_rv64_standard " + "-e " + "../tests/" + test["elf"]
  stdout_txt = log_dir + "stdout_" + test["name"] + ".txt"
  stderr_txt = log_dir + "stderr_" + test["name"] + ".txt"
  system("#{command_str} 2> #{stderr_txt} 1> #{stdout_txt}")
  print test["name"] + "\t: "
  result_stdout = `cat #{stdout_txt}`
  if result_stdout.include?("SIMULATION FINISH : PASS")
    print "PASS\n"
  elsif result_stdout.include?("SIMULATION FINISH : ERROR")
    print "ERROR\n"
  else
    print "UNKNOWN\n"
  end
}
