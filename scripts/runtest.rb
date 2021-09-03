#!/usr/bin/env ruby
# coding: utf-8

require "json"
require "fileutils"

veri_sim_binary = ARGV[0]
test_json_file = ARGV[1]
max_threads = ARGV[2].to_i

File.open(test_json_file) do |file|
  $test_table = JSON.load(file)
end

log_dir = 'log/'

FileUtils.mkdir_p(log_dir)

pass_num = 0

select_test = $test_table.select{ |test| not (test.key?("skip") and test["skip"] == 1) }
test_num = select_test.size

puts_locks = Queue.new
1.times { puts_locks.push :lock }

select_test.each_slice(max_threads) do |group|
  group.map do |test|
    Thread.new do
      output_file = log_dir + test["name"] + "_" + File.basename(test["elf"], ".*") + ".log"
      command_str = "./" + ARGV[0] + " -e " + "../tests/" + test["elf"] + " -o " + output_file
      # puts "#{command_str} 2> /dev/null 1> /dev/null"
      system("#{command_str} 2> /dev/null 1> /dev/null")

      lock = puts_locks.pop
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
      puts_locks.push(lock)
    end
  end.each(&:join)
end


printf("============================\n")
printf("PASS / TOTAL = %d / %d\n", pass_num, test_num)
printf("============================\n")
