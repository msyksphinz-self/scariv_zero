#!/usr/bin/env ruby
# coding: utf-8

require "json"
require "fileutils"

veri_sim_binary = ARGV[0]
test_json_file = ARGV[1]
log_dir = ARGV[2]
max_threads = ARGV[3].to_i

File.open(test_json_file) do |file|
  $test_table = JSON.load(file)
end

FileUtils.mkdir_p(log_dir)

pass_num = 0

select_test = $test_table.select{ |test| not (test.key?("skip") and test["skip"] == 1) }

xlen = 64
if veri_sim_binary =~ /rv32/ then
  xlen = 32
end

if veri_sim_binary =~ /rv#{xlen}imc/ then
  select_test = select_test.select{ |test| not ((test["elf"] =~ /rv32ud/) or (test["elf"] =~ /rv32uf/) or
                                                (test["elf"] =~ /rv64ud/) or (test["elf"] =~ /rv64uf/)) }
elsif veri_sim_binary =~ /rv#{xlen}imfc/ then
  select_test = select_test.select{ |test| not ((test["elf"] =~ /rv32ud/) or (test["elf"] =~ /rv64ud/)) }
elsif veri_sim_binary =~ /rv#{xlen}imfdc/ then
end

test_num = select_test.size

puts_locks = Queue.new
1.times { puts_locks.push :lock }

select_test.each_slice(max_threads) do |group|
  group.map do |test|
    Thread.new do
      output_file = log_dir + "/" + test["name"] + "_" + File.basename(test["elf"], ".*") + ".log"
      command_str = "./" + ARGV[0] + " -e " + "../tests/" + test["elf"] + " -o " + output_file
      # puts "#{command_str} 2> /dev/null 1> /dev/null"
      system("#{command_str} 2> /dev/null 1> /dev/null")

      lock = puts_locks.pop
      print test["name"] + "\t: "
      result_stdout = `cat #{output_file}`
      if result_stdout.include?("SIMULATION FINISH : FAIL (CODE=100)")
        print "ERROR\n"
      elsif result_stdout.include?("SIMULATION FINISH : FAIL")
        print "MATCH\n"
        pass_num = pass_num + 1
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
printf("|%s | %d / %d (%03.2f%%)|\n", veri_sim_binary, pass_num, test_num, (pass_num.to_f / test_num.to_f) * 100.0)
printf("============================\n")
