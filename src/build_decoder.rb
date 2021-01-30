#!/usr/bin/env ruby

require "json"
require 'open3'

File.open("riscv_decoder.json") do |file|
  $arch_table = JSON.load(file)
end

ctrl_fields = []

$arch_table.each{ |arch|
  if arch["field"].join.length != $arch_table[0]["field"].join.length then
    STDERR.puts "each instruciton fields should have same size"
    exit
  end

  arch["inst_ctrl"].each {|ctrl|
    if not ctrl_fields.include?(ctrl) then
      ctrl_fields.push(ctrl)
    end
  }
}

inst_length = $arch_table[0]["field"].join.length

require "tempfile"

tmp_file = Tempfile.open()
tmp_file.puts 'type fd'
tmp_file.puts '.i ' + inst_length.to_s
tmp_file.puts '.o ' + ctrl_fields.length.to_s
tmp_file.print '.ilb '
inst_length.times{|i| tmp_file.print "inst[" + i.to_s +  "] " }
tmp_file.puts ''
tmp_file.puts '.ob ' + ctrl_fields.join(' ').to_s


$arch_table.each{ |arch|
  tmp_file.print arch["field"].join.gsub('X', '-')
  tmp_file.print ' '
  ctrl_fields.each {|ctrl|
    if arch["inst_ctrl"].include?(ctrl) then
      tmp_file.print '1'
    else
      tmp_file.print '0'
    end
  }
  tmp_file.puts ''
}

tmp_file.puts '.e'

tmp_file.close

puts tmp_file.path

cmd = "./espresso " + tmp_file.path
result_line = ""
Open3.popen2e(cmd) do |stdin, stdout_err, stderr, wait_thr|
  while line = stdout_err.gets
    result_line += line
  end
end

result_line = result_line.split("\n")
result_line = result_line.drop(6)
result_line.pop

puts result_line

sv_file = open("decoder.sv", "w")

sv_file.puts "module decoder ("
sv_file.puts "  input logic [" + (inst_length-1).to_s + ":0] inst,"
ctrl_fields.each_with_index{|ct, i|
  sv_file.print "  output logic " + ct
  if i == ctrl_fields.length - 1 then
    sv_file.print "\n"
  else
    sv_file.print ",\n"
  end
}
sv_file.puts ");"

result_line.each_with_index{|line, index|
  inst_field = line.split(' ')[0]

  sv_file.print "wire tmp_" + index.to_s + " = "
  inst_field.chars.each_with_index{|char, ch_idx|
    inst_index = inst_length - ch_idx - 1
    if char == '0' then
      sv_file.print "!inst[" + inst_index.to_s + "] & "
    elsif char == '1' then
      sv_file.print "inst[" + inst_index.to_s + "] & "
    end
  }
  sv_file.print "1'b1;\n"
}

ctrl_fields.each_with_index{|ctrl, ct_index|
  sv_file.print "assign " + ctrl + " = "
  result_line.each_with_index{|res, res_index|
    ctrl_field = res.split(' ')[1]
    if ctrl_field[ct_index] == '1' then
      sv_file.print "tmp_" + res_index.to_s + " | "
    end
  }
  sv_file.print "1'b0;\n"
}

sv_file.puts "endmodule"

sv_file.close
