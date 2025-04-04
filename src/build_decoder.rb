#!/usr/bin/env ruby
# coding: utf-8

require "json"
require 'open3'
require "tempfile"

class CtrlSig_t
  attr_accessor :name, :op_list

  def initialize(name, op)
    @name = name
    @op_list = [op]
  end
  def push(op)
    @op_list.push(op)
  end
  def search(op)
    @op_list.include?(op)
  end

end


File.open("riscv_decoder.json") do |file|
  $arch_table = JSON.load(file)
end

ctrl_idx = ARGV[0]
xlen = ARGV[1].to_s
flen = ARGV[2].to_s
isa  = ARGV[3].to_s
if ARGV.size != 4 then
  STDERR.print "Please specify signal fields in JSON file\n"
end

if isa.include?('b') then
  File.open("b_ext.json") do |file|
    $arch_table = $arch_table + JSON.load(file)
  end
end

if isa.include?('zicond') then
  File.open("zicond_ext.json") do |file|
    $arch_table = $arch_table + JSON.load(file)
  end
end

ctrl_fields = []

$arch_table.each{ |arch|
  if arch["field"].join.length != $arch_table[0]["field"].join.length then
    STDERR.puts "each instruciton fields should have same size"
    exit
  end

  if not arch.key?(ctrl_idx) then
    next
  end
  # if arch.key?("xlen") and not arch["xlen"].include?(xlen) then
  #   next
  # end
  # if arch.key?("flen") and not arch["flen"].include?(flen) then
  #   next
  # end
  arch[ctrl_idx].each {|ctrl|
    puts "inst " + arch["name"].split(' ')[0]
    search_hit = false
    ctrl_fields.each{|ctrl_field|
      if ctrl_field.name == ctrl[0] then
        if not ctrl_field.search(ctrl[1]) then
          ctrl_field.push(ctrl[1])
        end
        search_hit = true
        break
      end
    }
    if not search_hit then
      ctrl_field = CtrlSig_t::new(ctrl[0], "_")
      ctrl_field.push(ctrl[1])
      ctrl_fields.push(ctrl_field)
    end
  }
}

inst_length = $arch_table[0]["field"].join.length

tmp_file = Tempfile.open()
tmp_file.puts 'type fd'
tmp_file.puts '.i ' + inst_length.to_s
tmp_file.puts '.o ' + ctrl_fields.map{|ct|
  if ct.op_list.length == 1 then
    1
  else
    Math.log2(ct.op_list.length).ceil
  end
}.reduce{|a,b| a+b}.to_s

tmp_file.print '.ilb '
inst_length.times{|i| tmp_file.print "inst[" + i.to_s +  "] " }
tmp_file.puts ''
tmp_file.puts '.ob ' + ctrl_fields.map{|ct|
  list = []
  if ct.op_list.length == 1 then
    list.push(ct.name)
  else
    Math.log2(ct.op_list.length).ceil.times{|i|
      list.push(ct.name + "[" + i.to_s + "]")
    }
  end
  list.reverse
}.join(' ')


$arch_table.each{ |arch|
  if not arch.key?(ctrl_idx) then
    next
  end
  if arch.key?("xlen") and not arch["xlen"].include?(xlen) then
    next
  end
  if arch.key?("flen") and not arch["flen"].include?(flen) then
    next
  end
  if arch.key?("isa_ext") and not isa.include?(arch["isa_ext"]) then
    next
  end
  tmp_file.print arch["field"].join.gsub('X', '-')
  tmp_file.print ' '
  ctrl_fields.each {|ctrl|
    puts "inst " + arch["name"].split(' ')[0]
    if arch[ctrl_idx].map{|n| n[0]}.include?(ctrl.name) then
      sig_index = arch[ctrl_idx].map{|n| n[0]}.index(ctrl.name)
      sig_val   = arch[ctrl_idx].map{|n| n[1]}[sig_index]
      puts "ctrl name " + ctrl.name + " sig_index = " + sig_index.to_s + ", sig_val = " + sig_val + ", final index = " + ctrl.op_list.index(sig_val).to_s
      tmp_file.printf("%0*b", Math.log2(ctrl.op_list.length).ceil, ctrl.op_list.index(sig_val))
    else
      tmp_file.printf("%0*b", Math.log2(ctrl.op_list.length).ceil, 0)
    end
  }
  tmp_file.puts ''
}

tmp_file.puts '.e'

tmp_file.close

filename = tmp_file.path
system("cat " + filename)

cmd = "./../tools/espresso-logic/bin/espresso " + tmp_file.path
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

sv_file = open("decoder_" + ctrl_idx + ".sv", "w")

sv_file.puts "package decoder_" + ctrl_idx + "_pkg;"
ctrl_fields.each_with_index{|ct, i|
  sv_file.puts "  typedef enum logic [" + (Math.log2(ct.op_list.length)-1).ceil.to_s + ": 0] {"
  ct.op_list.each_with_index {|op, i|
    sv_file.print "    " + ct.name.upcase + "_" + op.upcase + " = " + i.to_s
    if i == ct.op_list.length - 1 then
      sv_file.print "\n"
    else
      sv_file.print ",\n"
    end
  }
  sv_file.puts "  } " + ct.name + "_t;"
}

sv_file.puts "  typedef struct packed {"
sv_file.puts "    logic dummy;"
ctrl_fields.each{|ct|
  sv_file.puts "    " + ct.name + "_t " + ct.name + ";"
}
sv_file.puts "  } pipe_ctrl_t;"

sv_file.puts "endpackage\n\n"


sv_file.puts "module internal_decoder_" + ctrl_idx + " ("
sv_file.puts "  input logic [" + (inst_length-1).to_s + ":0] inst"
if ctrl_fields.size != 0 then
  sv_file.puts ","
end
ctrl_fields.each_with_index{|ct, i|
  sv_file.print "  output logic "
  if ct.op_list.length > 2 then
    sv_file.print "[" + (Math.log2(ct.op_list.length)-1).ceil.to_s + ": 0]  " + ct.name
  else
    sv_file.print ct.name
  end

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

ct_index = 0
ctrl_fields.each{|ct|
  loop_num = 1
  if ct.op_list.length > 2 then
    loop_num = Math.log2(ct.op_list.length).ceil
  end
  loop_num.times{|i|
    if ct.op_list.length <= 2 then
      sv_file.print "assign " + ct.name + " = "
    else
      sv_file.print "assign " + ct.name + "[" + (loop_num - i - 1).to_s + "] = "
    end

    result_line.each_with_index{|res, res_index|
      ct_field = res.split(' ')[1]
      if ct_field[ct_index] == '1' then
        sv_file.print "tmp_" + res_index.to_s + " | "
      end
    }
    sv_file.print "1'b0;\n"

    ct_index = ct_index + 1
  }
}

sv_file.puts "endmodule\n\n"


sv_file.puts "module decoder_" + ctrl_idx + " ("
sv_file.puts  "  input logic [" + (inst_length-1).to_s + ":0] inst"
if ctrl_fields.size != 0 then
  sv_file.puts ","
end
ctrl_fields.each_with_index{|ct, i|
  sv_file.print "  output decoder_" + ctrl_idx + "_pkg::" + ct.name + "_t " + ct.name

  if i == ctrl_fields.length - 1 then
    sv_file.print "\n"
  else
    sv_file.print ",\n"
  end
}
sv_file.puts ");"

ctrl_fields.each{|ct|
  sv_file.print "logic "
  if ct.op_list.length > 2 then
    sv_file.print "[" + (Math.log2(ct.op_list.length)-1).ceil.to_s + ": 0] raw_" + ct.name + ";\n"
  else
    sv_file.print "raw_" + ct.name + ";\n"
  end
}

sv_file.puts "internal_decoder_" + ctrl_idx + " u_inst ("
sv_file.puts " .inst(inst)"
if ctrl_fields.size != 0 then
  sv_file.puts ","
end
ctrl_fields.each_with_index{|ct,i|
  sv_file.print " ." + ct.name + "(raw_" + ct.name + ")"
  if i == ctrl_fields.length - 1 then
    sv_file.print "\n"
  else
    sv_file.print ",\n"
  end
}
sv_file.puts ");"

ctrl_fields.each{|ct|
  sv_file.print "assign "
  sv_file.print ct.name + " = decoder_" + ctrl_idx + "_pkg::" + ct.name + "_t'(raw_" + ct.name + ");\n"
}

sv_file.print "endmodule\n\n"

sv_file.close
