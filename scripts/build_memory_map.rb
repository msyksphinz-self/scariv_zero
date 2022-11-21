#!/usr/bin/env ruby
# coding: utf-8

require "json"
require 'open3'
require "tempfile"

json_file = ARGV[0]
rv_xlen = ARGV[1].to_i
if rv_xlen != 32 and rv_xlen != 64 then
  printf("rv_xlen should be 32 or 64.");
  exit
end

File.open(json_file) do |file|
  $map_table = JSON.load(file)
end

out_sv = File.open("pma_map.sv", "w")

printf(out_sv, "module pma_map\n")
printf(out_sv, "  import scariv_lsu_pkg::*;\n")
printf(out_sv, "(\n")
printf(out_sv, "  input logic [riscv_pkg::PADDR_W-1: 0] i_pa,\n")
printf(out_sv, "  output logic o_map_hit,\n")
printf(out_sv, "  output map_attr_t o_map_attr\n")
printf(out_sv, ");\n\n\n")

printf(out_sv, "localparam MAP_TABLE_SIZE = %d;\n", $map_table.size)

printf(out_sv, "logic [MAP_TABLE_SIZE-1: 0] w_hit_addr;\n")
printf(out_sv, "map_attr_t w_map_attr[MAP_TABLE_SIZE];\n")

$map_table.each_with_index{ |map, map_index|
  if not map.key?("base") then
    STDERR.puts "Each memory map need to set base address"
    exit
  end

  if not map.key?("size") then
    STDERR.puts "Each memory map need to set size"
    exit
  end

  base_addr = map["base"].gsub('_', '').gsub("0x", "").hex
  size_byte = map["size"].gsub('_', '').gsub("0x", "").hex
  if size_byte & (size_byte-1) != 0 then
    STDERR.puts "size field need to be power of 2"
    exit
  end

  paddr_bitlen = rv_xlen == 32 ? 34 : 56
  printf(out_sv, "assign w_hit_addr[%2d] = (i_pa & %d'h%014x) == %d'h%014x;  // Address Region : %x - %x\n",
         map_index,
         paddr_bitlen,
         ~(size_byte-1) & ((1 << paddr_bitlen)-1),
         paddr_bitlen,
         base_addr & ~(size_byte-1),
         base_addr,
         base_addr + size_byte -1)
  printf(out_sv, "assign w_map_attr[%2d].r = 1'b%01d;\n", map_index, map["attr"]["R"]);
  printf(out_sv, "assign w_map_attr[%2d].w = 1'b%01d;\n", map_index, map["attr"]["W"]);
  printf(out_sv, "assign w_map_attr[%2d].x = 1'b%01d;\n", map_index, map["attr"]["X"]);
  printf(out_sv, "assign w_map_attr[%2d].a = 1'b%01d;\n", map_index, map["attr"]["A"]);
  printf(out_sv, "assign w_map_attr[%2d].c = 1'b%01d;\n", map_index, map["attr"]["C"]);

}

printf(out_sv, "\n\n")

printf(out_sv, "assign o_map_hit = |w_hit_addr;\n")
printf(out_sv, "always_comb begin\n")
printf(out_sv, "case (w_hit_addr)\n")
$map_table.each_with_index{ |map, map_index|
  printf(out_sv, "  %d'b%0*b : o_map_attr = w_map_attr[%d];\n",
         $map_table.size, $map_table.size, 1 << map_index, map_index, map_index)
}
printf(out_sv, "  default   : o_map_attr = 'h0;\n")
printf(out_sv, "endcase\n")
printf(out_sv, "end\n\n")

printf(out_sv, "endmodule\n")

out_sv.close
