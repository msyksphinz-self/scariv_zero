`default_nettype none

`include "riscv_common_pkg.sv"

package riscv_pkg;

  import riscv_common_pkg::*;

  localparam XLEN_W = 64;
  localparam VADDR_W = 39;
  localparam PADDR_W = 56;

  localparam PG_IDX_BITS = 12;
  // Page Table Walk
  localparam PPN_W = 26;
endpackage

`default_nettype wire
