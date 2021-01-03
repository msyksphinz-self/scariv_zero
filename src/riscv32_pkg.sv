`default_nettype none

package riscv_pkg;

  import riscv_common_pkg::*;

  localparam XLEN_W = 32;
  localparam VADDR_W = 32;
  localparam PADDR_W = 34;

  localparam PG_IDX_BITS = 12;
  // Page Table Walk
  localparam PPN_W = 12;
endpackage

`default_nettype wire
