`default_nettype none

package riscv_pkg;

  localparam XLEN_W = 64;
  localparam VADDR_W = 39;
  localparam PADDR_W = 56;

  // Page Table Walk
  localparam PPN_W = 26;

endpackage

`default_nettype wire
