`default_nettype none

package riscv_pkg;

import riscv_fpu_pkg::*;

  localparam XLEN_W = 32;
  localparam VADDR_W = 32;
  localparam VADDR_MSB = 31;
  localparam PADDR_W = 34;

  localparam PG_IDX_BITS = 12;
  // Page Table Walk
  localparam PPN_W = PADDR_W - PG_IDX_BITS;
  localparam PG_LEVELS = 2;

  typedef logic [XLEN_W-1: 0]   xlen_t;
  typedef logic [XLEN_W/8-1: 0] xlenb_t;

  function riscv_pkg::xlen_t map_sstatus (xlen_t mstatus);
    return {mstatus [riscv_pkg::XLEN_W-1],
            8'b0000_0000,
            1'b0, 1'b0, 1'b0, mstatus[19], mstatus[18],
            1'b0, mstatus[16:15], mstatus[14:13], mstatus[12:11], mstatus[10: 9],
            mstatus[8], 1'b0, 1'b0, mstatus[5], 1'b0, 1'b0, 1'b0, mstatus[1], 1'b0};
  endfunction

  localparam init_mstatus = 'h0;
  localparam MSTATUS_SD = 31;

endpackage

`default_nettype wire
