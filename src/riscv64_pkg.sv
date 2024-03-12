`default_nettype none

package riscv_pkg;

import riscv_fpu_pkg::*;

  parameter XLEN_W = 64;
  parameter FLEN_W = riscv_fpu_pkg::FLEN_W;
  parameter VADDR_W = 39;
  parameter VADDR_MSB = 38;
  parameter PADDR_W = 56;

  localparam PG_IDX_BITS = 12;
  // Page Table Walk
  localparam PPN_W = PADDR_W - PG_IDX_BITS;
  localparam PG_LEVELS = 3;

  typedef logic [XLEN_W-1: 0]   xlen_t;
  typedef logic [XLEN_W/8-1: 0] xlenb_t;

  function xlen_t map_sstatus (xlen_t mstatus);
    return {mstatus [XLEN_W-1],
            25'b0,
            1'b0, 1'b0, 2'b00, mstatus[33:32],
            9'b0_0000_0000, 1'b0, 1'b0, 1'b0, mstatus[19], mstatus[18],
            1'b0, mstatus[16:15], mstatus[14:13], mstatus[12:11], mstatus[10: 9],
            mstatus[8], 1'b0, 1'b0, mstatus[5], 1'b0, 1'b0, 1'b0, mstatus[1], 1'b0};
  endfunction // map_sstatus

  //                         SXL  , UXL
  localparam init_mstatus = {2'b10, 2'b10, 32'h0};
  localparam MSTATUS_SD = 63;

endpackage

`default_nettype wire
