`default_nettype none

package riscv_pkg;

  localparam XLEN_W = 64;
  localparam VADDR_W = 39;
  localparam PADDR_W = 56;

  localparam PG_IDX_BITS = 12;
  // Page Table Walk
  localparam PPN_W = PADDR_W - PG_IDX_BITS;

  function logic [riscv_pkg::XLEN_W-1: 0] map_sstatus (logic [risv_pkg::XLEN_W-1: 0] mstatus);
    return {mstatus [riscv_pkg::XLEN_W-1],
            25'b0,
            1'b0, 1'b0, 2'b00, mstatus[33:32],
            9'b0_0000_0000, 1'b0, 1'b0, 1'b0, mstatus[19], mstatus[18],
            1'b0, mstatus[16:15], mstatus[14:13], mstatus[12:11], 2'b00,
            mstatus[8], 1'b0, 1'b0, mstatus[5], 1'b0, 1'b0, 1'b0, mstatus[1], 1'b0};
  endfunction // map_sstatus

endpackage

`default_nettype wire
