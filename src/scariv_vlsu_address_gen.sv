// ------------------------------------------------------------------------
// NAME : scariv_vlsu_address_gen
// TYPE : module
// ------------------------------------------------------------------------
// Address Generator for Vector LSU
// ------------------------------------------------------------------------
//
// ------------------------------------------------------------------------

module scariv_vlsu_address_gen
  import decoder_lsu_ctrl_pkg::*;
  import scariv_lsu_pkg::*;
(
 input logic i_clk,
 input logic i_reset_n,

 input riscv_pkg::xlen_t   i_rs1_base,
 output scariv_pkg::vaddr_t o_vaddr
 );

assign o_vaddr = i_rs1_base;

endmodule // scariv_vlsu_address_gen
