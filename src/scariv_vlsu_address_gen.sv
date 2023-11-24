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

 input logic                     i_valid,
 input riscv_pkg::xlen_t         i_rs1_base,
 input scariv_vec_pkg::vec_pos_t i_vec_step_index,
 output scariv_pkg::vaddr_t      o_vaddr
 );

scariv_vec_pkg::dlen_t r_acc_addr_offset;

assign o_vaddr = i_rs1_base + r_acc_addr_offset;

always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_acc_addr_offset <= 'h0;
  end else begin
    if (i_valid) begin
      if (i_vec_step_index == scariv_vec_pkg::VEC_STEP_W-1) begin
        r_acc_addr_offset <= 'h0;
      end else begin
        r_acc_addr_offset <= r_acc_addr_offset + riscv_vec_conf_pkg::DLEN_W / 8;
      end
    end
  end // else: !if(!i_reset_n)
end // always_ff @ (posedge i_clk, negedge i_reset_n)

endmodule // scariv_vlsu_address_gen
