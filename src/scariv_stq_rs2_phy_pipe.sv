module scariv_stq_rs2_phy_pipe
  import scariv_lsu_pkg::*;
(
 input logic i_clk,
 input logic i_reset_n,

 input logic               i_ex0_phy_rd_valid,
 input scariv_pkg::rnid_t  i_ex0_phy_rnid,
 input scariv_pkg::reg_t   i_ex0_phy_type,

 output logic              o_ex1_phy_valid,
 output scariv_pkg::alen_t o_ex1_phy_data,

 input logic [scariv_conf_pkg::STQ_SIZE-1: 0]          i_ex0_stq_valid,
 output logic [$clog2(scariv_conf_pkg::STQ_SIZE)-1: 0] o_ex1_stq_ptr,

 // Store Data Read Interface
 regread_if.master   int_rs2_regread,
 regread_if.master   fp_rs2_regread
 );

logic [$clog2(scariv_conf_pkg::STQ_SIZE)-1: 0] w_ex0_stq_ptr;
bit_encoder #(.WIDTH(scariv_conf_pkg::STQ_SIZE)) u_encoder_ptr (.i_in(i_ex0_stq_valid), .o_out(w_ex0_stq_ptr));

// -----------------------
// Physical Register Read
// -----------------------
assign int_rs2_regread.valid = i_ex0_phy_rd_valid & (i_ex0_phy_type == scariv_pkg::GPR);
assign int_rs2_regread.rnid  = i_ex0_phy_rnid;

assign fp_rs2_regread.valid = i_ex0_phy_rd_valid & (i_ex0_phy_type == scariv_pkg::FPR);
assign fp_rs2_regread.rnid  = i_ex0_phy_rnid;

scariv_pkg::reg_t r_reg_type;
always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    o_ex1_phy_valid <= 1'b0;
  end else begin
    o_ex1_phy_valid <= i_ex0_phy_rd_valid;

    o_ex1_stq_ptr   <= w_ex0_stq_ptr;
    r_reg_type <= i_ex0_phy_type;
  end
end
assign o_ex1_phy_data = r_reg_type == scariv_pkg::GPR ? int_rs2_regread.data : fp_rs2_regread.data;

endmodule // scariv_stq_rs2_pipe
