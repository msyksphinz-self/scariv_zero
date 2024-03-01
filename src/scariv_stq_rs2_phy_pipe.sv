module scariv_stq_rs2_phy_pipe
  import scariv_lsu_pkg::*;
(
 input logic i_clk,

 input logic               i_ex0_phy_rd_valid,
 input scariv_pkg::reg_t   i_ex0_phy_type,
 input scariv_pkg::rnid_t  i_ex0_phy_rnid,
 output scariv_pkg::alen_t o_ex1_phy_data,

 // Store Data Read Interface
 regread_if.master   int_rs2_regread,
 regread_if.master   fp_rs2_regread
 );

// -----------------------
// Physical Register Read
// -----------------------
assign int_rs2_regread.valid = i_ex0_phy_rd_valid & (i_ex0_phy_type == scariv_pkg::GPR);
assign int_rs2_regread.rnid  = i_ex0_phy_rnid;

assign fp_rs2_regread.valid = i_ex0_phy_rd_valid & (i_ex0_phy_type == scariv_pkg::FPR);
assign fp_rs2_regread.rnid  = i_ex0_phy_rnid;

scariv_pkg::reg_t r_reg_type;
always_ff @ (posedge i_clk) begin
  r_reg_type <= i_ex0_phy_type;
end
assign o_ex1_phy_data = r_reg_type == scariv_pkg::GPR ? int_rs2_regread.data : fp_rs2_regread.data;

endmodule // scariv_stq_rs2_pipe
