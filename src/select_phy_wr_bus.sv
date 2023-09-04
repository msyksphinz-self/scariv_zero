module select_phy_wr_bus
  #(parameter REG_TYPE = scariv_pkg::GPR,
    localparam REN_UPD_NUM = REG_TYPE == scariv_pkg::GPR ? scariv_pkg::TGT_XPR_BUS_SIZE : scariv_pkg::TGT_FPR_BUS_SIZE
    )
(
   input scariv_pkg::rnid_t   i_entry_rnid,
   input scariv_pkg::reg_t    i_entry_type,
   input scariv_pkg::phy_wr_t i_phy_wr[REN_UPD_NUM],

   output logic                o_valid
   );

logic [REN_UPD_NUM-1:0] w_hit;

scariv_pkg::phy_wr_t alu_idx0, alu_idx1;
assign alu_idx0 = i_phy_wr[0];
assign alu_idx1 = i_phy_wr[1];


generate for (genvar r_idx = 0; r_idx < REN_UPD_NUM; r_idx++) begin : phy_wr_loop
  assign w_hit[r_idx] = i_phy_wr[r_idx].valid &&
                        (i_entry_rnid == i_phy_wr[r_idx].rd_rnid) &&
                        (i_entry_type == i_phy_wr[r_idx].rd_type);
end endgenerate

assign o_valid = |w_hit;

endmodule // select_phy_wr_bus
