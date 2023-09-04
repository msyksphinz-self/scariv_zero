module select_phy_wr_data
  #(parameter REG_TYPE = scariv_pkg::GPR,
    localparam REN_UPD_NUM = REG_TYPE == scariv_pkg::GPR ? scariv_pkg::TGT_XPR_BUS_SIZE : scariv_pkg::TGT_FPR_BUS_SIZE
    )
  (
   input scariv_pkg::rnid_t   i_entry_rnid,
   input scariv_pkg::reg_t    i_entry_type,
   input scariv_pkg::phy_wr_t i_phy_wr[REN_UPD_NUM],

   output logic             o_valid,
   output scariv_pkg::alen_t  o_data
   );

logic [REN_UPD_NUM-1:0] w_hit;
scariv_pkg::alen_t     w_data[REN_UPD_NUM];

generate for (genvar r_idx = 0; r_idx < REN_UPD_NUM; r_idx++) begin : phy_wr_loop
  assign w_hit[r_idx] = i_phy_wr[r_idx].valid &&
                        ((i_phy_wr[r_idx].rd_type == scariv_pkg::GPR) ? (i_phy_wr[r_idx].rd_rnid != 'h0) : 1'b1) &
                        (i_entry_rnid == i_phy_wr[r_idx].rd_rnid) &&
                        (i_entry_type == i_phy_wr[r_idx].rd_type);
  assign w_data[r_idx] = i_phy_wr[r_idx].rd_data;
end
endgenerate

assign o_valid = |w_hit;
bit_oh_or #(.T(scariv_pkg::alen_t), .WORDS(REN_UPD_NUM))
u_data_select(.i_oh(w_hit), .i_data(w_data), .o_selected(o_data));

endmodule // select_phy_wr_data
