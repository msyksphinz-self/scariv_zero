module select_phy_wr_data
  (
   input msrh_pkg::rnid_t i_entry_rnid,
   input msrh_pkg::reg_t        i_entry_type,
   input msrh_pkg::phy_wr_t     i_phy_wr[msrh_pkg::TGT_BUS_SIZE],

   output logic                 o_valid,
   output riscv_pkg::xlen_t o_data
   );

logic [msrh_pkg::TGT_BUS_SIZE-1:0] w_hit;
riscv_pkg::xlen_t     w_data[msrh_pkg::TGT_BUS_SIZE];

generate for (genvar r_idx = 0; r_idx < msrh_pkg::TGT_BUS_SIZE; r_idx++) begin : phy_wr_loop
  assign w_hit[r_idx] = i_phy_wr[r_idx].valid &&
                        ((i_phy_wr[r_idx].rd_type == msrh_pkg::GPR) ? (i_phy_wr[r_idx].rd_rnid != 'h0) : 1'b1) &
                        (i_entry_rnid == i_phy_wr[r_idx].rd_rnid) &&
                        (i_entry_type == i_phy_wr[r_idx].rd_type);
  assign w_data[r_idx] = i_phy_wr[r_idx].rd_data;
end
endgenerate

assign o_valid = |w_hit;
bit_oh_or #(.T(riscv_pkg::xlen_t), .WORDS(msrh_pkg::TGT_BUS_SIZE))
u_data_select(.i_oh(w_hit), .i_data(w_data), .o_selected(o_data));

endmodule // select_phy_wr_data
