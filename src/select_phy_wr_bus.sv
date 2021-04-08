module select_phy_wr_bus
  (
   input [msrh_pkg::RNID_W-1:0] i_entry_rnid,
   input msrh_pkg::reg_t        i_entry_type,
   input msrh_pkg::phy_wr_t     i_phy_wr[msrh_pkg::TGT_BUS_SIZE],

   output logic                 o_valid
   );

logic [msrh_pkg::TGT_BUS_SIZE-1:0] w_hit;

msrh_pkg::phy_wr_t alu_idx0, alu_idx1;
assign alu_idx0 = i_phy_wr[0];
assign alu_idx1 = i_phy_wr[1];


generate for (genvar r_idx = 0; r_idx < msrh_pkg::TGT_BUS_SIZE; r_idx++) begin : phy_wr_loop
  assign w_hit[r_idx] = i_phy_wr[r_idx].valid &&
                        (i_entry_rnid == i_phy_wr[r_idx].rd_rnid) &&
                        (i_entry_type == i_phy_wr[r_idx].rd_type);
end
endgenerate

assign o_valid = |w_hit;

endmodule // select_phy_wr_bus
