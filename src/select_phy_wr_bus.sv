module select_phy_wr_bus
  (
   input scariv_pkg::rnid_t i_entry_rnid,
   input scariv_pkg::reg_t        i_entry_type,
   phy_wr_if.slave     phy_wr_if[scariv_pkg::TGT_BUS_SIZE],

   output logic                 o_valid
   );

logic [scariv_pkg::TGT_BUS_SIZE-1:0] w_hit;

scariv_pkg::phy_wr_t alu_idx0, alu_idx1;
assign alu_idx0 = phy_wr_if[0];
assign alu_idx1 = phy_wr_if[1];


generate for (genvar r_idx = 0; r_idx < scariv_pkg::TGT_BUS_SIZE; r_idx++) begin : phy_wr_loop
  assign w_hit[r_idx] = phy_wr_if[r_idx].valid &&
                        (i_entry_rnid == phy_wr_if[r_idx].rd_rnid) &&
                        (i_entry_type == phy_wr_if[r_idx].rd_type);
end
endgenerate

assign o_valid = |w_hit;

endmodule // select_phy_wr_bus
