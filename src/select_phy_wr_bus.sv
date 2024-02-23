module select_phy_wr_bus
  #(parameter BUS_SIZE = scariv_pkg::TGT_BUS_SIZE)
(
   input scariv_pkg::rnid_t i_entry_rnid,
   input scariv_pkg::reg_t  i_entry_type,
   phy_wr_if.slave          phy_wr_if[BUS_SIZE],

   output logic                 o_valid
   );

logic [BUS_SIZE-1:0] w_hit;

generate for (genvar r_idx = 0; r_idx < BUS_SIZE; r_idx++) begin : phy_wr_loop
  assign w_hit[r_idx] = phy_wr_if[r_idx].valid &&
                        (i_entry_rnid == phy_wr_if[r_idx].rd_rnid) &&
                        (i_entry_type == phy_wr_if[r_idx].rd_type);
end endgenerate

assign o_valid = |w_hit;

endmodule // select_phy_wr_bus
