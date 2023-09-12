module select_early_wr_bus_oh
  (
   input scariv_pkg::rnid_t     i_entry_rnid,
   input scariv_pkg::reg_t      i_entry_type,
   input scariv_pkg::early_wr_t i_early_wr[scariv_pkg::REL_BUS_SIZE],

   output logic                                         o_valid,
   output logic [$clog2(scariv_pkg::REL_BUS_SIZE)-1: 0] o_hit_index,
   output logic [scariv_pkg::REL_BUS_SIZE-1: 0]         o_may_mispred
   );


logic [scariv_pkg::REL_BUS_SIZE-1: 0]                   w_hit_valid;
logic [scariv_pkg::REL_BUS_SIZE-1: 0]                   w_may_mispred;

generate for (genvar r_idx = 0; r_idx < scariv_pkg::REL_BUS_SIZE; r_idx++) begin : early_wr_loop
  assign w_hit_valid[r_idx] = i_early_wr[r_idx].valid &&
                              ((i_early_wr[r_idx].rd_type == scariv_pkg::GPR) ? (i_early_wr[r_idx].rd_rnid != 'h0) : 1'b1) &
                              (i_entry_rnid == i_early_wr[r_idx].rd_rnid) &&
                              (i_entry_type == i_early_wr[r_idx].rd_type);
  assign w_may_mispred[r_idx] = w_hit_valid[r_idx] & i_early_wr[r_idx].may_mispred;
end endgenerate

encoder #(.SIZE(scariv_pkg::REL_BUS_SIZE)) u_hit_enc (.i_in(w_hit_valid), .o_out(o_hit_index));
assign o_valid       = |w_hit_valid;
assign o_may_mispred = |w_may_mispred;

endmodule // select_early_wr_bus_oh
