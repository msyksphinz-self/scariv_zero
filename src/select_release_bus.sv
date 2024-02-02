module select_early_wr_bus
  (
   input scariv_pkg::rnid_t i_entry_rnid,
   input scariv_pkg::reg_t        i_entry_type,
   early_wr_if.slave   early_wr_if[scariv_pkg::REL_BUS_SIZE],

   output logic                 o_valid,
   output logic                 o_may_mispred
   );

logic [scariv_pkg::REL_BUS_SIZE-1:0] w_rel_hit;
logic [scariv_pkg::REL_BUS_SIZE-1:0] w_rel_hit_may_mispred;

scariv_pkg::early_wr_t alu_idx0, alu_idx1;
assign alu_idx0 = early_wr_if[0];
assign alu_idx1 = early_wr_if[1];


generate for (genvar r_idx = 0; r_idx < scariv_pkg::REL_BUS_SIZE; r_idx++) begin : early_wr_loop
  assign w_rel_hit[r_idx] = early_wr_if[r_idx].valid &&
                            ((early_wr_if[r_idx].rd_type == scariv_pkg::GPR) ? (early_wr_if[r_idx].rd_rnid != 'h0) : 1'b1) &
                            (i_entry_rnid == early_wr_if[r_idx].rd_rnid) &&
                            (i_entry_type == early_wr_if[r_idx].rd_type);
  assign w_rel_hit_may_mispred[r_idx] = w_rel_hit[r_idx] & early_wr_if[r_idx].may_mispred;
end
endgenerate

assign o_valid = |w_rel_hit;
assign o_may_mispred = |w_rel_hit_may_mispred;

endmodule // select_early_wr_bus
