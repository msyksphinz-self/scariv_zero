module select_early_wr_bus
  (
   input [msrh_pkg::RNID_W-1:0] i_entry_rnid,
   input msrh_pkg::reg_t        i_entry_type,
   input msrh_pkg::early_wr_t   i_early_wr[msrh_pkg::REL_BUS_SIZE],

   output logic                 o_valid
   );

logic [msrh_pkg::REL_BUS_SIZE-1:0] w_rel_hit;

msrh_pkg::early_wr_t alu_idx0, alu_idx1;
assign alu_idx0 = i_early_wr[0];
assign alu_idx1 = i_early_wr[1];


generate for (genvar r_idx = 0; r_idx < msrh_pkg::REL_BUS_SIZE; r_idx++) begin : early_wr_loop
  assign w_rel_hit[r_idx] = i_early_wr[r_idx].valid &&
                            (i_entry_rnid == i_early_wr[r_idx].rd_rnid) &&
                            (i_entry_type == i_early_wr[r_idx].rd_type);
end
endgenerate

assign o_valid = |w_rel_hit;

endmodule // select_early_wr_bus
