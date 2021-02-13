module select_release_bus
  (
   input [msrh_pkg::RNID_W-1:0] i_entry_rnid,
   input msrh_pkg::reg_t     i_entry_type,
   input msrh_pkg::release_t release_in[msrh_pkg::REL_BUS_SIZE],

   output logic                 o_valid
   );

logic [msrh_pkg::REL_BUS_SIZE-1:0] w_rel_hit;

msrh_pkg::release_t alu_idx0, alu_idx1;
assign alu_idx0 = release_in[0];
assign alu_idx1 = release_in[1];


generate for (genvar r_idx = 0; r_idx < msrh_pkg::REL_BUS_SIZE; r_idx++) begin : release_loop
  assign w_rel_hit[r_idx] = release_in[r_idx].valid &&
                            (i_entry_rnid == release_in[r_idx].rd_rnid) &&
                            (i_entry_type == release_in[r_idx].rd_type);
end
endgenerate

assign o_valid = |w_rel_hit;

endmodule // select_release_bus
