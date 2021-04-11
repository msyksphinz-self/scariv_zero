module select_mispred_bus
  (
   input [msrh_pkg::RNID_W-1:0] i_entry_rnid,
   input msrh_pkg::reg_t        i_entry_type,
   input msrh_pkg::mispred_t    i_mispred[msrh_conf_pkg::LSU_INST_NUM],

   output logic                 o_mispred
   );

logic [msrh_conf_pkg::LSU_INST_NUM-1: 0] w_mispred_hit;

generate for (genvar r_idx = 0; r_idx < msrh_conf_pkg::LSU_INST_NUM; r_idx++) begin : mispred_loop
  assign w_mispred_hit[r_idx] = i_mispred[r_idx].mis_valid &&
                                (i_entry_rnid == i_mispred[r_idx].rd_rnid) &&
                                (i_entry_type == i_mispred[r_idx].rd_type);
end
endgenerate

assign o_mispred = |w_mispred_hit;

endmodule // select_mispred_bus
