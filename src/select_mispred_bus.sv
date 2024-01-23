module select_mispred_bus
  (
   input scariv_pkg::rnid_t i_entry_rnid,
   input scariv_pkg::reg_t        i_entry_type,
   lsu_mispred_if.slave    i_mispred[scariv_conf_pkg::LSU_INST_NUM],

   output logic                 o_mispred
   );

logic [scariv_conf_pkg::LSU_INST_NUM-1: 0] w_mispred_hit;

generate for (genvar r_idx = 0; r_idx < scariv_conf_pkg::LSU_INST_NUM; r_idx++) begin : mispred_loop
  assign w_mispred_hit[r_idx] = i_mispred[r_idx].mis_valid &&
                                (i_entry_rnid == i_mispred[r_idx].rd_rnid) &&
                                (i_entry_type == i_mispred[r_idx].rd_type);
end
endgenerate

assign o_mispred = |w_mispred_hit;

endmodule // select_mispred_bus
