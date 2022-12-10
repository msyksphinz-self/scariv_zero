module scariv_disp_merge
  import scariv_pkg::*;
(
 disp_if.slave  i_int_disp,
 disp_if.slave  i_fp_disp,
 disp_if.master o_disp
 );

assign o_disp.valid            = i_int_disp.valid & i_fp_disp.valid;
assign o_disp.pc_addr          = i_int_disp.pc_addr;
assign o_disp.tlb_except_valid = i_int_disp.tlb_except_valid;
assign o_disp.tlb_except_cause = i_int_disp.tlb_except_cause;
assign o_disp.tlb_except_tval  = i_int_disp.tlb_except_tval;
assign o_disp.cmt_id           = i_int_disp.cmt_id;
assign o_disp.resource_cnt     = i_int_disp.resource_cnt;
generate for (genvar d_idx = 0; d_idx < scariv_conf_pkg::DISP_SIZE; d_idx++) begin : disp_loop
  assign o_disp.inst[d_idx]    = merge_disp_if (i_int_disp.inst[d_idx], i_fp_disp.inst[d_idx]);
end
endgenerate
assign o_disp.is_br_included   = i_int_disp.is_br_included;
assign o_disp.sim_int_inserted = i_int_disp.sim_int_inserted;

assign i_int_disp.ready = o_disp.ready;
assign i_fp_disp.ready  = o_disp.ready;

endmodule // scariv_disp_merge
