// ------------------------------------------------------------------------
// NAME : scariv_disp_merge
// TYPE : module
// ------------------------------------------------------------------------
// Dispatch Merge
// ------------------------------------------------------------------------
// Merge two dispatch information into single interface
// ------------------------------------------------------------------------

module scariv_disp_merge
  import scariv_pkg::*;
(
 scariv_front_if.slave  i_int_disp,
 scariv_front_if.slave  i_fp_disp,
 scariv_front_if.master o_disp
 );

assign o_disp.valid            = i_int_disp.valid & i_fp_disp.valid;
assign o_disp.payload.pc_addr          = i_int_disp.payload.pc_addr;
`ifdef SIMULATION
assign o_disp.payload.pc_addr_debug    = i_int_disp.payload.pc_addr_debug;
`endif // SIMULATION
assign o_disp.payload.tlb_except_valid = i_int_disp.payload.tlb_except_valid;
assign o_disp.payload.tlb_except_cause = i_int_disp.payload.tlb_except_cause;
assign o_disp.payload.tlb_except_tval  = i_int_disp.payload.tlb_except_tval;
assign o_disp.payload.cmt_id           = i_int_disp.payload.cmt_id;
assign o_disp.payload.resource_cnt     = i_int_disp.payload.resource_cnt;
generate for (genvar d_idx = 0; d_idx < scariv_conf_pkg::DISP_SIZE; d_idx++) begin : disp_loop
  assign o_disp.payload.inst[d_idx]    = merge_scariv_front_if (i_int_disp.payload.inst[d_idx], i_fp_disp.payload.inst[d_idx]);
end
endgenerate
assign o_disp.payload.is_br_included   = i_int_disp.payload.is_br_included;
assign o_disp.payload.int_inserted = i_int_disp.payload.int_inserted;

assign i_int_disp.ready = o_disp.ready;
assign i_fp_disp.ready  = o_disp.ready;

endmodule // scariv_disp_merge
