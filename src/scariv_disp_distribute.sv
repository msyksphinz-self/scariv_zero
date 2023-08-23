// ------------------------------------------------------------------------
// NAME : scariv_disp_distribute
// TYPE : module
// ------------------------------------------------------------------------
// Dispatch Distributer
// ------------------------------------------------------------------------
// Broadcast Distpach information to 2-outputs
// Ready is ANDed
// ------------------------------------------------------------------------

module scariv_disp_distribute
  import scariv_pkg::*;
(
 scariv_front_if.slave  i_disp,
 scariv_front_if.master o_disp[2]
 );

generate for (genvar p_idx = 0; p_idx < 2; p_idx++) begin : port_loop
  assign o_disp[p_idx].valid            = i_disp.valid;
  assign o_disp[p_idx].payload.pc_addr          = i_disp.payload.pc_addr;
  assign o_disp[p_idx].payload.tlb_except_valid = i_disp.payload.tlb_except_valid;
  assign o_disp[p_idx].payload.tlb_except_cause = i_disp.payload.tlb_except_cause;
  assign o_disp[p_idx].payload.tlb_except_tval  = i_disp.payload.tlb_except_tval;
  assign o_disp[p_idx].payload.cmt_id           = i_disp.payload.cmt_id;
  assign o_disp[p_idx].payload.resource_cnt     = i_disp.payload.resource_cnt;
  assign o_disp[p_idx].payload.is_br_included   = i_disp.payload.is_br_included;
  assign o_disp[p_idx].payload.int_inserted = i_disp.payload.int_inserted;

  for (genvar d_idx = 0; d_idx < scariv_conf_pkg::DISP_SIZE; d_idx++) begin : disp_loop
    assign o_disp[p_idx].payload.inst[d_idx]    = i_disp.payload.inst[d_idx];
  end

end // block: port_loop
endgenerate

assign i_disp.ready = o_disp[0].ready & o_disp[1].ready;

endmodule // scariv_disp_distribute
