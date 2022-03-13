module msrh_disp_distribute
  import msrh_pkg::*;
(
 disp_if.slave  i_disp,
 disp_if.master o_disp[2]
 );

generate for (genvar p_idx = 0; p_idx < 2; p_idx++) begin : port_loop
  assign o_disp[p_idx].valid            = i_disp.valid;
  assign o_disp[p_idx].pc_addr          = i_disp.pc_addr;
  assign o_disp[p_idx].tlb_except_valid = i_disp.tlb_except_valid;
  assign o_disp[p_idx].tlb_except_cause = i_disp.tlb_except_cause;
  assign o_disp[p_idx].tlb_except_tval  = i_disp.tlb_except_tval;
  assign o_disp[p_idx].cmt_id           = i_disp.cmt_id;
  assign o_disp[p_idx].resource_cnt     = i_disp.resource_cnt;
  assign o_disp[p_idx].is_br_included   = i_disp.is_br_included;

  for (genvar d_idx = 0; d_idx < msrh_conf_pkg::DISP_SIZE; d_idx++) begin : disp_loop
    assign o_disp[p_idx].inst[d_idx]    = i_disp.inst[d_idx];
  end

end // block: port_loop
endgenerate

assign i_disp.ready = o_disp[0].ready & o_disp[1].ready;

endmodule // msrh_disp_distribute
