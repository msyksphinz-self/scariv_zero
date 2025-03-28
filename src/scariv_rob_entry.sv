// ------------------------------------------------------------------------
// NAME : scariv_rob_entry
// TYPE : module
// ------------------------------------------------------------------------
// Reorder Buffer Entry
// ------------------------------------------------------------------------
//
// ------------------------------------------------------------------------

module scariv_rob_entry
  import scariv_pkg::*;
  (
   input logic        i_clk,
   input logic        i_reset_n,

   input cmt_id_t     i_cmt_id,

   input logic        i_load_valid,
   input rob_entry_t  i_entry_in,

   done_report_if.slave  done_report_if [CMT_BUS_SIZE],
   flush_report_if.slave flush_report_if [scariv_conf_pkg::LSU_INST_NUM],

   output rob_entry_t o_entry,
   output logic       o_block_all_done,
   input logic        commit_if_finish,

   input logic        i_kill,

   br_upd_if.slave  br_upd_slave_if
   );

rob_entry_t             r_entry;
rob_entry_t             w_entry_next;

scariv_pkg::grp_id_t   w_done_rpt_valid;
scariv_pkg::grp_id_t   w_finished_grp_id;
scariv_pkg::grp_id_t   w_done_rpt_except_valid;
grp_id_t                               w_done_rpt_fflags_update_valid;
scariv_pkg::fflags_t                     w_done_rpt_fflags     [scariv_conf_pkg::DISP_SIZE];
cmt_id_t w_cmt_id;
cmt_id_t w_in_cmt_id;
assign w_cmt_id    = {r_entry.cmt_id_msb,    i_cmt_id[CMT_ENTRY_W-1:0]};
assign w_in_cmt_id = {i_entry_in.cmt_id_msb, i_cmt_id[CMT_ENTRY_W-1:0]};


generate for (genvar d_idx = 0; d_idx < scariv_conf_pkg::DISP_SIZE; d_idx++) begin : grp_id_loop
  logic [CMT_BUS_SIZE-1: 0] w_done_rpt_tmp_valid;
  done_rpt_t                w_done_rpt_payloads[CMT_BUS_SIZE];
  done_rpt_t                w_done_rpt_selected;
  for (genvar c_idx = 0; c_idx < CMT_BUS_SIZE; c_idx++) begin : cmt_loop
    assign w_done_rpt_tmp_valid[c_idx] = done_report_if[c_idx].valid &
                                         done_report_if[c_idx].cmt_id[CMT_ENTRY_W-1:0] == w_cmt_id[CMT_ENTRY_W-1:0] &&
                                         done_report_if[c_idx].grp_id == (1 << d_idx);
    assign w_done_rpt_payloads[c_idx] = done_report_if[c_idx].get_payload();
  end
  assign w_done_rpt_valid[d_idx] = |w_done_rpt_tmp_valid;
  bit_oh_or #(.T(done_rpt_t), .WORDS(CMT_BUS_SIZE))
  sel_done_rpt (.i_oh(w_done_rpt_tmp_valid),
                .i_data(w_done_rpt_payloads),
                .o_selected(w_done_rpt_selected));
  assign w_done_rpt_except_valid[d_idx] = w_done_rpt_selected.except_valid;

  assign w_done_rpt_fflags_update_valid[d_idx] = w_done_rpt_selected.fflags_update_valid;
  assign w_done_rpt_fflags             [d_idx] = w_done_rpt_selected.fflags;
end
endgenerate


// --------------------
// Another Flush Match
// --------------------
grp_id_t w_another_flush_tmp_valid[scariv_conf_pkg::LSU_INST_NUM];
grp_id_t w_another_flush_valid;
grp_id_t w_another_tree_flush_valid;
generate for (genvar l_idx = 0; l_idx < scariv_conf_pkg::LSU_INST_NUM; l_idx++) begin : lsu_loop
  assign w_another_flush_tmp_valid[l_idx] = flush_report_if[l_idx].valid &
                                            (flush_report_if[l_idx].cmt_id[CMT_ENTRY_W-1:0] == w_cmt_id[CMT_ENTRY_W-1:0]) ? flush_report_if[l_idx].grp_id : 'h0;
end
endgenerate


bit_or #(.WIDTH(scariv_conf_pkg::DISP_SIZE), .WORDS(scariv_conf_pkg::LSU_INST_NUM))
another_flush_select (.i_data(w_another_flush_tmp_valid), .o_selected(w_another_flush_valid));

bit_tree_lsb #(.WIDTH(scariv_conf_pkg::DISP_SIZE))
bit_tree_another_flush (.in(w_another_flush_valid), .out(w_another_tree_flush_valid));


// ------------------------------------
// Make dead to following instructions
// ------------------------------------
grp_id_t w_flush_tmp_valid;
grp_id_t w_tree_flush_valid;
assign w_flush_tmp_valid = (w_done_rpt_except_valid & w_done_rpt_valid) << 1;

bit_tree_lsb #(.WIDTH(scariv_conf_pkg::DISP_SIZE))
bit_tree_done_flush (.in(w_flush_tmp_valid), .out(w_tree_flush_valid));


`ifdef SIMULATION
riscv_pkg::xlen_t   r_mstatus[scariv_conf_pkg::DISP_SIZE];
`endif // SIMULATION


always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_entry <= 'h0;
  end else begin
    r_entry <= w_entry_next;

`ifdef SIMULATION
    for (int d_idx = 0; d_idx < scariv_conf_pkg::DISP_SIZE; d_idx++) begin
      if (w_entry_next.done_grp_id[d_idx] & ~r_entry.done_grp_id[d_idx]) begin
        r_mstatus[d_idx] <= `SUBSYSTEM_TOP.u_tile.u_csu.u_scariv_csr.w_mstatus_next;
      end
    end
`endif // SIMULATION
  end
end

assign w_finished_grp_id = (r_entry.done_grp_id | r_entry.dead) & r_entry.grp_id;

always_comb begin
  w_entry_next = r_entry;

  if (i_load_valid) begin
    w_entry_next = i_entry_in;
    if (br_upd_slave_if.update) begin
      for (int d_idx = 0; d_idx < scariv_conf_pkg::DISP_SIZE; d_idx++) begin : disp_loop
        if (is_br_flush_target_wo_itself (w_in_cmt_id, 1 << d_idx, br_upd_slave_if.cmt_id, br_upd_slave_if.grp_id,
                                          br_upd_slave_if.dead, br_upd_slave_if.mispredict)) begin
          w_entry_next.done_grp_id [d_idx] = 1'b1;
          w_entry_next.dead        [d_idx] = 1'b1;
          // w_entry_next.flush_valid [d_idx] = 1'b0;
`ifdef SIMULATION
          w_entry_next.sim_dead_reason[d_idx] = DEAD_BRANCH;
`endif // SIMULATION
        end
        // Resolve the branch dependency
      end
      // if (br_upd_slave_if.cmt_id[CMT_ENTRY_W-1:0] == w_cmt_id[CMT_ENTRY_W-1:0]) begin
      //   w_entry_next.br_upd_info.upd_valid   [encoder_grp_id(br_upd_slave_if.grp_id)] = br_upd_slave_if.taken;
      // end
    end // if (br_upd_slave_if.update)

`ifdef SIMULATION
    for (int d_idx = 0; d_idx < scariv_conf_pkg::DISP_SIZE; d_idx++) begin: life_loop
      w_entry_next.lifetime[d_idx] = 0;
    end
`endif // SIMULATION
  end // if (i_load_valid)

  if (r_entry.valid) begin
    // Condition :
    // all instruction done, or ROB entry dead,
    // So, during killing, allocated new instruction should be killed.
    if (commit_if_finish & o_block_all_done) begin
      w_entry_next.valid = 1'b0;
    end

    w_entry_next.done_grp_id = r_entry.done_grp_id | w_done_rpt_valid;

    for (int d_idx = 0; d_idx < scariv_conf_pkg::DISP_SIZE; d_idx++) begin : disp_loop
      if (w_done_rpt_valid[d_idx]) begin
        if (!r_entry.dead[d_idx]) begin
          w_entry_next.fflags_update_valid [d_idx] = w_done_rpt_fflags_update_valid [d_idx];
          w_entry_next.fflags              [d_idx] = w_done_rpt_fflags              [d_idx];
        end
      end
      if (w_tree_flush_valid[d_idx]) begin
        if (!r_entry.dead[d_idx]) begin
          w_entry_next.dead        [d_idx] = r_entry.grp_id[d_idx];
          // w_entry_next.flush_valid [d_idx] = r_entry.grp_id[d_idx];
`ifdef SIMULATION
          w_entry_next.sim_dead_reason[d_idx] = DEAD_PREVINST;
`endif // SIMULATION
        end
      end
    end

    // Branch condition update
    if (br_upd_slave_if.update) begin
      for (int d_idx = 0; d_idx < scariv_conf_pkg::DISP_SIZE; d_idx++) begin : disp_loop
        if (r_entry.valid & r_entry.grp_id[d_idx] &
            is_br_flush_target_wo_itself (w_cmt_id, 1 << d_idx, br_upd_slave_if.cmt_id, br_upd_slave_if.grp_id,
                                          br_upd_slave_if.dead, br_upd_slave_if.mispredict)) begin
          w_entry_next.done_grp_id [d_idx] = 1'b1;
          w_entry_next.dead        [d_idx] = 1'b1;
`ifdef SIMULATION
          w_entry_next.sim_dead_reason[d_idx] = DEAD_BRANCH;
`endif // SIMULATION
        end
        // Resolve the branch dependency
      end
      // if (br_upd_slave_if.cmt_id[CMT_ENTRY_W-1:0] == w_cmt_id[CMT_ENTRY_W-1:0]) begin
      //   w_entry_next.br_upd_info.upd_valid   [encoder_grp_id(br_upd_slave_if.grp_id)] = br_upd_slave_if.taken;
      // end // if (br_upd_slave_if.cmt_id[CMT_ENTRY_W-1:0] == w_cmt_id[CMT_ENTRY_W-1:0])
// `ifdef SIMULATION
//       if ((br_upd_slave_if.cmt_id[CMT_ENTRY_W-1:0] == w_cmt_id[CMT_ENTRY_W-1:0]) & ~br_upd_slave_if.dead) begin
//         w_entry_next.br_upd_info.sim_ras_index    = br_upd_slave_if.ras_index;
//         w_entry_next.br_upd_info.sim_pred_vaddr   = br_upd_slave_if.pred_vaddr;
//       end
// `endif // SIMULATION
    end // if (br_upd_slave_if.update)

    for (int d_idx = 0; d_idx < scariv_conf_pkg::DISP_SIZE; d_idx++) begin : disp_loop
      if (i_kill) begin
        w_entry_next.dead        [d_idx] = r_entry.grp_id[d_idx];
`ifdef SIMULATION
        // w_entry_next.sim_dead_reason[d_idx] = DEAD_EXT_KILL;
`endif // SIMULATION
      end
    end

`ifdef SIMULATION
    for (int d_idx = 0; d_idx < scariv_conf_pkg::DISP_SIZE; d_idx++) begin: life_loop
      if (r_entry.done_grp_id[d_idx]) begin
        w_entry_next.lifetime[d_idx] = r_entry.lifetime[d_idx] + 1;
      end
    end
`endif // SIMULATION
  end
end // always_comb


assign o_entry = r_entry;
assign o_block_all_done = r_entry.valid & (w_finished_grp_id == r_entry.grp_id);

endmodule // scariv_rob_entry
