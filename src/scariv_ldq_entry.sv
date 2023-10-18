// ------------------------------------------------------------------------
// NAME : scariv_ldq_entry
// TYPE : module
// ------------------------------------------------------------------------
// LSU Load Queue Entry
// ------------------------------------------------------------------------
//
// ------------------------------------------------------------------------

module scariv_ldq_entry
  import scariv_lsu_pkg::*;
#(parameter entry_index = 0)
(
 input logic                                     i_clk,
 input logic                                     i_reset_n,

 // ROB notification interface
 rob_info_if.slave                               rob_info_if,

 input logic                                     i_disp_load,
 input scariv_pkg::cmt_id_t                      i_disp_cmt_id,
 input scariv_pkg::grp_id_t                      i_disp_grp_id,
 input                                           scariv_pkg::disp_t i_disp,
 input logic [scariv_conf_pkg::LSU_INST_NUM-1: 0]  i_disp_pipe_sel_oh,

 output                                          ldq_entry_t o_entry,
 output logic                                    o_entry_ready,
 output logic [scariv_conf_pkg::LSU_INST_NUM-1: 0] o_ex2_ldq_entries_recv,

 input logic                                     i_entry_picked,

  // Updates from LSU Pipeline EX1 stage
  input logic                                    i_ex1_q_valid,
  input ex1_q_update_t                           i_ex1_q_updates,

  input logic                                    i_ex2_q_valid,
  input ex2_q_update_t                           i_ex2_q_updates,

 input                                           missu_resolve_t i_missu_resolve,
 input logic                                     i_missu_is_full,
 // Commit notification
 input                                           scariv_pkg::commit_blk_t i_commit,
 br_upd_if.slave                                 br_upd_if,

 input logic                                     i_st_buffer_empty,
 input logic                                     i_st_requester_empty,

 input stq_resolve_t                             i_stq_rs2_resolve,

 input logic                                     i_ldq_outptr_valid,
 output logic                                    o_entry_finish

 // done_if.slave   ex3_done_if
 );

logic                                            w_entry_ready;

ldq_entry_t                                      r_entry;
/* verilator lint_off UNOPTFLAT */
ldq_entry_t                                      w_entry_next;
logic                                            w_entry_flush;
logic                                            w_commit_flush;
logic                                            w_br_flush;
logic                                            w_load_br_flush;
logic                                            w_load_commit_flush;
logic                                            w_load_flush;
logic                                            w_dead_state_clear;
logic                                            w_entry_commit;
logic                                            w_oldest_ready;

logic                                            w_missu_is_full;
logic                                            w_missu_is_assigned;
logic                                            w_missu_resolve_match;
logic                                            w_missu_evict_is_hazard;

logic [scariv_conf_pkg::LSU_INST_NUM-1: 0]         r_ex2_ldq_entries_recv;
logic [scariv_conf_pkg::LSU_INST_NUM-1: 0]         w_ex2_ldq_entries_recv_next;

scariv_pkg::rnid_t                                 w_rs_rnid[2];
scariv_pkg::reg_t                                  w_rs_type[2];
logic [ 1: 0]                                    w_rs_rel_hit;
logic [ 1: 0]                                    w_rs_may_mispred;
logic [ 1: 0]                                    w_rs_phy_hit;
logic [ 1: 0]                                    w_rs_mispredicted;

assign o_entry = r_entry;
assign o_ex2_ldq_entries_recv = r_ex2_ldq_entries_recv;

assign w_commit_flush = scariv_pkg::is_flushed_commit(i_commit) & r_entry.is_valid;
assign w_br_flush     = scariv_pkg::is_br_flush_target(r_entry.inst.cmt_id, r_entry.inst.grp_id, br_upd_if.cmt_id, br_upd_if.grp_id,
                                                     br_upd_if.dead, br_upd_if.mispredict) & br_upd_if.update & r_entry.is_valid;
assign w_entry_flush  = w_commit_flush | w_br_flush;


assign w_load_commit_flush = scariv_pkg::is_flushed_commit(i_commit);
assign w_load_br_flush = scariv_pkg::is_br_flush_target(i_disp_cmt_id, i_disp_grp_id, br_upd_if.cmt_id, br_upd_if.grp_id,
                                                      br_upd_if.dead, br_upd_if.mispredict) & br_upd_if.update;
assign w_load_flush = w_load_commit_flush | w_load_br_flush;

assign w_dead_state_clear = i_commit.commit & (i_commit.cmt_id == r_entry.inst.cmt_id);

assign o_entry_finish = r_entry.is_valid & (r_entry.is_committed | r_entry.dead) & i_ldq_outptr_valid;

assign w_entry_commit = i_commit.commit & (i_commit.cmt_id == r_entry.inst.cmt_id);

// assign o_entry_ready = (r_entry.state == LDQ_ISSUE_WAIT) & !w_entry_flush &
//                        all_operand_ready(r_entry);
//
// assign w_oldest_ready = (rob_info_if.cmt_id == r_entry.inst.cmt_id) &
//                         ((rob_info_if.done_grp_id & r_entry.inst.grp_id-1) == r_entry.inst.grp_id-1);


always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_entry.is_valid <= 1'b0;
    // r_entry.state <= LDQ_INIT;
    // r_entry.missu_haz_index_oh <= 'h0;

    r_ex2_ldq_entries_recv <= 'h0;
  end else begin
    r_entry <= w_entry_next;
    r_ex2_ldq_entries_recv <= w_ex2_ldq_entries_recv_next;
  end
end

always_comb begin

  w_entry_next = r_entry;

//  for (int rs_idx = 0; rs_idx < 2; rs_idx++) begin
//    w_entry_next.inst.rd_regs[rs_idx].ready = r_entry.inst.rd_regs[rs_idx].ready | w_rs_phy_hit[rs_idx];
//    w_entry_next.inst.rd_regs[rs_idx].predict_ready = w_rs_rel_hit[rs_idx] & w_rs_may_mispred[rs_idx];
//  end

  w_ex2_ldq_entries_recv_next = r_ex2_ldq_entries_recv;

  if (!r_entry.is_valid) begin
    if (i_disp_load) begin
        w_entry_next = assign_ldq_disp(i_disp, i_disp_cmt_id, i_disp_grp_id,
                                       1 << (entry_index % scariv_conf_pkg::LSU_INST_NUM));
        if (w_load_flush) begin
          w_entry_next.dead = 1'b1;
        end
      end
  end else if (r_entry.is_committed | r_entry.dead) begin
    if (i_ldq_outptr_valid) begin
      w_entry_next.is_valid = 1'b0;
    end
  end else begin
    w_entry_next.inst.oldest_valid = r_entry.inst.oldest_valid | w_oldest_ready;

    if (w_entry_flush) begin
      w_entry_next.dead = 1'b1;
    end else if (~r_entry.paddr_valid & i_ex1_q_valid & (i_ex1_q_updates.hazard_typ == EX1_HAZ_NONE)) begin
      w_entry_next.addr        = i_ex1_q_updates.paddr;
      w_entry_next.paddr_valid = !i_ex1_q_updates.tlb_except_valid;
      w_entry_next.size        = i_ex1_q_updates.size;
    end else if (i_ex2_q_valid & r_entry.paddr_valid & (i_ex2_q_updates.hazard_typ == EX2_HAZ_NONE)) begin
      w_entry_next.is_get_data = 1'b1;
    end

    if (w_entry_commit) begin
      w_entry_next.is_committed = 1'b1;
    end

  end

//   case (r_entry.state)
//     LDQ_INIT :
//       if (w_entry_flush & r_entry.is_valid) begin
//         w_entry_next.state    = LDQ_WAIT_ENTRY_CLR;
//         // w_entry_next.is_valid = 1'b0;
//         // w_entry_next.inst.cmt_id = 'h0;
//         // w_entry_next.inst.grp_id = 'h0;
//       end else if (i_disp_load) begin
//         w_entry_next = assign_ldq_disp(i_disp, i_disp_cmt_id, i_disp_grp_id, 1 << (entry_index % scariv_conf_pkg::LSU_INST_NUM));
//         for (int rs_idx = 0; rs_idx < 2; rs_idx++) begin
//           w_entry_next.inst.rd_regs[rs_idx].valid         = i_disp.rd_regs[rs_idx].valid;
//           w_entry_next.inst.rd_regs[rs_idx].typ           = i_disp.rd_regs[rs_idx].typ;
//           w_entry_next.inst.rd_regs[rs_idx].regidx        = i_disp.rd_regs[rs_idx].regidx;
//           w_entry_next.inst.rd_regs[rs_idx].rnid          = i_disp.rd_regs[rs_idx].rnid;
//           w_entry_next.inst.rd_regs[rs_idx].ready         = i_disp.rd_regs[rs_idx].ready | w_rs_rel_hit[rs_idx] & ~w_rs_may_mispred[rs_idx] | w_rs_phy_hit[rs_idx];
//           w_entry_next.inst.rd_regs[rs_idx].predict_ready = w_rs_rel_hit[rs_idx] & w_rs_may_mispred[rs_idx];
//         end
//
//         for (int rs_idx = 2; rs_idx < 3; rs_idx++) begin
//           w_entry_next.inst.rd_regs[rs_idx].valid = 1'b0;
//         end
//
//         w_entry_next.inst.wr_reg.valid  = i_disp.wr_reg.valid;
//         w_entry_next.inst.wr_reg.typ    = i_disp.wr_reg.typ;
//         w_entry_next.inst.wr_reg.regidx = i_disp.wr_reg.regidx;
//         w_entry_next.inst.wr_reg.rnid   = i_disp.wr_reg.rnid;
//
//         if (w_load_flush) begin
//           w_entry_next.state    = LDQ_WAIT_ENTRY_CLR;
//         end else begin
//           w_entry_next.state    = LDQ_EX3_DONE;
//         end
//       end
//     LDQ_ISSUE_WAIT : begin
//       if (w_entry_flush) begin
//         w_entry_next.state = LDQ_WAIT_ENTRY_CLR;
//       end else if (r_entry.inst.rd_regs[0].predict_ready & w_rs_mispredicted[0] |
//                    r_entry.inst.rd_regs[1].predict_ready & w_rs_mispredicted[1]) begin
//           w_entry_next.state = LDQ_ISSUE_WAIT;
//           w_entry_next.inst.rd_regs[0].predict_ready = 1'b0;
//           w_entry_next.inst.rd_regs[1].predict_ready = 1'b0;
//       end else if (o_entry_ready & i_entry_picked) begin
//         w_entry_next.state = LDQ_ISSUED;
//       end
//     end
//     // LDQ_ISSUED : begin
//     //   if (w_entry_flush) begin
//     //     w_entry_next.state = LDQ_WAIT_ENTRY_CLR;
//     //   end else begin
//     //     if (w_entry_next.is_valid & i_ex1_q_valid) begin
//     //       w_entry_next.state           = i_ex1_q_updates.hazard_typ == EX1_HAZ_TLB_MISS  ? LDQ_TLB_HAZ :
//     //                                      i_ex1_q_updates.hazard_typ == EX1_HAZ_UC_ACCESS ? LDQ_WAIT_OLDEST :
//     //                                      LDQ_EX2_RUN;
//     //       w_entry_next.except_valid    = i_ex1_q_updates.tlb_except_valid;
//     //       w_entry_next.except_type     = i_ex1_q_updates.tlb_except_type;
//     //       w_entry_next.addr            = i_ex1_q_updates.tlb_except_valid ? i_ex1_q_updates.vaddr :
//     //                                      i_ex1_q_updates.paddr;
//     //       // w_entry_next.pipe_sel_idx_oh = i_ex1_q_updates.pipe_sel_idx_oh;
//     //       // w_entry_next.inst            = i_ex1_q_updates.inst;
//     //       w_entry_next.size            = i_ex1_q_updates.size;
//     //
//     //       for (int p_idx = 0; p_idx < scariv_conf_pkg::LSU_INST_NUM; p_idx++) begin : pipe_loop
//     //         w_ex2_ldq_entries_recv_next[p_idx] =  i_ex1_q_valid &
//     //                                               (i_ex1_q_updates.hazard_typ == EX1_HAZ_NONE) &
//     //                                               r_entry.pipe_sel_idx_oh[p_idx];
//     //       end
//     //     end // if (i_ex1_q_valid)
//     //   end // else: !if(w_entry_flush)
//     // end // case: LDQ_ISSUED
//     // LDQ_TLB_HAZ : begin
//     //   if (w_entry_flush) begin
//     //     w_entry_next.state = LDQ_WAIT_ENTRY_CLR;
//     //   end else if (|i_tlb_resolve) begin
//     //     w_entry_next.state = LDQ_ISSUE_WAIT;
//     //   end
//     // end
//     // LDQ_EX2_RUN : begin
//     //   if (w_entry_flush) begin
//     //     w_entry_next.state = LDQ_WAIT_ENTRY_CLR;
//     //   end else if (i_ex2_q_valid) begin
//     //     w_entry_next.state = i_ex2_q_updates.hazard_typ == EX2_HAZ_L1D_CONFLICT   ? LDQ_ISSUE_WAIT      :
//     //                          i_ex2_q_updates.hazard_typ == EX2_HAZ_STQ_NONFWD_HAZ ? LDQ_NONFWD_HAZ_WAIT :
//     //                          i_ex2_q_updates.hazard_typ == EX2_HAZ_RMW_ORDER_HAZ  ? LDQ_WAIT_OLDEST     :
//     //                          w_missu_resolve_match   ? LDQ_ISSUE_WAIT :
//     //                          w_missu_is_full         ? LDQ_MISSU_FULL :
//     //                          w_missu_evict_is_hazard ? LDQ_MISSU_EVICT_HAZ :
//     //                          w_missu_is_assigned     ? LDQ_MISSU_WAIT      :
//     //                          LDQ_EX3_DONE;
//     //     w_entry_next.is_get_data = (w_entry_next.state == LDQ_EX3_DONE);
//     //     w_entry_next.missu_haz_index_oh = i_ex2_q_updates.missu_index_oh;
//     //     w_entry_next.hazard_index     = i_ex2_q_updates.hazard_index;
//     //     w_ex2_ldq_entries_recv_next = 'h0;
//     //   end
//     // end
//     // LDQ_MISSU_WAIT : begin
//     //   if (w_entry_flush) begin
//     //     w_entry_next.state = LDQ_WAIT_ENTRY_CLR;
//     //   end else if (i_missu_resolve.valid && i_missu_resolve.resolve_index_oh == r_entry.missu_haz_index_oh) begin
//     //     w_entry_next.state = LDQ_ISSUE_WAIT;
//     //   end else if (~|(i_missu_resolve.missu_entry_valids & r_entry.missu_haz_index_oh)) begin
//     //     w_entry_next.state = LDQ_ISSUE_WAIT;
//     //   end
//     // end
//     // LDQ_MISSU_FULL : begin
//     //   if (w_entry_flush) begin
//     //     w_entry_next.state = LDQ_WAIT_ENTRY_CLR;
//     //   end else if (!i_missu_is_full) begin
//     //     w_entry_next.state = LDQ_ISSUE_WAIT;
//     //   end
//     // end
//     // LDQ_MISSU_EVICT_HAZ : begin
//     //   if (w_entry_flush) begin
//     //     w_entry_next.state = LDQ_WAIT_ENTRY_CLR;
//     //   end else if (i_missu_resolve.valid && i_missu_resolve.resolve_index_oh == r_entry.missu_haz_index_oh) begin
//     //     w_entry_next.state = LDQ_ISSUE_WAIT;
//     //   end else if (~|(i_missu_resolve.missu_entry_valids & r_entry.missu_haz_index_oh)) begin
//     //     w_entry_next.state = LDQ_ISSUE_WAIT;
//     //   end
//     // end
//     // LDQ_NONFWD_HAZ_WAIT : begin
//     //   w_entry_next.hazard_index = r_entry.hazard_index & ~i_stq_rs2_resolve.index;
//     //   if (w_entry_flush) begin
//     //     w_entry_next.state = LDQ_WAIT_ENTRY_CLR;
//     //   end else if (r_entry.hazard_index == 'h0) begin
//     //     w_entry_next.state = LDQ_ISSUE_WAIT;
//     //   end
//     // end
//     // LDQ_EX3_DONE : begin
//     //   if (w_entry_flush) begin
//     //     w_entry_next.state = LDQ_WAIT_ENTRY_CLR;
//     //   end else begin
//     //     w_entry_next.state = LDQ_WAIT_COMMIT;
//     //   end
//     // end
//     // LDQ_WAIT_OLDEST : begin
//     //   if (w_entry_flush) begin
//     //     w_entry_next.state = LDQ_WAIT_ENTRY_CLR;
//     //   end else if (w_oldest_ready & i_st_buffer_empty & i_st_requester_empty) begin
//     //     w_entry_next.state = LDQ_ISSUE_WAIT;
//     //   end
//     // end
//     // LDQ_WAIT_COMMIT : begin
//     //   if (w_entry_commit | w_entry_flush) begin
//     //     w_entry_next.state = LDQ_WAIT_ENTRY_CLR;
//     //   end
//     // end
//     // LDQ_WAIT_ENTRY_CLR : begin
//     //   if (i_ldq_outptr_valid) begin
//     //     w_entry_next.state = LDQ_INIT;
//     //     w_entry_next.is_valid = 1'b0;
//     //     // prevent all updates from Pipeline
//     //     w_entry_next.inst.cmt_id = 'h0;
//     //     w_entry_next.inst.grp_id = 'h0;
//     //   end
//     // end // case: LDQ_WAIT_ENTRY_CLR
//     // default : begin
//     //   w_entry_next.state = LDQ_INIT;
// // `ifdef SIMULATION
// //       $fatal (0, "This state sholudn't be reached.\n");
// // `endif // SIMULATION
//     // end
//   endcase // case (r_entry.state)

//   // BrMask update
//   if (br_upd_if.update) begin
//   end

end // always_comb


// `ifdef SIMULATION
// always_ff @ (negedge i_clk, negedge i_reset_n) begin
//   if (i_reset_n & (r_entry.state == LDQ_EX2_RUN) & ~w_entry_flush & i_ex2_q_valid) begin
//     if (w_missu_is_assigned & !$onehot(i_ex2_q_updates.missu_index_oh)) begin
//       $fatal (0, "When MISSU is assigned, MISSU index ID must be one hot but actually %x\n", i_ex2_q_updates.missu_index_oh);
//     end
//   end
// end
// `endif // SIMULATION


function automatic ldq_entry_t assign_ldq_disp (scariv_pkg::disp_t in,
                                                scariv_pkg::cmt_id_t cmt_id,
                                                scariv_pkg::grp_id_t grp_id,
                                                logic [scariv_conf_pkg::LSU_INST_NUM-1: 0] pipe_sel_oh);
  ldq_entry_t ret;
  ret = 'h0;

  ret.is_valid  = 1'b1;

  ret.inst.cmt_id    = cmt_id;
  ret.inst.grp_id    = grp_id;

//  ret.brtag   = in.brtag;

  // ret.state     = LDQ_ISSUE_WAIT;
  ret.is_get_data = 1'b0;
//  ret.pipe_sel_idx_oh = pipe_sel_oh;
  ret.addr     = 'h0;
  ret.except_valid = 1'b0;

`ifdef SIMULATION
  ret.inst.sim_inst = in.inst;
  ret.inst.sim_cat  = in.cat;

  ret.kanata_id = in.kanata_id;
`endif // SIMULATION

  return ret;
endfunction // assign_ldq_disp


// function logic all_operand_ready(ldq_entry_t entry);
//   logic     ret;
//   ret = (!entry.inst.rd_regs[0].valid |
//           entry.inst.rd_regs[0].valid & (entry.inst.rd_regs[0].ready |
//                                          entry.inst.rd_regs[0].predict_ready & !w_rs_mispredicted[0])) &
//         (!entry.inst.rd_regs[1].valid |
//           entry.inst.rd_regs[1].valid & (entry.inst.rd_regs[1].ready |
//                                          entry.inst.rd_regs[1].predict_ready & !w_rs_mispredicted[1]));
//   return ret;
// endfunction // all_operand_ready

endmodule // scariv_ldq_entry
