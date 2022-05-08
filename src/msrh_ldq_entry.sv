module msrh_ldq_entry
  import msrh_lsu_pkg::*;
(
 input logic                                     i_clk,
 input logic                                     i_reset_n,

 input logic                                     i_disp_load,
 input msrh_pkg::cmt_id_t            i_disp_cmt_id,
 input msrh_pkg::grp_id_t      i_disp_grp_id,
 input                                           msrh_pkg::disp_t i_disp,
 input logic [msrh_conf_pkg::LSU_INST_NUM-1: 0]  i_disp_pipe_sel_oh,

 /* Forwarding path */
 input                                           msrh_pkg::early_wr_t i_early_wr[msrh_pkg::REL_BUS_SIZE],
 input                                           msrh_pkg::phy_wr_t i_phy_wr [msrh_pkg::TGT_BUS_SIZE],
 input                                           msrh_pkg::mispred_t i_mispred_lsu[msrh_conf_pkg::LSU_INST_NUM],

 // Updates from LSU Pipeline EX1 stage
 input logic                                     i_ex1_q_valid,
 input                                           ex1_q_update_t i_ex1_q_updates,
 // Updates from LSU Pipeline EX2 stage
 input logic [msrh_conf_pkg::LSU_INST_NUM-1: 0]  i_tlb_resolve,
 input logic                                     i_ex2_q_valid,
 input                                           ex2_q_update_t i_ex2_q_updates,

 output                                          ldq_entry_t o_entry,
 output logic                                    o_entry_ready,
 output logic [msrh_conf_pkg::LSU_INST_NUM-1: 0] o_ex2_ldq_entries_recv,

 input logic                                     i_entry_picked,

 input                                           lrq_resolve_t i_lrq_resolve,
 input logic                                     i_lrq_is_full,
 // Commit notification
 input                                           msrh_pkg::commit_blk_t i_commit,
 br_upd_if.slave                                 br_upd_if,

 input logic                                     i_ldq_outptr_valid,
 output logic                                    o_entry_finish,

 done_if.slave   ex3_done_if
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

logic                                            w_lrq_is_conflict;
logic                                            w_lrq_is_full;
logic                                            w_lrq_is_assigned;
logic                                            w_lrq_resolve_match;
logic                                            w_lrq_evict_is_hazard;

logic [msrh_conf_pkg::LSU_INST_NUM-1: 0]         r_ex2_ldq_entries_recv;
logic [msrh_conf_pkg::LSU_INST_NUM-1: 0]         w_ex2_ldq_entries_recv_next;

msrh_pkg::rnid_t                                 w_rs_rnid[2];
msrh_pkg::reg_t                                  w_rs_type[2];
logic [ 1: 0]                                    w_rs_rel_hit;
logic [ 1: 0]                                    w_rs_may_mispred;
logic [ 1: 0]                                    w_rs_phy_hit;
logic [ 1: 0]                                    w_rs_mispredicted;

assign o_entry = r_entry;
assign o_ex2_ldq_entries_recv = r_ex2_ldq_entries_recv;

assign w_commit_flush = msrh_pkg::is_commit_flush_target(r_entry.cmt_id, r_entry.grp_id, i_commit) & r_entry.is_valid;
assign w_br_flush     = msrh_pkg::is_br_flush_target(r_entry.br_mask, br_upd_if.brtag,
                                                     br_upd_if.dead, br_upd_if.mispredict) & br_upd_if.update & r_entry.is_valid;
assign w_entry_flush  = w_commit_flush | w_br_flush;


assign w_load_commit_flush = msrh_pkg::is_commit_flush_target(i_disp_cmt_id, i_disp_grp_id, i_commit);
assign w_load_br_flush = msrh_pkg::is_br_flush_target(i_disp.br_mask, br_upd_if.brtag,
                                                      br_upd_if.dead, br_upd_if.mispredict) & br_upd_if.update;
assign w_load_flush = w_load_commit_flush | w_load_br_flush;

assign w_dead_state_clear = i_commit.commit & (i_commit.cmt_id == r_entry.cmt_id);

assign w_lrq_is_conflict = i_ex2_q_updates.hazard_typ == LRQ_CONFLICT;
assign w_lrq_is_full     = i_ex2_q_updates.hazard_typ == LRQ_FULL;
assign w_lrq_evict_is_hazard = i_ex2_q_updates.hazard_typ == LRQ_EVICT_CONFLICT;

assign w_lrq_is_assigned = i_ex2_q_updates.hazard_typ == LRQ_ASSIGNED;
assign w_lrq_resolve_match = i_ex2_q_updates.hazard_typ == LRQ_CONFLICT &
                             i_lrq_resolve.valid &
                             (i_lrq_resolve.resolve_index_oh == i_ex2_q_updates.lrq_index_oh);

assign o_entry_finish = (r_entry.state == LDQ_WAIT_ENTRY_CLR) & i_ldq_outptr_valid;

assign w_entry_commit = i_commit.commit & (i_commit.cmt_id == r_entry.cmt_id);

assign o_entry_ready = (r_entry.state == LDQ_ISSUE_WAIT) & !w_entry_flush &
                       all_operand_ready(r_entry);


generate for (genvar rs_idx = 0; rs_idx < 2; rs_idx++) begin : rs_loop
  assign w_rs_rnid[rs_idx] = i_disp_load ? i_disp.rd_regs[rs_idx].rnid : r_entry.inst.rd_regs[rs_idx].rnid;
  assign w_rs_type[rs_idx] = i_disp_load ? i_disp.rd_regs[rs_idx].typ  : r_entry.inst.rd_regs[rs_idx].typ;

  select_early_wr_bus rs_rel_select    (.i_entry_rnid (w_rs_rnid[rs_idx]), .i_entry_type (w_rs_type[rs_idx]), .i_early_wr (i_early_wr),
                                        .o_valid   (w_rs_rel_hit[rs_idx]), .o_may_mispred (w_rs_may_mispred[rs_idx]));
  select_phy_wr_bus   rs_phy_select    (.i_entry_rnid (w_rs_rnid[rs_idx]), .i_entry_type (w_rs_type[rs_idx]), .i_phy_wr   (i_phy_wr),
                                        .o_valid   (w_rs_phy_hit[rs_idx]));
  select_mispred_bus  rs_mispred_select(.i_entry_rnid (w_rs_rnid[rs_idx]), .i_entry_type (w_rs_type[rs_idx]), .i_mispred  (i_mispred_lsu),
                                        .o_mispred (w_rs_mispredicted[rs_idx]));
end
endgenerate

always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_entry.is_valid <= 1'b0;
    r_entry.state <= LDQ_INIT;
    r_entry.lrq_haz_index_oh <= 'h0;

    r_ex2_ldq_entries_recv <= 'h0;
  end else begin
    r_entry <= w_entry_next;
    r_ex2_ldq_entries_recv <= w_ex2_ldq_entries_recv_next;
  end
end

always_comb begin

  w_entry_next = r_entry;

  for (int rs_idx = 0; rs_idx < 2; rs_idx++) begin
    w_entry_next.inst.rd_regs[rs_idx].ready = r_entry.inst.rd_regs[rs_idx].ready | w_rs_phy_hit[rs_idx];
    w_entry_next.inst.rd_regs[rs_idx].predict_ready = w_rs_rel_hit[rs_idx] & w_rs_may_mispred[rs_idx];
  end

  w_ex2_ldq_entries_recv_next = r_ex2_ldq_entries_recv;

  case (r_entry.state)
    LDQ_INIT :
      if (w_entry_flush & r_entry.is_valid) begin
        w_entry_next.state    = LDQ_WAIT_ENTRY_CLR;
        // w_entry_next.is_valid = 1'b0;
        // w_entry_next.cmt_id = 'h0;
        // w_entry_next.grp_id = 'h0;
      end else if (i_disp_load) begin
        w_entry_next = assign_ldq_disp(i_disp, i_disp_cmt_id, i_disp_grp_id, i_disp_pipe_sel_oh);
        w_entry_next.inst = msrh_pkg::assign_issue_op2(i_disp, i_disp_cmt_id, i_disp_grp_id,
                                                       w_rs_rel_hit, w_rs_phy_hit, w_rs_may_mispred);
        if (w_load_flush) begin
          w_entry_next.state    = LDQ_WAIT_ENTRY_CLR;
        end
      end
    LDQ_ISSUE_WAIT : begin
      if (w_entry_flush) begin
        w_entry_next.state = LDQ_WAIT_ENTRY_CLR;
      end else if (r_entry.inst.rd_regs[0].predict_ready & w_rs_mispredicted[0] |
            r_entry.inst.rd_regs[1].predict_ready & w_rs_mispredicted[1]) begin
          w_entry_next.state = LDQ_ISSUE_WAIT;
          w_entry_next.inst.rd_regs[0].predict_ready = 1'b0;
          w_entry_next.inst.rd_regs[1].predict_ready = 1'b0;
      end else if (o_entry_ready & i_entry_picked) begin
        w_entry_next.state = LDQ_ISSUED;
      end
    end
    LDQ_ISSUED : begin
      if (w_entry_flush) begin
        w_entry_next.state = LDQ_WAIT_ENTRY_CLR;
      end else begin
        if (w_entry_next.is_valid & i_ex1_q_valid) begin
          w_entry_next.state           = i_ex1_q_updates.hazard_valid     ? LDQ_TLB_HAZ :
                                         LDQ_EX2_RUN;
          w_entry_next.except_valid    = i_ex1_q_updates.tlb_except_valid;
          w_entry_next.except_type     = i_ex1_q_updates.tlb_except_type;
          w_entry_next.vaddr           = i_ex1_q_updates.vaddr;
          w_entry_next.paddr           = i_ex1_q_updates.paddr;
          // w_entry_next.pipe_sel_idx_oh = i_ex1_q_updates.pipe_sel_idx_oh;
          // w_entry_next.inst            = i_ex1_q_updates.inst;
          w_entry_next.size            = i_ex1_q_updates.size;

          for (int p_idx = 0; p_idx < msrh_conf_pkg::LSU_INST_NUM; p_idx++) begin : pipe_loop
            w_ex2_ldq_entries_recv_next[p_idx] =  i_ex1_q_valid &
                                                  !i_ex1_q_updates.hazard_valid &
                                                  r_entry.pipe_sel_idx_oh[p_idx];
          end
        end // if (i_ex1_q_valid)
      end // else: !if(w_entry_flush)
    end // case: LDQ_ISSUED
    LDQ_TLB_HAZ : begin
      if (w_entry_flush) begin
        w_entry_next.state = LDQ_WAIT_ENTRY_CLR;
      end else if (|i_tlb_resolve) begin
        w_entry_next.state = LDQ_ISSUE_WAIT;
      end
    end
    LDQ_EX2_RUN : begin
      if (w_entry_flush) begin
        w_entry_next.state = LDQ_WAIT_ENTRY_CLR;
      end else if (i_ex2_q_valid) begin
        w_entry_next.state = i_ex2_q_updates.hazard_typ == L1D_CONFLICT ? LDQ_ISSUE_WAIT :
                             w_lrq_resolve_match   ? LDQ_ISSUE_WAIT :
                             w_lrq_is_conflict     ? LDQ_LRQ_CONFLICT :
                             w_lrq_is_full         ? LDQ_LRQ_FULL :
                             w_lrq_evict_is_hazard ? LDQ_LRQ_EVICT_HAZ :
                             w_lrq_is_assigned     ? LDQ_ISSUE_WAIT : // When LRQ Assigned, LRQ index return is zero so rerun and ge LRQ index.
                             LDQ_EX3_DONE;
        w_entry_next.is_get_data = (w_entry_next.state == LDQ_EX3_DONE);
        w_entry_next.lrq_haz_index_oh = i_ex2_q_updates.lrq_index_oh;
        w_ex2_ldq_entries_recv_next = 'h0;
      end
    end
    LDQ_LRQ_CONFLICT : begin
      if (w_entry_flush) begin
        w_entry_next.state = LDQ_WAIT_ENTRY_CLR;
      end else if (i_lrq_resolve.valid && i_lrq_resolve.resolve_index_oh == r_entry.lrq_haz_index_oh) begin
        w_entry_next.state = LDQ_ISSUE_WAIT;
      end else if (~|(i_lrq_resolve.lrq_entry_valids & r_entry.lrq_haz_index_oh)) begin
        w_entry_next.state = LDQ_ISSUE_WAIT;
      end
    end
    LDQ_LRQ_FULL : begin
      if (w_entry_flush) begin
        w_entry_next.state = LDQ_WAIT_ENTRY_CLR;
      end else if (!i_lrq_is_full) begin
        w_entry_next.state = LDQ_ISSUE_WAIT;
      end
    end
    LDQ_LRQ_EVICT_HAZ : begin
      if (w_entry_flush) begin
        w_entry_next.state = LDQ_WAIT_ENTRY_CLR;
      end else if (i_lrq_resolve.valid && i_lrq_resolve.resolve_index_oh == r_entry.lrq_haz_index_oh) begin
        w_entry_next.state = LDQ_ISSUE_WAIT;
      end else if (~|(i_lrq_resolve.lrq_entry_valids & r_entry.lrq_haz_index_oh)) begin
        w_entry_next.state = LDQ_ISSUE_WAIT;
      end
    end
    LDQ_EX3_DONE : begin
      if (w_entry_flush) begin
        w_entry_next.state = LDQ_WAIT_ENTRY_CLR;
      end else begin
        w_entry_next.state = LDQ_WAIT_COMMIT;
      end
    end
    LDQ_WAIT_COMMIT : begin
      if (w_entry_commit | w_entry_flush) begin
        w_entry_next.state = LDQ_WAIT_ENTRY_CLR;
      end
    end
    LDQ_WAIT_ENTRY_CLR : begin
      if (i_ldq_outptr_valid) begin
        w_entry_next.state = LDQ_INIT;
        w_entry_next.is_valid = 1'b0;
        // prevent all updates from Pipeline
        w_entry_next.cmt_id = 'h0;
        w_entry_next.grp_id = 'h0;
      end
    end // case: LDQ_WAIT_ENTRY_CLR
    default : begin
      w_entry_next.state = LDQ_INIT;
// `ifdef SIMULATION
//       $fatal (0, "This state sholudn't be reached.\n");
// `endif // SIMULATION
    end
  endcase // case (r_entry.state)

  // BrMask update
  if (br_upd_if.update) begin
    w_entry_next.br_mask[br_upd_if.brtag] = 1'b0;
  end

end // always_comb


`ifdef SIMULATION
always_ff @ (negedge i_clk, negedge i_reset_n) begin
  if (i_reset_n & (r_entry.state == LDQ_EX2_RUN) & ~w_entry_flush & i_ex2_q_valid) begin
    if (w_lrq_is_assigned & !$onehot(i_ex2_q_updates.lrq_index_oh)) begin
      $fatal (0, "When LRQ is assigned, LRQ index ID must be one hot but actually %x\n", i_ex2_q_updates.lrq_index_oh);
    end
    if (w_lrq_is_conflict & !$onehot0(i_ex2_q_updates.lrq_index_oh)) begin
      $fatal (0, "lrq_index_oh must be one hot but actually %x\n", i_ex2_q_updates.lrq_index_oh);
    end
  end
end
`endif // SIMULATION


function ldq_entry_t assign_ldq_disp (msrh_pkg::disp_t in,
                                      msrh_pkg::cmt_id_t cmt_id,
                                      msrh_pkg::grp_id_t grp_id,
                                      logic [msrh_conf_pkg::LSU_INST_NUM-1: 0] pipe_sel_oh);
  ldq_entry_t ret;

  ret.is_valid  = 1'b1;
  ret.cmt_id    = cmt_id;
  ret.grp_id    = grp_id;

  ret.brtag   = in.brtag;
  ret.br_mask = in.br_mask;

  ret.state     = LDQ_ISSUE_WAIT;
  ret.is_get_data = 1'b0;
  ret.pipe_sel_idx_oh = pipe_sel_oh;
  ret.vaddr     = 'h0;
  ret.except_valid = 1'b0;

`ifdef SIMULATION
  ret.kanata_id = in.kanata_id;
`endif // SIMULATION

  return ret;
endfunction // assign_ldq_disp


function logic all_operand_ready(ldq_entry_t entry);
  logic     ret;
  ret = (!entry.inst.rd_regs[0].valid | entry.inst.rd_regs[0].valid  & (entry.inst.rd_regs[0].ready | entry.inst.rd_regs[0].predict_ready)) &
        (!entry.inst.rd_regs[1].valid | entry.inst.rd_regs[1].valid  & (entry.inst.rd_regs[1].ready | entry.inst.rd_regs[1].predict_ready));
  return ret;
endfunction // all_operand_ready

endmodule // msrh_ldq_entry
