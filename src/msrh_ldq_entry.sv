module msrh_ldq_entry
  import msrh_lsu_pkg::*;
(
 input logic                                     i_clk,
 input logic                                     i_reset_n,

 input logic                                     i_disp_load,
 input logic [msrh_pkg::CMT_ID_W-1:0]            i_disp_cmt_id,
 input logic [msrh_conf_pkg::DISP_SIZE-1:0]      i_disp_grp_id,
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
 input                                           ex2_addr_check_t i_ex2_addr_check[msrh_conf_pkg::LSU_INST_NUM],

 output                                          ldq_entry_t o_entry,
 output logic                                    o_entry_ready,
 output logic [msrh_conf_pkg::LSU_INST_NUM-1: 0] o_ex2_ldq_entries_recv,

 input logic                                     i_entry_picked,

 input                                           lrq_resolve_t i_lrq_resolve,
 input                                           stq_resolve_t i_stq_resolve,
 // Commit notification
 input                                           msrh_pkg::commit_blk_t i_commit,
 br_upd_if.slave                                 br_upd_if,

 output logic                                    o_entry_finish,

 input logic [msrh_conf_pkg::LSU_INST_NUM-1: 0]  i_ex3_done
 );

logic                                            w_entry_ready;

ldq_entry_t                                      r_entry;
ldq_entry_t                                      w_entry_next;
logic                                            w_entry_flush;
logic                                            w_commit_flush;
logic                                            w_br_flush;
logic                                            w_load_br_flush;
logic                                            w_dead_state_clear;
logic                                            w_entry_complete;

logic                                            w_lrq_is_hazard;
logic                                            w_lrq_is_assigned;
logic                                            w_lrq_resolve_match;
logic                                            w_stq_is_hazard;
logic [msrh_conf_pkg::STQ_SIZE-1: 0]             stq_haz_idx_next;

logic [msrh_conf_pkg::LSU_INST_NUM-1: 0]         r_ex2_ldq_entries_recv;
logic [msrh_conf_pkg::LSU_INST_NUM-1: 0]         w_ex2_ldq_entries_recv_next;

logic                                            w_addr_conflict;

logic [msrh_pkg::RNID_W-1:0]                     w_rs1_rnid;
logic [msrh_pkg::RNID_W-1:0]                     w_rs2_rnid;
msrh_pkg::reg_t                                  w_rs1_type;
msrh_pkg::reg_t                                  w_rs2_type;

logic                                            w_rs1_rel_hit;
logic                                            w_rs2_rel_hit;

logic                                            w_rs1_may_mispred;
logic                                            w_rs2_may_mispred;

logic                                            w_rs1_phy_hit;
logic                                            w_rs2_phy_hit;

logic                                            w_rs1_mispredicted;
logic                                            w_rs2_mispredicted;

assign o_entry = r_entry;
assign o_ex2_ldq_entries_recv = r_ex2_ldq_entries_recv;

assign w_commit_flush = msrh_pkg::is_commit_flush_target(r_entry.cmt_id, r_entry.grp_id, i_commit) & r_entry.is_valid;
assign w_br_flush     = msrh_pkg::is_br_flush_target(r_entry.br_mask, br_upd_if.brtag) & br_upd_if.update & ~br_upd_if.dead & br_upd_if.mispredict & r_entry.is_valid;
assign w_entry_flush  = w_commit_flush | w_br_flush;

assign w_load_br_flush = msrh_pkg::is_br_flush_target(i_disp.br_mask, br_upd_if.brtag) & br_upd_if.update & ~br_upd_if.dead & br_upd_if.mispredict;

assign w_dead_state_clear = i_commit.commit &
                            (i_commit.cmt_id == r_entry.cmt_id);

assign w_lrq_is_hazard = i_ex2_q_updates.hazard_typ == LRQ_CONFLICT ||
                         i_ex2_q_updates.hazard_typ == LRQ_FULL;
assign w_stq_is_hazard = i_ex2_q_updates.hazard_typ == STQ_DEPEND;
assign w_lrq_is_assigned = i_ex2_q_updates.hazard_typ == LRQ_ASSIGNED;
assign w_lrq_resolve_match = i_ex2_q_updates.hazard_typ == LRQ_CONFLICT &
                             i_lrq_resolve.valid &
                             (i_lrq_resolve.resolve_index_oh == i_ex2_q_updates.lrq_index_oh);

assign o_entry_finish = (r_entry.state == LDQ_DEAD) & w_dead_state_clear |
                        (r_entry.state == LDQ_WAIT_COMPLETE) & w_entry_complete;

assign w_entry_complete = i_commit.commit & (i_commit.cmt_id == r_entry.cmt_id);

msrh_addr_check
  u_addr_check
    (
     .i_entry_cmt_id   (r_entry.cmt_id  ),
     .i_entry_grp_id   (r_entry.grp_id  ),
     .i_entry_paddr    (r_entry.paddr   ),
     .i_entry_size     (r_entry.size    ),
     .i_ex2_addr_check (i_ex2_addr_check),
     .o_addr_conflict  (w_addr_conflict )
     );

assign stq_haz_idx_next = i_stq_resolve.valid ? r_entry.stq_haz_idx & ~i_stq_resolve.resolve_index_oh :
                          r_entry.stq_haz_idx;

assign o_entry_ready = (r_entry.state == LDQ_ISSUE_WAIT) & !w_entry_flush &
                       all_operand_ready(r_entry);

assign w_rs1_rnid = i_disp_load ? i_disp.rs1_rnid : r_entry.inst.rs1_rnid;
assign w_rs2_rnid = i_disp_load ? i_disp.rs2_rnid : r_entry.inst.rs2_rnid;

assign w_rs1_type = i_disp_load ? i_disp.rs1_type : r_entry.inst.rs1_type;
assign w_rs2_type = i_disp_load ? i_disp.rs2_type : r_entry.inst.rs2_type;

select_early_wr_bus rs1_rel_select
(
 .i_entry_rnid (w_rs1_rnid),
 .i_entry_type (w_rs1_type),
 .i_early_wr   (i_early_wr),

 .o_valid      (w_rs1_rel_hit),
 .o_may_mispred(w_rs1_may_mispred)
 );


select_early_wr_bus rs2_rel_select
(
 .i_entry_rnid (w_rs2_rnid),
 .i_entry_type (w_rs2_type),
 .i_early_wr   (i_early_wr),

 .o_valid      (w_rs2_rel_hit),
 .o_may_mispred(w_rs2_may_mispred)
 );

select_phy_wr_bus rs1_phy_select
(
 .i_entry_rnid (w_rs1_rnid),
 .i_entry_type (w_rs1_type),
 .i_phy_wr     (i_phy_wr),

 .o_valid      (w_rs1_phy_hit)
 );


select_phy_wr_bus rs2_phy_select
(
 .i_entry_rnid (w_rs2_rnid),
 .i_entry_type (w_rs2_type),
 .i_phy_wr     (i_phy_wr),

 .o_valid      (w_rs2_phy_hit)
 );


select_mispred_bus rs1_mispred_select
(
 .i_entry_rnid (w_rs1_rnid),
 .i_entry_type (w_rs1_type),
 .i_mispred    (i_mispred_lsu),

 .o_mispred    (w_rs1_mispredicted)
 );


select_mispred_bus rs2_mispred_select
(
 .i_entry_rnid (w_rs2_rnid),
 .i_entry_type (w_rs2_type),
 .i_mispred    (i_mispred_lsu),

 .o_mispred    (w_rs2_mispredicted)
 );

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
  w_entry_next.inst.rs1_ready = r_entry.inst.rs1_ready | (w_rs1_rel_hit & ~w_rs1_may_mispred) | w_rs1_phy_hit;
  w_entry_next.inst.rs2_ready = r_entry.inst.rs2_ready | (w_rs2_rel_hit & ~w_rs2_may_mispred) | w_rs2_phy_hit;

  w_entry_next.inst.rs1_pred_ready = w_rs1_rel_hit & w_rs1_may_mispred;
  w_entry_next.inst.rs2_pred_ready = w_rs2_rel_hit & w_rs2_may_mispred;

  w_ex2_ldq_entries_recv_next = r_ex2_ldq_entries_recv;

  // BrMask update
  if (br_upd_if.update) begin
    w_entry_next.inst.br_mask[br_upd_if.brtag] = 1'b0;
  end

  case (r_entry.state)
    LDQ_INIT :
      if (w_entry_flush & r_entry.is_valid) begin
        w_entry_next.state    = LDQ_DEAD;
        // w_entry_next.is_valid = 1'b0;
        // w_entry_next.cmt_id = 'h0;
        // w_entry_next.grp_id = 'h0;
      end else if (i_disp_load) begin
        w_entry_next = assign_ldq_disp(i_disp, i_disp_cmt_id, i_disp_grp_id, i_disp_pipe_sel_oh);
        w_entry_next.inst = msrh_pkg::assign_issue_t(i_disp, i_disp_cmt_id, i_disp_grp_id,
                                                 w_rs1_rel_hit, w_rs2_rel_hit,
                                                 w_rs1_phy_hit, w_rs2_phy_hit,
                                                 w_rs1_may_mispred, w_rs2_may_mispred);
        if (w_load_br_flush) begin
          w_entry_next.state    = LDQ_DEAD;
        end
      end
    LDQ_ISSUE_WAIT : begin
      if (w_entry_flush) begin
        w_entry_next.state = LDQ_DEAD;
      end else if (o_entry_ready & i_entry_picked) begin
        w_entry_next.state = LDQ_ISSUED;
      end
    end
    LDQ_ISSUED : begin
      if (w_entry_flush) begin
        w_entry_next.state = LDQ_DEAD;
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
        if (r_entry.inst.rs1_pred_ready & w_rs1_mispredicted ||
            r_entry.inst.rs2_pred_ready & w_rs2_mispredicted) begin
          w_entry_next.state = LDQ_ISSUE_WAIT;
          w_entry_next.inst.rs1_pred_ready = 1'b0;
          w_entry_next.inst.rs2_pred_ready = 1'b0;
        end
      end // else: !if(w_entry_flush)
    end // case: LDQ_ISSUED
    LDQ_TLB_HAZ : begin
      if (w_entry_flush) begin
        w_entry_next.state = LDQ_DEAD;
      end else if (|i_tlb_resolve) begin
        w_entry_next.state = LDQ_ISSUE_WAIT;
      end
    end
    LDQ_EX2_RUN : begin
      if (w_entry_flush) begin
        w_entry_next.state = LDQ_DEAD;
      end else if (i_ex2_q_valid) begin
        w_entry_next.state = i_ex2_q_updates.hazard_typ == L1D_CONFLICT ? LDQ_ISSUE_WAIT :
                             w_lrq_resolve_match ? LDQ_ISSUE_WAIT :
                             w_lrq_is_hazard ? LDQ_LRQ_HAZ :
                             w_stq_is_hazard ? LDQ_STQ_HAZ :
                             w_lrq_is_assigned ? LDQ_ISSUE_WAIT : // When LRQ Assigned, LRQ index return is zero so rerun and ge LRQ index.
                         LDQ_EX3_DONE;    // LDQ_CHECK_ST_DEPEND
        w_entry_next.lrq_haz_index_oh = i_ex2_q_updates.lrq_index_oh;
        w_entry_next.stq_haz_idx      = i_ex2_q_updates.stq_haz_idx;
`ifdef SIMULATION
        if (!i_reset_n) begin
        end else begin
          if (w_lrq_is_assigned & i_ex2_q_updates.lrq_index_oh != 0) begin
            $fatal (0, "When LRQ is assigned, LRQ index ID must be zero\n");
          end
          if (w_lrq_is_hazard & !$onehot0(i_ex2_q_updates.lrq_index_oh)) begin
            $fatal (0, "lrq_index_oh must be one hot but actually %x\n", i_ex2_q_updates.lrq_index_oh);
          end
        end
`endif // SIMULATION
        w_ex2_ldq_entries_recv_next = 'h0;
      end
    end
    LDQ_LRQ_HAZ : begin
      if (w_entry_flush) begin
        w_entry_next.state = LDQ_DEAD;
      end else if (i_lrq_resolve.valid && i_lrq_resolve.resolve_index_oh == r_entry.lrq_haz_index_oh) begin
        w_entry_next.state = LDQ_ISSUE_WAIT;
      end
    end
    LDQ_STQ_HAZ : begin
      if (w_entry_flush) begin
        w_entry_next.state = LDQ_DEAD;
      end else begin
        w_entry_next.stq_haz_idx = stq_haz_idx_next;
        if (stq_haz_idx_next == 'h0) begin
          w_entry_next.state = LDQ_ISSUE_WAIT;
        end
      end
    end
    LDQ_EX3_DONE : begin
      if (w_entry_flush) begin
        w_entry_next.state = LDQ_DEAD;
      end else begin
        w_entry_next.state = LDQ_WAIT_COMPLETE;
      end
    end
    LDQ_WAIT_COMPLETE : begin
      if (w_entry_complete) begin
        w_entry_next.state = LDQ_INIT;
        w_entry_next.is_valid = 1'b0;
        // prevent all updates from Pipeline
        w_entry_next.cmt_id = 'h0;
        w_entry_next.grp_id = 'h0;
      end
    end
    LDQ_DEAD : begin
      if (w_dead_state_clear) begin
        w_entry_next.state = LDQ_INIT;
        w_entry_next.is_valid = 1'b0;
        // prevent all updates from Pipeline
        w_entry_next.cmt_id = 'h0;
        w_entry_next.grp_id = 'h0;
      end
    end // case: LDQ_DEAD
    LDQ_CHECK_ST_DEPEND: begin
      // Younger Store Instruction, address conflict
      if (w_addr_conflict) begin
        w_entry_next.state = LDQ_ISSUE_WAIT;
      end
      // When entry become oldest uncommitted
      if (i_commit.cmt_id == r_entry.cmt_id &&
          (i_commit.grp_id & (r_entry.grp_id-1)) == r_entry.grp_id-1) begin
        w_entry_next.state = LDQ_EX3_DONE;
      end
    end
    default : begin
      $fatal ("This state sholudn't be reached.\n");
    end
  endcase // case (r_entry.state)
end // always_comb


function ldq_entry_t assign_ldq_disp (msrh_pkg::disp_t in,
                                      logic [msrh_pkg::CMT_ID_W-1: 0] cmt_id,
                                      logic [msrh_conf_pkg::DISP_SIZE-1: 0] grp_id,
                                      logic [msrh_conf_pkg::LSU_INST_NUM-1: 0] pipe_sel_oh);
  ldq_entry_t ret;

  ret.is_valid  = 1'b1;
  ret.cmt_id    = cmt_id;
  ret.grp_id    = grp_id;

  ret.brtag   = in.brtag;
  ret.br_mask = in.br_mask;

  ret.state     = LDQ_ISSUE_WAIT;
  ret.pipe_sel_idx_oh = pipe_sel_oh;
  ret.vaddr     = 'h0;
  ret.except_valid = 1'b0;

  return ret;
endfunction // assign_ldq_disp


function logic all_operand_ready(ldq_entry_t entry);
  logic     ret;
  ret = (!entry.inst.rs1_valid | entry.inst.rs1_valid  & (entry.inst.rs1_ready | entry.inst.rs1_pred_ready)) &
        (!entry.inst.rs2_valid | entry.inst.rs2_valid  & (entry.inst.rs2_ready | entry.inst.rs2_pred_ready));
  return ret;
endfunction // all_operand_ready

endmodule // msrh_ldq_entry
