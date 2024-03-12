// ------------------------------------------------------------------------
// NAME : scariv_lsu_issue_entry
// TYPE : module
// ------------------------------------------------------------------------
// Scheduler entry for LSU
// ------------------------------------------------------------------------
//
// ------------------------------------------------------------------------

module scariv_lsu_issue_entry
import scariv_lsu_pkg::*;
  (
   input logic       i_clk,
   input logic       i_reset_n,

   // Output point valid specifield
   input logic       i_out_ptr_valid,

  // ROB notification interface
  rob_info_if.slave           rob_info_if,

   input logic                i_put,
   input iq_entry_t    i_put_entry,
   input scariv_pkg::cmt_id_t i_cmt_id,
   input scariv_pkg::grp_id_t i_grp_id,
   input logic                i_stq_rmw_existed,

   output logic               o_entry_valid,
  /* verilator lint_off UNOPTFLAT */
   output logic               o_entry_ready,
   output scariv_lsu_pkg::iq_entry_t o_entry,

   /* Forwarding path */
   early_wr_if.slave early_wr_if[scariv_pkg::REL_BUS_SIZE],
   phy_wr_if.slave   phy_wr_if [scariv_pkg::TGT_BUS_SIZE],
   lsu_mispred_if.slave  mispred_if[scariv_conf_pkg::LSU_INST_NUM],

  // Execution updates from pipeline
   iq_upd_if.slave iq_upd_if,
   input logic                  i_st_buffer_empty,
   input logic                  i_st_requester_empty,
   input logic                  i_missu_is_empty,
   input logic                  i_replay_queue_full,

   input logic       i_entry_picked,

   // Commit notification
   commit_if.monitor commit_if,
   // Branch Flush Notification
   br_upd_if.slave   br_upd_if,

   output logic      o_issue_succeeded,
   input logic       i_clear_entry
   );

logic    r_issued;
logic    w_issued_next;
logic    r_dead;
logic    w_dead_next;
scariv_lsu_pkg::iq_entry_t r_entry;
/* verilator lint_off UNOPTFLAT */
scariv_lsu_pkg::iq_entry_t w_entry_next;

logic    w_inst_oldest_ready;
logic    w_oldest_ready;
logic    r_oldest_ready;

scariv_pkg::rnid_t        w_rs1_rnid;
scariv_pkg::reg_t         w_rs1_type;
scariv_pkg::rel_bus_idx_t w_rs1_rel_index;
logic                     w_rs1_rel_hit;
logic                     w_rs1_may_mispred;
logic                     w_rs1_phy_hit;
logic                     w_rs1_mispredicted;
logic                     w_rs1_pred_mispredicted;

scariv_pkg::rnid_t        w_rs2_rnid;
scariv_pkg::reg_t         w_rs2_type;
scariv_pkg::rel_bus_idx_t w_rs2_rel_index;
logic                     w_rs2_rel_hit;
logic                     w_rs2_may_mispred;
logic                     w_rs2_phy_hit;
logic                     w_rs2_mispredicted;
logic                     w_rs2_pred_mispredicted;

logic     w_entry_flush;
logic     w_commit_flush;
logic     w_br_flush;
logic     w_load_commit_flush;
logic     w_load_br_flush;

logic     w_load_entry_flush;
logic     w_entry_finish;

// When previous instruction generates exception or jump
logic w_pc_update_before_entry;

scariv_lsu_pkg::lsu_sched_state_t r_state;
scariv_lsu_pkg::lsu_sched_state_t w_state_next;

// Only rs1 operand ready is checked.
function logic all_operand_ready(scariv_lsu_pkg::iq_entry_t entry);
  logic     ret;
  ret = (!entry.rd_regs[0].valid | entry.rd_regs[0].valid  & (entry.rd_regs[0].ready | entry.rd_regs[0].predict_ready));
        // (!entry.rd_regs[1].valid | entry.rd_regs[1].valid  & (entry.rd_regs[1].ready | entry.rd_regs[1].predict_ready));
        // (!entry.rd_regs[2].valid | entry.rd_regs[2].valid  & (entry.rd_regs[2].ready | entry.rd_regs[2].predict_ready));
  return ret;
endfunction // all_operand_ready

assign w_rs1_rnid = r_entry.rd_regs[0].rnid;
assign w_rs1_type = r_entry.rd_regs[0].typ;
select_early_wr_bus_oh rs1_rel_select_oh (.i_entry_rnid (w_rs1_rnid), .i_entry_type (w_rs1_type), .early_wr_if (early_wr_if),
                                          .o_valid   (w_rs1_rel_hit), .o_hit_index (w_rs1_rel_index), .o_may_mispred (w_rs1_may_mispred));
select_phy_wr_bus   rs1_phy_select    (.i_entry_rnid (w_rs1_rnid), .i_entry_type (w_rs1_type), .phy_wr_if   (phy_wr_if),
                                       .o_valid   (w_rs1_phy_hit));
select_mispred_bus  rs1_mispred_select(.i_entry_rnid (w_rs1_rnid), .i_entry_type (w_rs1_type), .i_mispred  (mispred_if),
                                       .o_mispred (w_rs1_mispredicted));

assign w_rs1_pred_mispredicted = r_entry.rd_regs[0].predict_ready & w_rs1_mispredicted;

always_comb begin
  w_state_next  = r_state;
  w_dead_next   = r_dead;
  w_issued_next = r_issued;
  w_entry_next  = r_entry;

  w_entry_next.rd_regs[0].ready            = r_entry.rd_regs[0].ready | (w_rs1_rel_hit & ~w_rs1_may_mispred) | w_rs1_phy_hit;
  w_entry_next.rd_regs[0].predict_ready[0] = w_rs1_rel_hit;
  w_entry_next.rd_regs[0].predict_ready[1] = r_entry.rd_regs[0].predict_ready[0];
  if (w_entry_next.rd_regs[0].predict_ready[0]) begin
    w_entry_next.rd_regs[0].early_index    = w_rs1_rel_index;
  end

  if (r_entry.valid) begin
    w_entry_next.oldest_valid = r_entry.oldest_valid | w_inst_oldest_ready;
  end

  case (r_state)
    scariv_lsu_pkg::LSU_SCHED_INIT : begin
      // if (w_entry_flush) begin
      //   w_state_next = scariv_lsu_pkg::LSU_SCHED_INIT;
      // end else
      if (i_put) begin
        w_entry_next = i_put_entry;
        w_issued_next = 1'b0;
        if (w_load_entry_flush) begin
          w_state_next = scariv_lsu_pkg::LSU_SCHED_CLEAR;
          w_dead_next  = 1'b1;
        end else begin
          w_state_next = scariv_lsu_pkg::LSU_SCHED_WAIT;
        end
      end
    end
    scariv_lsu_pkg::LSU_SCHED_WAIT : begin
      if (w_entry_flush) begin
        w_state_next = scariv_lsu_pkg::LSU_SCHED_CLEAR;
        w_dead_next  = 1'b1;
      end else begin
        if (o_entry_valid & o_entry_ready & i_entry_picked & !w_rs1_pred_mispredicted & !w_rs2_pred_mispredicted &
            (~i_replay_queue_full | r_entry.oldest_valid)) begin
          w_issued_next = 1'b1;
          w_state_next = scariv_lsu_pkg::LSU_SCHED_ISSUED;
        end
      end
    end
    scariv_lsu_pkg::LSU_SCHED_ISSUED : begin
      if (w_entry_flush) begin
        w_state_next = scariv_lsu_pkg::LSU_SCHED_CLEAR;
        w_dead_next  = 1'b1;
      end else begin
        if (w_rs1_pred_mispredicted | w_rs2_pred_mispredicted) begin
          w_state_next = scariv_lsu_pkg::LSU_SCHED_WAIT;
          w_issued_next = 1'b0;
          w_entry_next.rd_regs[0].predict_ready = 1'b0;
          // w_entry_next.rd_regs[1].predict_ready = 1'b0;
          // w_entry_next.rd_regs[2].predict_ready = 1'b0;
        end else if (iq_upd_if.update) begin
          w_entry_next.haz_reason = iq_upd_if.hazard_typ == EX1_HAZ_TLB_MISS  ? LSU_ISSUE_HAZ_TLB_MISS :
                                    iq_upd_if.hazard_typ == EX1_HAZ_UC_ACCESS ? LSU_ISSUE_HAZ_UC_ACCESS :
                                    r_entry.haz_reason;
          w_state_next            = iq_upd_if.hazard_typ != EX1_HAZ_NONE  ? scariv_lsu_pkg::LSU_SCHED_HAZ_WAIT :
                                    scariv_lsu_pkg::LSU_SCHED_CLEAR;
        end else begin
          w_state_next = scariv_lsu_pkg::LSU_SCHED_CLEAR;
        end
      end
    end // case: scariv_lsu_pkg::LSU_SCHED_ISSUED
    scariv_lsu_pkg::LSU_SCHED_HAZ_WAIT : begin
      if (w_entry_flush) begin
        w_state_next = scariv_lsu_pkg::LSU_SCHED_CLEAR;
      end else begin
        case (r_entry.haz_reason)
          LSU_ISSUE_HAZ_TLB_MISS : begin
            if (iq_upd_if.tlb_resolve) begin
              w_state_next = scariv_lsu_pkg::LSU_SCHED_WAIT;
            end
          end
          LSU_ISSUE_HAZ_UC_ACCESS : begin
            if (w_inst_oldest_ready & i_st_buffer_empty & i_st_requester_empty) begin
              w_state_next = scariv_lsu_pkg::LSU_SCHED_WAIT;
            end
          end
          default : begin
`ifdef SIMULATION
            $fatal(0, "This state must not come");
`endif // SIMULATION
          end
        endcase
      end
    end
    scariv_lsu_pkg::LSU_SCHED_CLEAR : begin
      if (i_clear_entry) begin
        w_state_next = scariv_lsu_pkg::LSU_SCHED_INIT;
        w_entry_next.valid = 1'b0;
      end
    end
    default : begin
// `ifdef SIMULATION
//       $fatal (0, "ALU scheduler entry reached unexpected state\n");
// `endif // SIMULATION
      w_state_next = scariv_lsu_pkg::LSU_SCHED_INIT;
    end
  endcase // case (r_state)

  // BrMask update
  if (br_upd_if.update) begin
  end
end // always_comb


assign w_commit_flush = scariv_pkg::is_flushed_commit(commit_if.commit_valid, commit_if.payload) & r_entry.valid;
assign w_br_flush     = scariv_pkg::is_br_flush_target(r_entry.cmt_id, r_entry.grp_id, br_upd_if.cmt_id, br_upd_if.grp_id,
                                                       br_upd_if.dead, br_upd_if.mispredict) & br_upd_if.update & r_entry.valid;
assign w_entry_flush = w_commit_flush | w_br_flush;

assign w_load_commit_flush = scariv_pkg::is_flushed_commit(commit_if.commit_valid, commit_if.payload) & i_put;
assign w_load_br_flush = scariv_pkg::is_br_flush_target(i_put_entry.cmt_id, br_upd_if.grp_id, br_upd_if.cmt_id, br_upd_if.grp_id,
                                                        br_upd_if.dead, br_upd_if.mispredict) & br_upd_if.update;
assign w_load_entry_flush = w_load_commit_flush | w_load_br_flush;

assign w_entry_finish = i_out_ptr_valid;

always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_entry <= 'h0;

    r_state <= scariv_lsu_pkg::LSU_SCHED_INIT;
    r_issued <= 1'b0;
    r_dead   <= 1'b0;

    r_oldest_ready <= 1'b0;
  end else begin
    r_entry <= w_entry_next;

    r_state <= w_state_next;
    r_issued <= w_issued_next;
    r_dead   <= w_dead_next;

    r_oldest_ready <= i_put ? 1'b0 : w_oldest_ready;
  end // else: !if(!i_reset_n)
end

assign w_inst_oldest_ready = (rob_info_if.cmt_id == r_entry.cmt_id) &
                             ((rob_info_if.done_grp_id & r_entry.grp_id-1) == r_entry.grp_id-1);
assign w_oldest_ready = r_entry.oldest_valid & i_st_buffer_empty /* & ~i_stq_rmw_existed */ & i_missu_is_empty & w_inst_oldest_ready /* i_out_ptr_valid */;

assign w_pc_update_before_entry = 1'b0;


assign o_entry_valid = r_entry.valid;
assign o_entry_ready = r_entry.valid & (r_state == scariv_lsu_pkg::LSU_SCHED_WAIT) &
                       (r_entry.need_oldest ? r_oldest_ready : 1'b1)  &
                       !w_pc_update_before_entry & all_operand_ready(r_entry);
assign o_entry       = r_entry;

assign o_issue_succeeded = (r_state == scariv_lsu_pkg::LSU_SCHED_CLEAR);

endmodule // scariv_lsu_issue_entry
