// ------------------------------------------------------------------------
// NAME : scariv_sched_entry
// TYPE : module
// ------------------------------------------------------------------------
// SCARIV Scheduler Entry
// ------------------------------------------------------------------------
// ------------------------------------------------------------------------

module scariv_sched_entry
  #(
    parameter IS_STORE = 1'b0,
    parameter IS_BRANCH = 1'b0,
    parameter EN_OLDEST = 1'b0,
    parameter NUM_OPERANDS = 2
    )
(
   input logic                                 i_clk,
   input logic                                 i_reset_n,

   // Output point valid specifield
   input logic                                 i_out_ptr_valid,

   // ROB notification interface
   rob_info_if.slave                           rob_info_if,

   input logic                                 i_put,
   input scariv_pkg::cmt_id_t                    i_cmt_id,
   input scariv_pkg::grp_id_t                    i_grp_id,
   input scariv_pkg::disp_t                      i_put_data,

   output logic                                o_entry_valid,
   output logic                                o_entry_ready,
   output                                      scariv_pkg::issue_t o_entry,

   /* Forwarding path */
   input                                       scariv_pkg::early_wr_t i_early_wr[scariv_pkg::REL_BUS_SIZE],
   input                                       scariv_pkg::phy_wr_t i_phy_wr [scariv_pkg::TGT_BUS_SIZE],
   input                                       scariv_pkg::mispred_t i_mispred_lsu[scariv_conf_pkg::LSU_INST_NUM],

   input logic                                 i_entry_picked,

   // Done Interface
   input logic                                 i_pipe_done,
   input scariv_pkg::done_payload_t              i_pipe_done_payload,

   // Commit notification
   input                                       scariv_pkg::commit_blk_t i_commit,
   // Branch Flush Notification
   br_upd_if.slave                             br_upd_if,

   output logic                                o_entry_wait_complete,
   output logic                                o_entry_finish,

   output scariv_pkg::done_rpt_t                 o_done_report,
   input logic                                 i_done_accept
   );

logic    r_issued;
logic    w_issued_next;
logic    r_dead;
logic    w_dead_next;
scariv_pkg::issue_t r_entry;
/* verilator lint_off UNOPTFLAT */
scariv_pkg::issue_t w_entry_next;
scariv_pkg::issue_t w_init_entry;

logic    w_oldest_ready;

scariv_pkg::rnid_t w_rs_rnid[NUM_OPERANDS];
scariv_pkg::reg_t  w_rs_type[NUM_OPERANDS];
logic [NUM_OPERANDS-1: 0] w_rs_rel_hit;
logic [NUM_OPERANDS-1: 0] w_rs_may_mispred;
logic [NUM_OPERANDS-1: 0] w_rs_phy_hit;
logic [NUM_OPERANDS-1: 0] w_rs_mispredicted;

logic     w_entry_flush;
logic     w_commit_flush;
logic     w_br_flush;
logic     w_load_commit_flush;
logic     w_load_br_flush;

logic     w_load_entry_flush;
logic     w_entry_finish;

// When previous instruction generates exception or jump
logic w_pc_update_before_entry;

scariv_pkg::sched_state_t r_state;
scariv_pkg::sched_state_t w_state_next;

function logic all_operand_ready(scariv_pkg::issue_t entry);
  logic     ret;
  if (IS_STORE) begin
    ret = (!entry.rd_regs[0].valid | entry.rd_regs[0].valid  & (entry.rd_regs[0].ready | entry.rd_regs[0].predict_ready));
  end else begin
    ret = (!entry.rd_regs[0].valid | entry.rd_regs[0].valid  & (entry.rd_regs[0].ready | entry.rd_regs[0].predict_ready)) &
          (!entry.rd_regs[1].valid | entry.rd_regs[1].valid  & (entry.rd_regs[1].ready | entry.rd_regs[1].predict_ready)) &
          (!entry.rd_regs[2].valid | entry.rd_regs[2].valid  & (entry.rd_regs[2].ready | entry.rd_regs[2].predict_ready));
  end
  return ret;
endfunction // all_operand_ready

generate for (genvar rs_idx = 0; rs_idx < NUM_OPERANDS; rs_idx++) begin : rs_loop
  assign w_rs_rnid[rs_idx] = i_put ? i_put_data.rd_regs[rs_idx].rnid : r_entry.rd_regs[rs_idx].rnid;
  assign w_rs_type[rs_idx] = i_put ? i_put_data.rd_regs[rs_idx].typ  : r_entry.rd_regs[rs_idx].typ;

  select_early_wr_bus rs_rel_select    (.i_entry_rnid (w_rs_rnid[rs_idx]), .i_entry_type (w_rs_type[rs_idx]), .i_early_wr (i_early_wr),
                                        .o_valid   (w_rs_rel_hit[rs_idx]), .o_may_mispred (w_rs_may_mispred[rs_idx]));
  select_phy_wr_bus   rs_phy_select    (.i_entry_rnid (w_rs_rnid[rs_idx]), .i_entry_type (w_rs_type[rs_idx]), .i_phy_wr   (i_phy_wr),
                                        .o_valid   (w_rs_phy_hit[rs_idx]));
  select_mispred_bus  rs_mispred_select(.i_entry_rnid (w_rs_rnid[rs_idx]), .i_entry_type (w_rs_type[rs_idx]), .i_mispred  (i_mispred_lsu),
                                        .o_mispred (w_rs_mispredicted[rs_idx]));
end
endgenerate

logic [NUM_OPERANDS-1: 0] w_rs_pred_mispredicted;
logic                     w_rs_pred_mispredicted_or;
generate for (genvar rs_idx = 0; rs_idx < NUM_OPERANDS; rs_idx++) begin : rs_pred_mispred_loop
  assign w_rs_pred_mispredicted[rs_idx] = r_entry.rd_regs[rs_idx].predict_ready & w_rs_mispredicted[rs_idx];
end
endgenerate
assign w_rs_pred_mispredicted_or = |w_rs_pred_mispredicted;


always_comb begin
  w_state_next  = r_state;
  w_dead_next   = r_dead;
  w_issued_next = r_issued;
  w_entry_next  = r_entry;

  for (int rs_idx = 0; rs_idx < NUM_OPERANDS; rs_idx++) begin
    w_entry_next.rd_regs[rs_idx].ready         = r_entry.rd_regs[rs_idx].ready | (w_rs_rel_hit[rs_idx] & ~w_rs_may_mispred[rs_idx]) | w_rs_phy_hit[rs_idx];
    w_entry_next.rd_regs[rs_idx].predict_ready = w_rs_rel_hit[rs_idx] & w_rs_may_mispred[rs_idx];
  end

  case (r_state)
    scariv_pkg::INIT : begin
      if (w_entry_flush) begin
        w_state_next = scariv_pkg::INIT;
      end else if (i_put) begin
        w_entry_next = w_init_entry;
        if (w_load_entry_flush) begin
          w_state_next = scariv_pkg::DEAD;
          w_dead_next  = 1'b1;
        end else begin
          w_state_next = scariv_pkg::WAIT;
        end
      end
    end
    scariv_pkg::WAIT : begin
      if (w_entry_flush) begin
        w_state_next = scariv_pkg::DEAD;
        w_dead_next  = 1'b1;
      end else begin
        if (o_entry_valid & w_pc_update_before_entry & w_oldest_ready) begin
          w_state_next = scariv_pkg::DONE;
        end else if (o_entry_valid & o_entry_ready & i_entry_picked) begin
          w_issued_next = 1'b1;
          w_state_next = scariv_pkg::ISSUED;
        end
      end
    end
    scariv_pkg::ISSUED : begin
      if (w_entry_flush) begin
        w_state_next = scariv_pkg::DEAD;
        w_dead_next  = 1'b1;
      end else begin
        if (i_pipe_done) begin
          w_state_next = scariv_pkg::DONE;
          w_entry_next.except_valid = i_pipe_done_payload.except_valid;
          w_entry_next.except_type  = i_pipe_done_payload.except_type;
          w_entry_next.except_tval  = i_pipe_done_payload.except_tval;
          w_entry_next.fflags_update_valid = i_pipe_done_payload.fflags_update_valid;
          w_entry_next.fflags              = i_pipe_done_payload.fflags;
        end
        if (w_rs_pred_mispredicted_or) begin
          w_state_next = scariv_pkg::WAIT;
          w_issued_next = 1'b0;
          w_entry_next.rd_regs[0].predict_ready = 1'b0;
          w_entry_next.rd_regs[1].predict_ready = 1'b0;
          w_entry_next.rd_regs[2].predict_ready = 1'b0;
        end
      end
    end
    scariv_pkg::DONE : begin
      if (w_entry_flush) begin
        w_state_next = scariv_pkg::DEAD;
        w_dead_next  = 1'b1;
      end else begin
        if (i_done_accept) begin
          w_state_next = scariv_pkg::WAIT_COMPLETE;
        end
      end
    end
    scariv_pkg::WAIT_COMPLETE : begin
      if (w_entry_finish) begin
        w_state_next = scariv_pkg::INIT;
        w_entry_next.valid = 1'b0;
        w_issued_next = 1'b0;
        w_dead_next = 1'b0;
        // prevent all updates from Pipeline
        w_entry_next.cmt_id = 'h0;
        w_entry_next.grp_id = 'h0;
      end else if (w_entry_flush) begin
        w_state_next = scariv_pkg::DEAD;
        w_dead_next  = 1'b1;
      end
    end // case: scariv_pkg::WAIT_COMPLETE
    scariv_pkg::DEAD : begin
      if (w_entry_finish) begin
        w_state_next = scariv_pkg::INIT;
        w_entry_next.valid = 1'b0;
        w_issued_next = 1'b0;
        w_dead_next   = 1'b0;
        // prevent all updates from Pipeline
        w_entry_next.cmt_id = 'h0;
        w_entry_next.grp_id = 'h0;
      end
    end // case: scariv_pkg::DEAD
    default : begin
      w_state_next = scariv_pkg::INIT;
// `ifdef SIMULATION
//       $fatal(0, "Unknown state reached\n");
// `endif // SIMULATION
    end
  endcase // case (r_state)

  // BrMask update
  if (br_upd_if.update) begin
    w_entry_next.br_mask[br_upd_if.brtag] = 1'b0;
  end
end


generate if (NUM_OPERANDS == 3) begin : init_entry_op3
  assign w_init_entry = scariv_pkg::assign_issue_op3(i_put_data, i_cmt_id, i_grp_id,
                                                   w_rs_rel_hit, w_rs_phy_hit, w_rs_may_mispred);
end else begin
  assign w_init_entry = scariv_pkg::assign_issue_op2(i_put_data, i_cmt_id, i_grp_id,
                                                   w_rs_rel_hit, w_rs_phy_hit, w_rs_may_mispred);
end
endgenerate

assign w_commit_flush = scariv_pkg::is_commit_flush_target(r_entry.cmt_id, r_entry.grp_id, i_commit) & r_entry.valid;
assign w_br_flush     = scariv_pkg::is_br_flush_target(r_entry.br_mask, br_upd_if.brtag,
                                                     br_upd_if.dead, br_upd_if.mispredict) & br_upd_if.update & r_entry.valid;
assign w_entry_flush = w_commit_flush | w_br_flush;

assign w_load_commit_flush = scariv_pkg::is_commit_flush_target(i_cmt_id, i_grp_id, i_commit) & i_put;
assign w_load_br_flush = scariv_pkg::is_br_flush_target(i_put_data.br_mask, br_upd_if.brtag,
                                                      br_upd_if.dead, br_upd_if.mispredict) & br_upd_if.update;
assign w_load_entry_flush = w_load_commit_flush | w_load_br_flush;

assign w_entry_finish = i_out_ptr_valid;

always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_entry <= 'h0;

    r_state <= scariv_pkg::INIT;
    r_issued <= 1'b0;
    r_dead   <= 1'b0;
  end else begin
    r_entry <= w_entry_next;

    r_state <= w_state_next;
    r_issued <= w_issued_next;
    r_dead   <= w_dead_next;
  end // else: !if(!i_reset_n)
end

generate if (EN_OLDEST == 1'b1) begin
  assign w_oldest_ready = (rob_info_if.cmt_id == r_entry.cmt_id) &
                          ((rob_info_if.done_grp_id & r_entry.grp_id-1) == r_entry.grp_id-1);
  assign w_pc_update_before_entry = |((r_entry.grp_id - 1) & (rob_info_if.upd_pc_valid | rob_info_if.except_valid) & rob_info_if.done_grp_id);
end else begin
  assign w_oldest_ready = 1'b1;
  assign w_pc_update_before_entry = 1'b0;
end
endgenerate


assign o_entry_valid = r_entry.valid;
assign o_entry_ready = r_entry.valid & (r_state == scariv_pkg::WAIT) & !w_entry_flush &
                       w_oldest_ready & !w_pc_update_before_entry & all_operand_ready(w_entry_next);
assign o_entry       = w_entry_next;

assign o_entry_wait_complete = (r_state == scariv_pkg::WAIT_COMPLETE);

assign o_done_report.valid        = (r_state == scariv_pkg::DONE) & !w_entry_flush;
assign o_done_report.cmt_id       = r_entry.cmt_id;
assign o_done_report.grp_id       = r_entry.grp_id;
assign o_done_report.except_valid = r_entry.except_valid;
assign o_done_report.except_type  = r_entry.except_type;
assign o_done_report.except_tval  = r_entry.except_tval;
assign o_done_report.fflags_update_valid = r_entry.fflags_update_valid;
assign o_done_report.fflags       = r_entry.fflags;

assign o_entry_finish = w_entry_finish & ((r_state == scariv_pkg::DEAD) |
                                          (r_state == scariv_pkg::WAIT_COMPLETE));

`ifdef SIMULATION
// Kanata
import "DPI-C" function void log_stage
(
 input longint id,
 input string stage
);

always_ff @ (negedge i_clk, negedge i_reset_n) begin
  if (i_reset_n) begin
    if (o_done_report.valid & i_done_accept) begin
      log_stage (r_entry.kanata_id, "DO");
    end
  end
end
`endif // SIMULATION

endmodule // scariv_sched_entry
