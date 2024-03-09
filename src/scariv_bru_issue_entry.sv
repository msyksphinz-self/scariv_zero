// ------------------------------------------------------------------------
// NAME : scariv_issue_entry
// TYPE : module
// ------------------------------------------------------------------------
// Scheduler entry for ALU
// ------------------------------------------------------------------------
//
// ------------------------------------------------------------------------

module scariv_bru_issue_entry
  (
   input logic       i_clk,
   input logic       i_reset_n,

   // Output point valid specifield
   input logic       i_out_ptr_valid,

   // ROB notification interface
   rob_info_if.slave rob_info_if,

   input logic                i_put,
   input logic                i_dead_put,

   input scariv_pkg::cmt_id_t i_cmt_id,
   input scariv_pkg::grp_id_t i_grp_id,
   input scariv_pkg::disp_t   i_put_data,
   input logic [riscv_pkg::VADDR_W-1:1]  i_basicblk_pc_vaddr,

   output logic               o_entry_valid,
   /* verilator lint_off UNOPTFLAT */
   output logic               o_entry_ready,
   output scariv_bru_pkg::issue_entry_t o_entry,

   /* Forwarding path */
   early_wr_if.slave early_wr_if   [scariv_pkg::REL_BUS_SIZE],
   phy_wr_if.slave   phy_wr_if     [scariv_pkg::TGT_BUS_SIZE],
   lsu_mispred_if.slave  mispred_if[scariv_conf_pkg::LSU_INST_NUM],

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
scariv_bru_pkg::issue_entry_t r_entry;
/* verilator lint_off UNOPTFLAT */
scariv_bru_pkg::issue_entry_t w_entry_next;
scariv_bru_pkg::issue_entry_t w_init_entry;

logic    w_oldest_ready;

scariv_pkg::rnid_t w_rs_rnid[2];
scariv_pkg::reg_t  w_rs_type[2];
logic [ 1: 0]             w_rs_rel_hit;
scariv_pkg::rel_bus_idx_t w_rs_rel_index[2];
logic [ 1: 0]             w_rs_may_mispred;
logic [ 1: 0]             w_rs_phy_hit;
logic [ 1: 0]             w_rs_mispredicted;

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

function logic all_operand_ready(scariv_bru_pkg::issue_entry_t entry);
  logic     ret;
  ret = (!entry.rd_regs[0].valid | entry.rd_regs[0].valid  & (entry.rd_regs[0].ready | entry.rd_regs[0].predict_ready)) &
        (!entry.rd_regs[1].valid | entry.rd_regs[1].valid  & (entry.rd_regs[1].ready | entry.rd_regs[1].predict_ready)) &
        (!entry.rd_regs[2].valid | entry.rd_regs[2].valid  & (entry.rd_regs[2].ready | entry.rd_regs[2].predict_ready));
  return ret;
endfunction // all_operand_ready

generate for (genvar rs_idx = 0; rs_idx < 2; rs_idx++) begin : rs_loop
  assign w_rs_rnid[rs_idx] = i_put ? i_put_data.rd_regs[rs_idx].rnid : r_entry.rd_regs[rs_idx].rnid;
  assign w_rs_type[rs_idx] = i_put ? i_put_data.rd_regs[rs_idx].typ  : r_entry.rd_regs[rs_idx].typ;

  select_early_wr_bus_oh rs_rel_select_oh (.i_entry_rnid (w_rs_rnid[rs_idx]), .i_entry_type (w_rs_type[rs_idx]), .early_wr_if (early_wr_if),
                                           .o_valid   (w_rs_rel_hit[rs_idx]), .o_hit_index (w_rs_rel_index[rs_idx]), .o_may_mispred (w_rs_may_mispred[rs_idx]));
  select_phy_wr_bus   rs_phy_select    (.i_entry_rnid (w_rs_rnid[rs_idx]), .i_entry_type (w_rs_type[rs_idx]), .phy_wr_if   (phy_wr_if),
                                        .o_valid   (w_rs_phy_hit[rs_idx]));
  select_mispred_bus  rs_mispred_select(.i_entry_rnid (w_rs_rnid[rs_idx]), .i_entry_type (w_rs_type[rs_idx]), .i_mispred  (mispred_if),
                                        .o_mispred (w_rs_mispredicted[rs_idx]));
end
endgenerate

logic [ 1: 0] w_rs_pred_mispredicted;
logic         w_rs_pred_mispredicted_or;
generate for (genvar rs_idx = 0; rs_idx < 2; rs_idx++) begin : rs_pred_mispred_loop
  assign w_rs_pred_mispredicted[rs_idx] = r_entry.rd_regs[rs_idx].predict_ready & w_rs_mispredicted[rs_idx];
end
endgenerate
assign w_rs_pred_mispredicted_or = |w_rs_pred_mispredicted;


always_comb begin
  w_state_next  = r_state;
  w_dead_next   = r_dead;
  w_issued_next = r_issued;
  w_entry_next  = r_entry;

  for (int rs_idx = 0; rs_idx < 2; rs_idx++) begin
    w_entry_next.rd_regs[rs_idx].ready            = r_entry.rd_regs[rs_idx].ready | (w_rs_rel_hit[rs_idx] & ~w_rs_may_mispred[rs_idx]) | w_rs_phy_hit[rs_idx];
    w_entry_next.rd_regs[rs_idx].predict_ready[0] = w_rs_rel_hit[rs_idx];
    w_entry_next.rd_regs[rs_idx].predict_ready[1] = r_entry.rd_regs[rs_idx].predict_ready[0];

    if (w_entry_next.rd_regs[rs_idx].predict_ready[0]) begin
      w_entry_next.rd_regs[rs_idx].early_index    = w_rs_rel_index[rs_idx];
    end
  end

  case (r_state)
    scariv_pkg::INIT : begin
      if (w_entry_flush) begin
        w_state_next = scariv_pkg::INIT;
      end else if (i_put) begin
        w_entry_next = w_init_entry;
        w_issued_next = 1'b0;
        if (w_load_entry_flush) begin
          w_state_next = scariv_pkg::SCHED_CLEAR;
          w_dead_next  = 1'b1;
        end else begin
          w_state_next = scariv_pkg::WAIT;
        end
      end
    end
    scariv_pkg::WAIT : begin
      if (w_entry_flush) begin
        w_state_next = scariv_pkg::SCHED_CLEAR;
        w_dead_next  = 1'b1;
      end else begin
        if (o_entry_valid & w_pc_update_before_entry & w_oldest_ready) begin
          w_state_next = scariv_pkg::DONE;
        end else if (o_entry_ready & i_entry_picked & !w_rs_pred_mispredicted_or) begin
          w_issued_next = 1'b1;
          w_state_next = scariv_pkg::ISSUED;
        end
      end
    end
    scariv_pkg::ISSUED : begin
      if (w_entry_flush) begin
        w_state_next = scariv_pkg::SCHED_CLEAR;
        w_dead_next  = 1'b1;
      end else begin
        if (w_rs_pred_mispredicted_or) begin
          w_state_next = scariv_pkg::WAIT;
          w_issued_next = 1'b0;
          w_entry_next.rd_regs[0].predict_ready = 1'b0;
          w_entry_next.rd_regs[1].predict_ready = 1'b0;
          w_entry_next.rd_regs[2].predict_ready = 1'b0;
        end else begin
          w_state_next = scariv_pkg::SCHED_CLEAR;
        end
      end
    end // case: scariv_pkg::ISSUED
    scariv_pkg::SCHED_CLEAR : begin
      if (i_clear_entry) begin
        w_state_next = scariv_pkg::INIT;
        w_entry_next.valid = 1'b0;
      end
    end
    default : begin
// `ifdef SIMULATION
//       $fatal (0, "ALU scheduler entry reached unexpected state\n");
// `endif // SIMULATION
      w_state_next = scariv_pkg::INIT;
    end
  endcase // case (r_state)

  // BrMask update
  if (br_upd_if.update) begin
  end
end // always_comb


assign w_init_entry = scariv_bru_pkg::assign_bru_issue(i_put_data, i_cmt_id, i_grp_id,
                                                       w_rs_rel_hit, w_rs_phy_hit, w_rs_may_mispred, w_rs_rel_index,
                                                       i_basicblk_pc_vaddr);


assign w_commit_flush = commit_if.is_flushed_commit() & r_entry.valid;
assign w_br_flush     = scariv_pkg::is_br_flush_target(r_entry.cmt_id, r_entry.grp_id, br_upd_if.cmt_id, br_upd_if.grp_id,
                                                     br_upd_if.dead, br_upd_if.mispredict) & br_upd_if.update & r_entry.valid;
assign w_entry_flush = w_commit_flush | w_br_flush;

assign w_load_commit_flush = commit_if.is_flushed_commit() & i_put;
assign w_load_br_flush = scariv_pkg::is_br_flush_target(i_cmt_id, i_grp_id, br_upd_if.cmt_id, br_upd_if.grp_id,
                                                        br_upd_if.dead, br_upd_if.mispredict) & br_upd_if.update;
assign w_load_entry_flush = w_load_commit_flush | w_load_br_flush | i_dead_put;

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

assign w_oldest_ready = 1'b1;
assign w_pc_update_before_entry = 1'b0;


assign o_entry_valid = r_entry.valid;
assign o_entry_ready = r_entry.valid & (r_state == scariv_pkg::WAIT) &
                       w_oldest_ready & !w_pc_update_before_entry & all_operand_ready(r_entry);
assign o_entry       = r_entry;

assign o_issue_succeeded = (r_state == scariv_pkg::SCHED_CLEAR);

endmodule // scariv_bru_issue_entry
