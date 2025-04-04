// ------------------------------------------------------------------------
// NAME : scariv_csu_issue_entry
// TYPE : module
// ------------------------------------------------------------------------
// Scheduler entry for CSU
// ------------------------------------------------------------------------
//
// ------------------------------------------------------------------------

module scariv_csu_issue_entry
  #(
    parameter IS_BRANCH = 1'b0,
    parameter NUM_OPERANDS = 2
    )
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
   input logic                i_inst_oldest,

   output logic               o_entry_valid,
   /* verilator lint_off UNOPTFLAT */
   output logic               o_entry_ready,
   output scariv_pkg::issue_t o_entry,

   /* Forwarding path */
   phy_wr_if.slave   phy_wr_if [scariv_pkg::TGT_BUS_SIZE],

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
scariv_pkg::issue_t r_entry;
/* verilator lint_off UNOPTFLAT */
scariv_pkg::issue_t w_entry_next;
scariv_pkg::issue_t w_init_entry;

logic    w_oldest_ready;

scariv_pkg::rnid_t w_rs_rnid[NUM_OPERANDS];
scariv_pkg::reg_t  w_rs_type[NUM_OPERANDS];
logic [NUM_OPERANDS-1: 0] w_rs_phy_hit;
scariv_pkg::rel_bus_idx_t w_rs_rel_index[NUM_OPERANDS];

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
  ret = (!entry.rd_regs[0].valid | entry.rd_regs[0].valid  & (entry.rd_regs[0].ready | entry.rd_regs[0].predict_ready)) &
        (!entry.rd_regs[1].valid | entry.rd_regs[1].valid  & (entry.rd_regs[1].ready | entry.rd_regs[1].predict_ready)) &
        (!entry.rd_regs[2].valid | entry.rd_regs[2].valid  & (entry.rd_regs[2].ready | entry.rd_regs[2].predict_ready));
  return ret;
endfunction // all_operand_ready

generate for (genvar rs_idx = 0; rs_idx < NUM_OPERANDS; rs_idx++) begin : rs_loop
  assign w_rs_rnid[rs_idx] = i_put ? i_put_data.rd_regs[rs_idx].rnid : r_entry.rd_regs[rs_idx].rnid;
  assign w_rs_type[rs_idx] = i_put ? i_put_data.rd_regs[rs_idx].typ  : r_entry.rd_regs[rs_idx].typ;

  select_phy_wr_bus   rs_phy_select    (.i_entry_rnid (w_rs_rnid[rs_idx]), .i_entry_type (w_rs_type[rs_idx]), .phy_wr_if   (phy_wr_if),
                                        .o_valid   (w_rs_phy_hit[rs_idx]));
  assign w_rs_rel_index[rs_idx] = 'h0;
end endgenerate

always_comb begin
  w_state_next  = r_state;
  w_dead_next   = r_dead;
  w_issued_next = r_issued;
  w_entry_next  = r_entry;

  for (int rs_idx = 0; rs_idx < NUM_OPERANDS; rs_idx++) begin
    w_entry_next.rd_regs[rs_idx].ready         = r_entry.rd_regs[rs_idx].ready | w_rs_phy_hit[rs_idx];
    w_entry_next.rd_regs[rs_idx].predict_ready = 'h0;
  end

  case (r_state)
    scariv_pkg::INIT : begin
      if (w_entry_flush) begin
        w_state_next = scariv_pkg::INIT;
      end else if (i_put) begin
        w_entry_next = w_init_entry;
        w_entry_next.oldest_valid = i_inst_oldest;
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
        end else if (o_entry_valid & o_entry_ready & i_entry_picked) begin
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
        w_state_next = scariv_pkg::SCHED_CLEAR;
      end
    end // case: scariv_pkg::ISSUED
    scariv_pkg::SCHED_CLEAR : begin
      if (i_clear_entry) begin
        w_state_next = scariv_pkg::INIT;
        w_entry_next.valid = 1'b0;
      end
    end
    default : begin
`ifdef SIMULATION
      $fatal (0, "ALU scheduler entry reached unexpected state\n");
`endif // SIMULATION
    end
  endcase // case (r_state)

  // BrMask update
  if (br_upd_if.update) begin
  end
end // always_comb


generate if (NUM_OPERANDS == 3) begin : init_entry_op3
  assign w_init_entry = scariv_pkg::assign_issue_op3(i_put_data, i_cmt_id, i_grp_id,
                                                     'h0, w_rs_phy_hit, 'h0);
end else begin
  assign w_init_entry = scariv_pkg::assign_issue_op2(i_put_data, i_cmt_id, i_grp_id,
                                                     'h0, w_rs_phy_hit, 'h0, w_rs_rel_index);
end endgenerate


assign w_commit_flush = scariv_pkg::is_flushed_commit(commit_if.commit_valid, commit_if.payload) & r_entry.valid;
assign w_br_flush     = scariv_pkg::is_br_flush_target(r_entry.cmt_id, r_entry.grp_id, br_upd_if.cmt_id, br_upd_if.grp_id,
                                                     br_upd_if.dead, br_upd_if.mispredict) & br_upd_if.update & r_entry.valid;
assign w_entry_flush = w_commit_flush | w_br_flush;

assign w_load_commit_flush = scariv_pkg::is_flushed_commit(commit_if.commit_valid, commit_if.payload) & i_put;
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

assign w_oldest_ready = ~r_entry.oldest_valid  ? 1'b1 :
                        (rob_info_if.cmt_id == r_entry.cmt_id) &
                        ((rob_info_if.done_grp_id & r_entry.grp_id-1) == r_entry.grp_id-1);
assign w_pc_update_before_entry = |((r_entry.grp_id - 1) & (rob_info_if.upd_pc_valid | rob_info_if.except_valid) & rob_info_if.done_grp_id);


assign o_entry_valid = r_entry.valid;
assign o_entry_ready = r_entry.valid & (r_state == scariv_pkg::WAIT) &
                       w_oldest_ready & !w_pc_update_before_entry & all_operand_ready(r_entry);
assign o_entry       = r_entry;

assign o_issue_succeeded = (r_state == scariv_pkg::SCHED_CLEAR);

endmodule // scariv_csu_issue_entry
