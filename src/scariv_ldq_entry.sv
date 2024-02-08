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

 input logic                                     i_entry_picked,

  input logic                        i_ex2_q_valid,
  input scariv_lsu_pkg::ldq_update_t i_ex2_q_updates,

 input                                           missu_resolve_t i_missu_resolve,
 input logic                                     i_missu_is_full,
 // Commit notification
 commit_if.monitor                               commit_if,
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

scariv_pkg::rnid_t                                 w_rs_rnid[2];
scariv_pkg::reg_t                                  w_rs_type[2];
logic [ 1: 0]                                    w_rs_rel_hit;
logic [ 1: 0]                                    w_rs_may_mispred;
logic [ 1: 0]                                    w_rs_phy_hit;
logic [ 1: 0]                                    w_rs_mispredicted;

assign o_entry = r_entry;

assign w_commit_flush = commit_if.is_flushed_commit() & r_entry.is_valid;
assign w_br_flush     = scariv_pkg::is_br_flush_target(r_entry.inst.cmt_id, r_entry.inst.grp_id, br_upd_if.cmt_id, br_upd_if.grp_id,
                                                     br_upd_if.dead, br_upd_if.mispredict) & br_upd_if.update & r_entry.is_valid;
assign w_entry_flush  = w_commit_flush | w_br_flush;


assign w_load_commit_flush = commit_if.is_flushed_commit();
assign w_load_br_flush = scariv_pkg::is_br_flush_target(i_disp_cmt_id, i_disp_grp_id, br_upd_if.cmt_id, br_upd_if.grp_id,
                                                      br_upd_if.dead, br_upd_if.mispredict) & br_upd_if.update;
assign w_load_flush = w_load_commit_flush | w_load_br_flush;

assign w_dead_state_clear = commit_if.commit_valid & (commit_if.payload.cmt_id == r_entry.inst.cmt_id);

assign o_entry_finish = r_entry.is_valid & (r_entry.is_committed | r_entry.dead) & i_ldq_outptr_valid;

assign w_entry_commit = commit_if.commit_valid & (commit_if.payload.cmt_id == r_entry.inst.cmt_id);

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

  end else begin
    r_entry <= w_entry_next;
  end
end

always_comb begin

  w_entry_next = r_entry;

//  for (int rs_idx = 0; rs_idx < 2; rs_idx++) begin
//    w_entry_next.inst.rd_regs[rs_idx].ready = r_entry.inst.rd_regs[rs_idx].ready | w_rs_phy_hit[rs_idx];
//    w_entry_next.inst.rd_regs[rs_idx].predict_ready = w_rs_rel_hit[rs_idx] & w_rs_may_mispred[rs_idx];
//  end

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
    end else if (~r_entry.paddr_valid & i_ex2_q_valid) begin
      w_entry_next.addr        = i_ex2_q_updates.paddr;
      w_entry_next.size        = i_ex2_q_updates.size;
      w_entry_next.paddr_valid = 1'b1;
      w_entry_next.is_get_data = 1'b1;
    end

    if (w_entry_commit) begin
      w_entry_next.is_committed = 1'b1;
    end
  end
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

  ret.is_get_data = 1'b0;
  ret.paddr_valid = 1'b0;

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
