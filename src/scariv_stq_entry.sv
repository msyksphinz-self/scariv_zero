// ------------------------------------------------------------------------
// NAME : scariv_stq_entry
// TYPE : module
// ------------------------------------------------------------------------
// SCARIV Store Queue Entry
// ------------------------------------------------------------------------
//
// ------------------------------------------------------------------------

module scariv_stq_entry
  import scariv_lsu_pkg::*;
#(parameter entry_index = 0)
(
   input logic                                i_clk,
   input logic                                i_reset_n,

   // ROB notification interface
   rob_info_if.slave                           rob_info_if,

   input logic                                  i_disp_load,
   input scariv_pkg::cmt_id_t                   i_disp_cmt_id,
   input scariv_pkg::grp_id_t                   i_disp_grp_id,
   input scariv_pkg::disp_t                     i_disp,
   input logic [scariv_conf_pkg::LSU_INST_NUM-1: 0] i_disp_pipe_sel_oh,

   /* Forwarding path */
   phy_wr_if.slave                            phy_wr_in_if [scariv_pkg::TGT_BUS_SIZE],

   // Updates from LSU Pipeline EX1 stage
   input logic                                i_ex1_q_valid,
   input ex1_q_update_t                       i_ex1_q_updates,
   // Updates from LSU Pipeline EX2 stage
   input logic                                i_ex2_q_valid,
   input ex2_q_update_t                       i_ex2_q_updates,

  // rs2 store data interface
    input logic                               i_rs2_read_accepted,
    input scariv_pkg::alen_t                  i_rs2_data,

   output stq_entry_t                         o_entry,

   // Commit notification
   commit_if.monitor               commit_if,
   br_upd_if.slave                            br_upd_if,

   input logic                                i_missu_is_empty,

   output logic                               o_stbuf_req_valid,
   input logic                                i_stbuf_accept,

   input logic                                i_st_buffer_empty,

   output logic                               o_uc_write_req_valid,
   input logic                                i_uc_write_accept,

   // // Snoop Interface
   // stq_snoop_if.slave                         stq_snoop_if,

   done_if.slave    ex3_done_if,
   input logic                                     i_stq_outptr_valid,
   output logic                                    o_stq_entry_st_finish
   );

stq_entry_t                          r_entry;
/* verilator lint_off UNOPTFLAT */
stq_entry_t                          w_entry_next;
logic                                              w_entry_flush;
logic                                              w_commit_flush;
logic                                              w_br_flush;
logic                                              w_rob_except_flush;
logic                                              w_load_br_flush;
logic                                              w_load_commit_flush;
logic                                              w_ready_to_mv_stbuf;

scariv_pkg::rnid_t                                 w_rs2_rnid;
scariv_pkg::reg_t                                  w_rs2_type;
logic                                              w_rs2_phy_hit;
logic                                              w_entry_rs2_ready_next;
logic                                              r_rs2_read_accepted;


assign  o_entry = r_entry;

assign w_rs2_rnid = i_disp_load ? i_disp.rd_regs[1].rnid : r_entry.inst.rd_reg.rnid;
assign w_rs2_type = i_disp_load ? i_disp.rd_regs[1].typ  : r_entry.inst.rd_reg.typ;

select_phy_wr_bus rs2_phy_select (.i_entry_rnid (w_rs2_rnid), .i_entry_type (w_rs2_type), .phy_wr_if (phy_wr_in_if),
                                  .o_valid (w_rs2_phy_hit));

assign w_rob_except_flush = (rob_info_if.cmt_id == r_entry.inst.cmt_id) & |(rob_info_if.except_valid & rob_info_if.done_grp_id & r_entry.inst.grp_id);
assign w_commit_flush = commit_if.is_commit_flush_target(r_entry.inst.cmt_id, r_entry.inst.grp_id) & r_entry.is_valid;
assign w_br_flush     = scariv_pkg::is_br_flush_target(r_entry.inst.cmt_id, r_entry.inst.grp_id, br_upd_if.cmt_id, br_upd_if.grp_id,
                                                       br_upd_if.dead, br_upd_if.mispredict) & br_upd_if.update & r_entry.is_valid;
assign w_entry_flush  = w_commit_flush | w_br_flush | w_rob_except_flush;

assign w_load_br_flush = scariv_pkg::is_br_flush_target(i_disp_cmt_id, i_disp_grp_id, br_upd_if.cmt_id, br_upd_if.grp_id,
                                                        br_upd_if.dead, br_upd_if.mispredict) & br_upd_if.update;
assign w_load_commit_flush = commit_if.is_commit_flush_target(i_disp_cmt_id, i_disp_grp_id);

assign w_entry_rs2_ready_next = r_entry.inst.rd_reg.ready | w_rs2_phy_hit;

// assign w_ready_to_mv_stbuf = commit_if.commit_valid & (commit_if.payload.cmt_id == r_entry.inst.cmt_id);
scariv_pkg::grp_id_t w_prev_grp_id_mask;
assign w_prev_grp_id_mask = r_entry.inst.grp_id-1;
assign w_ready_to_mv_stbuf = (rob_info_if.cmt_id == r_entry.inst.cmt_id) &
                             |(rob_info_if.done_grp_id & ~rob_info_if.except_valid & r_entry.inst.grp_id) &
                             ((w_prev_grp_id_mask & rob_info_if.done_grp_id) == w_prev_grp_id_mask);

assign o_stbuf_req_valid = r_entry.is_valid & r_entry.is_committed & r_entry.is_rs2_get &
                           r_entry.paddr_valid & ~r_entry.is_uc &
                           ~r_entry.st_buf_finished &
                           ((r_entry.rmwop != decoder_lsu_ctrl_pkg::RMWOP__) ?
                            (r_entry.rmwop != decoder_lsu_ctrl_pkg::RMWOP_SC | r_entry.paddr_valid) & i_st_buffer_empty & i_stq_outptr_valid :
                            1'b1);

assign o_uc_write_req_valid = r_entry.is_valid & r_entry.is_committed & r_entry.paddr_valid & r_entry.is_uc;

assign o_stq_entry_st_finish = r_entry.is_valid &
                               (r_entry.st_buf_finished |
                                r_entry.is_committed & (r_entry.rmwop == decoder_lsu_ctrl_pkg::RMWOP_SC) & ~r_entry.paddr_valid |  // SC.W/D condition failed.
                                r_entry.dead) &
                               i_stq_outptr_valid;

always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_entry.is_valid <= 1'b0;
  end else begin
    r_entry <= w_entry_next;

    r_rs2_read_accepted <= r_entry.inst.rd_reg.ready & i_rs2_read_accepted;
  end
end

always_comb begin
  w_entry_next = r_entry;

  w_entry_next.inst.rd_reg.ready = w_entry_rs2_ready_next | r_entry.inst.rd_reg.ready;
  if (~w_entry_next.is_rs2_get) begin
    if (r_rs2_read_accepted) begin
      w_entry_next.rs2_data   = i_rs2_data;
      w_entry_next.is_rs2_get = 1'b1;
    end
  end

  if (!r_entry.is_valid) begin
    if (i_disp_load) begin
      w_entry_next = assign_stq_disp(i_disp, i_disp_cmt_id, i_disp_grp_id,
                                     1 << (entry_index % scariv_conf_pkg::LSU_INST_NUM),
                                     w_rs2_phy_hit);
      if (w_load_br_flush | w_load_commit_flush) begin
        w_entry_next.dead = 1'b1;
      end
    end
  end else if (r_entry.is_committed | r_entry.dead) begin
    if (o_stq_entry_st_finish) begin
      w_entry_next.is_valid = 1'b0;
    end
    if (o_stbuf_req_valid & i_stbuf_accept |
        o_uc_write_req_valid & i_uc_write_accept) begin
      w_entry_next.st_buf_finished = 1'b1;
    end
  end else begin
    if (w_entry_flush) begin
      w_entry_next.dead = 1'b1;
    end else if (~r_entry.paddr_valid & i_ex1_q_valid & (i_ex1_q_updates.hazard_typ == EX1_HAZ_NONE)) begin
      w_entry_next.addr         = i_ex1_q_updates.paddr;
      w_entry_next.paddr_valid  = (i_ex1_q_updates.hazard_typ != EX1_HAZ_TLB_MISS) & ~i_ex1_q_updates.tlb_except_valid;
      w_entry_next.size         = i_ex1_q_updates.size;
      w_entry_next.is_uc        = i_ex1_q_updates.tlb_uc & ~i_ex1_q_updates.tlb_except_valid;
      w_entry_next.rmwop        = i_ex1_q_updates.rmwop;
    end else if ((r_entry.rmwop == decoder_lsu_ctrl_pkg::RMWOP_SC) & i_ex2_q_valid) begin
      w_entry_next.paddr_valid = r_entry.paddr_valid & i_ex2_q_updates.success;
    end
    if (w_ready_to_mv_stbuf) begin
      w_entry_next.is_committed = 1'b1;
    end
  end
end // always_comb

function automatic stq_entry_t assign_stq_disp (scariv_pkg::disp_t in,
                                                scariv_pkg::cmt_id_t cmt_id,
                                                scariv_pkg::grp_id_t grp_id,
                                                logic [scariv_conf_pkg::LSU_INST_NUM-1: 0] pipe_sel_oh,
                                                logic rs2_phy_hit);
  stq_entry_t ret;

  ret = 'h0;

  ret.is_valid  = 1'b1;

  ret.inst.cmt_id = cmt_id;
  ret.inst.grp_id = grp_id;

  // for (int rs_idx = 0; rs_idx < 2; rs_idx++) begin
  //   ret.inst.rd_regs[rs_idx].valid         = in.rd_regs[rs_idx].valid;
  //   ret.inst.rd_regs[rs_idx].typ           = in.rd_regs[rs_idx].typ;
  //   ret.inst.rd_regs[rs_idx].regidx        = in.rd_regs[rs_idx].regidx;
  //   ret.inst.rd_regs[rs_idx].rnid          = in.rd_regs[rs_idx].rnid;
  //   ret.inst.rd_regs[rs_idx].ready         = in.rd_regs[rs_idx].ready | rs_rel_hit[rs_idx] & ~rs_may_mispred[rs_idx] | rs_phy_hit[rs_idx];
  //   ret.inst.rd_regs[rs_idx].predict_ready = rs_rel_hit[rs_idx] & rs_may_mispred[rs_idx];
  // end

  ret.inst.rd_reg.valid         = in.rd_regs[1].valid;
  ret.inst.rd_reg.typ           = in.rd_regs[1].typ;
  ret.inst.rd_reg.regidx        = in.rd_regs[1].regidx;
  ret.inst.rd_reg.rnid          = in.rd_regs[1].rnid;
  ret.inst.rd_reg.ready         = in.rd_regs[1].ready | rs2_phy_hit;
  ret.inst.rd_reg.predict_ready = 1'b0;

  // ret.inst.wr_reg.valid  = in.wr_reg.valid;
  // ret.inst.wr_reg.typ    = in.wr_reg.typ;
  // ret.inst.wr_reg.regidx = in.wr_reg.regidx;
  // ret.inst.wr_reg.rnid   = in.wr_reg.rnid;

  // for (int rs_idx = 2; rs_idx < 3; rs_idx++) begin
  //   ret.inst.rd_regs[rs_idx].valid = 1'b0;
  // end

`ifdef SIMULATION
  ret.inst.sim_inst   = in.inst;
  ret.inst.sim_cat    = in.cat;

  ret.kanata_id = in.kanata_id;
`endif // SIMULATION

  return ret;
endfunction // assign_stq_disp

endmodule // scariv_stq_entry
