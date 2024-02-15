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

   // Updates from LSU Pipeline EX2 stage
   input logic                            i_ex1_q_valid,
   input scariv_lsu_pkg::stq_ex1_update_t i_ex1_q_updates,
   input logic                            i_ex2_q_valid,
   input scariv_lsu_pkg::stq_ex2_update_t i_ex2_q_updates,

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

assign  o_entry = r_entry;

assign w_rs2_rnid = i_disp_load ? i_disp.rd_regs[1].rnid : r_entry.inst.rd_reg.rnid;
assign w_rs2_type = i_disp_load ? i_disp.rd_regs[1].typ  : r_entry.inst.rd_reg.typ;

select_phy_wr_bus rs2_phy_select (.i_entry_rnid (w_rs2_rnid), .i_entry_type (w_rs2_type), .phy_wr_if (phy_wr_in_if),
                                  .o_valid (w_rs2_phy_hit));

assign  o_entry = r_entry;

assign w_rob_except_flush = (rob_info_if.cmt_id == r_entry.inst.cmt_id) & (|rob_info_if.except_valid) & (rob_info_if.except_valid <= r_entry.inst.grp_id);
assign w_commit_flush = commit_if.is_commit_flush_target(r_entry.inst.cmt_id, r_entry.inst.grp_id) & r_entry.is_valid;
assign w_br_flush     = scariv_pkg::is_br_flush_target(r_entry.inst.cmt_id, r_entry.inst.grp_id, br_upd_if.cmt_id, br_upd_if.grp_id,
                                                       br_upd_if.dead, br_upd_if.mispredict) & br_upd_if.update & r_entry.is_valid;
assign w_entry_flush  = w_commit_flush | w_br_flush | w_rob_except_flush;

assign w_load_br_flush = scariv_pkg::is_br_flush_target(i_disp_cmt_id, i_disp_grp_id, br_upd_if.cmt_id, br_upd_if.grp_id,
                                                        br_upd_if.dead, br_upd_if.mispredict) & br_upd_if.update;
assign w_load_commit_flush = commit_if.is_commit_flush_target(i_disp_cmt_id, i_disp_grp_id);

// assign w_ready_to_mv_stbuf = commit_if.commit_valid & (commit_if.payload.cmt_id == r_entry.inst.cmt_id);
scariv_pkg::grp_id_t w_prev_grp_id_mask;
assign w_prev_grp_id_mask = r_entry.inst.grp_id-1;
assign w_ready_to_mv_stbuf = (rob_info_if.cmt_id == r_entry.inst.cmt_id) &
                             |(rob_info_if.done_grp_id & ~rob_info_if.except_valid & r_entry.inst.grp_id) &
                             ((w_prev_grp_id_mask & rob_info_if.done_grp_id) == w_prev_grp_id_mask);

assign o_stbuf_req_valid = r_entry.is_valid & r_entry.is_committed & ~r_entry.dead &
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
  end
end

always_comb begin
  w_entry_next = r_entry;

  if (~w_entry_next.is_rs2_get) begin
    w_entry_next.inst.rd_reg.ready = w_rs2_phy_hit | r_entry.inst.rd_reg.ready;
    w_entry_next.rs2_read_accepted = i_rs2_read_accepted;
    if (r_entry.rs2_read_accepted) begin
      w_entry_next.rs2_data   = i_rs2_data;
      w_entry_next.is_rs2_get = 1'b1;
    end
  end

  if (!r_entry.is_valid) begin
    if (i_disp_load) begin
      w_entry_next = assign_stq_disp(i_disp, i_disp_cmt_id, i_disp_grp_id, w_rs2_phy_hit);
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
    end else if (~r_entry.paddr_valid & i_ex1_q_valid) begin
      w_entry_next.addr         = i_ex1_q_updates.paddr;
      w_entry_next.size         = i_ex1_q_updates.size;
      w_entry_next.is_uc        = i_ex1_q_updates.is_uc;
      w_entry_next.rmwop        = i_ex1_q_updates.rmwop;
      w_entry_next.paddr_valid  = (i_ex1_q_updates.rmwop != decoder_lsu_ctrl_pkg::RMWOP_SC) ? 1'b1 : i_ex2_q_updates.success;
    // end else if (r_entry.paddr_valid & i_ex2_q_valid) begin
    //   w_entry_next.paddr_valid  = r_entry.rmwop == decoder_lsu_ctrl_pkg::RMWOP_SC ? i_ex2_q_updates.success : r_entry.paddr_valid;
    end

    if (w_ready_to_mv_stbuf) begin
      w_entry_next.is_committed = 1'b1;
    end
  end
end // always_comb

function automatic stq_entry_t assign_stq_disp (scariv_pkg::disp_t in,
                                                scariv_pkg::cmt_id_t cmt_id,
                                                scariv_pkg::grp_id_t grp_id,
                                                logic rs2_phy_hit);
  stq_entry_t ret;

  ret = 'h0;

  ret.is_valid  = 1'b1;

  ret.inst.cmt_id = cmt_id;
  ret.inst.grp_id = grp_id;

  ret.inst.rd_reg.valid         = in.rd_regs[1].valid;
  ret.inst.rd_reg.typ           = in.rd_regs[1].typ;
  ret.inst.rd_reg.regidx        = in.rd_regs[1].regidx;
  ret.inst.rd_reg.rnid          = in.rd_regs[1].rnid;
  ret.inst.rd_reg.ready         = in.rd_regs[1].ready | rs2_phy_hit;
  ret.inst.rd_reg.predict_ready = 1'b0;

  ret.rs2_read_accepted = 1'b0;
  ret.is_rs2_get = 1'b0;

`ifdef SIMULATION
  ret.inst.sim_inst   = in.inst;
  ret.inst.sim_cat    = in.cat;

  ret.kanata_id = in.kanata_id;
`endif // SIMULATION

  return ret;
endfunction // assign_stq_disp

endmodule // scariv_stq_entry
