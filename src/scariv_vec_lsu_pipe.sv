// ------------------------------------------------------------------------
// NAME : scariv_vec_lsu_pipe
// TYPE : module
// ------------------------------------------------------------------------
// LSU Pipeline
// ------------------------------------------------------------------------
//
// ------------------------------------------------------------------------

module scariv_vec_lsu_pipe
  import decoder_vlsu_ctrl_pkg::*;
  import scariv_lsu_pkg::*;
(
 input logic i_clk,
 input logic i_reset_n,

 /* SFENCE update information */
 sfence_if.slave    sfence_if,
 /* CSR information */
 csr_info_if.slave  csr_info,
 /* Page Table Walk I/O */
 tlb_ptw_if.master ptw_if,

 // Commit notification
 input scariv_pkg::commit_blk_t i_commit,
 br_upd_if.slave                br_upd_if,

 input scariv_vec_pkg::issue_t  i_ex0_issue,
 input scariv_pkg::phy_wr_t ex1_i_phy_wr[scariv_pkg::TGT_BUS_SIZE],

 regread_if.master      ex0_xpr_regread_rs1,

 vec_regread_if.master  vec_phy_rd_if[2],
 vec_regread_if.master  vec_phy_old_wr_if,
 vec_regwrite_if.master vec_phy_wr_if ,
 vec_phy_fwd_if.master  vec_phy_fwd_if[1],

 output logic           o_tlb_resolve,

 /* EX1 L1D read stage */
 l1d_rd_if.master       l1d_rd_if,
 /* EX2 L1D MSHR control */
 l1d_missu_if.master    l1d_missu_if,

 /* Interface for Replay Queue */
 lsu_pipe_haz_if.master lsu_pipe_haz_if,

 vlsu_lsq_req_if.master vlsu_ldq_req_if,
 vlsu_lsq_req_if.master vlsu_stq_req_if,

 output scariv_pkg::done_rpt_t o_done_report
 );

logic   w_commit_flush;

scariv_vec_pkg::issue_t  w_ex0_issue;
decoder_vlsu_ctrl_pkg::pipe_ctrl_t w_ex0_pipe_ctrl;
logic                    w_ex0_br_flush;

scariv_vec_pkg::issue_t  r_ex1_issue;
scariv_vec_pkg::issue_t  w_ex1_issue_next;
riscv_pkg::xlen_t        r_ex1_rs1_data;
scariv_pkg::vaddr_t      w_ex1_vaddr;
tlb_req_t                w_ex1_tlb_req;
tlb_resp_t               w_ex1_tlb_resp;
decoder_vlsu_ctrl_pkg::pipe_ctrl_t              r_ex1_pipe_ctrl;
scariv_pkg::maxaddr_t    w_ex1_addr; // VADDR(when exception) and PADDR
scariv_vec_pkg::dlen_t   r_ex1_vpr_wr_old_data;
scariv_vec_pkg::dlen_t   r_ex1_vpr_wr_old_data_step0;
scariv_vec_pkg::dlen_t   r_ex1_vpr_rs_data[2];
logic                    w_ex1_br_flush;
logic                    w_ex1_ld_except_valid;
logic                    w_ex1_st_except_valid;
scariv_pkg::except_t     w_ex1_tlb_except_type;

scariv_vec_pkg::issue_t  r_ex2_issue;
scariv_vec_pkg::issue_t  w_ex2_issue_next;
scariv_pkg::maxaddr_t    r_ex2_addr;
decoder_vlsu_ctrl_pkg::pipe_ctrl_t              r_ex2_pipe_ctrl;
logic                    r_ex2_except_valid;
scariv_pkg::except_t     r_ex2_except_type;
logic                    w_ex2_br_flush;
logic                    w_ex2_l1d_missed;
logic                    w_ex2_l1d_conflicted;
logic                    w_ex2_hazard;
logic                    r_ex2_is_uc;
scariv_lsu_pkg::dc_data_t w_ex2_l1d_data;

scariv_vec_pkg::issue_t  r_ex3_issue;
scariv_vec_pkg::issue_t  w_ex3_issue_next;
decoder_vlsu_ctrl_pkg::pipe_ctrl_t              r_ex3_pipe_ctrl;
logic                    r_ex3_except_valid;
scariv_pkg::except_t     r_ex3_except_type;
scariv_pkg::maxaddr_t    r_ex3_addr;
logic                    r_ex3_mis_valid;
scariv_vec_pkg::dlen_t   r_ex3_aligned_data;

assign w_commit_flush = scariv_pkg::is_flushed_commit(i_commit);


// ---------------------
// EX0
// ---------------------

decoder_vlsu_ctrl u_pipe_ctrl (
  .inst (i_ex0_issue.inst),
  .op   (w_ex0_pipe_ctrl.op),
  .size (w_ex0_pipe_ctrl.size)
);

assign w_ex0_br_flush = scariv_pkg::is_br_flush_target(w_ex0_issue.cmt_id, w_ex0_issue.grp_id, br_upd_if.cmt_id, br_upd_if.grp_id,
                                                       br_upd_if.dead, br_upd_if.mispredict) & br_upd_if.update & w_ex0_issue.valid;

assign ex0_xpr_regread_rs1.valid = i_ex0_issue.valid & (i_ex0_issue.rd_regs[0].typ == scariv_pkg::GPR) & i_ex0_issue.rd_regs[0].valid;
assign ex0_xpr_regread_rs1.rnid  = i_ex0_issue.rd_regs[0].rnid;

generate for (genvar rs_idx = 0; rs_idx < 2; rs_idx++) begin : rs_vec_rd_loop
  assign vec_phy_rd_if[rs_idx].valid = i_ex0_issue.valid & (i_ex0_issue.rd_regs[rs_idx].typ == scariv_pkg::VPR) & i_ex0_issue.rd_regs[rs_idx].valid;
  assign vec_phy_rd_if[rs_idx].rnid  = i_ex0_issue.rd_regs[rs_idx].rnid;
  assign vec_phy_rd_if[rs_idx].pos   = i_ex0_issue.vec_step_index;
end endgenerate

// ---------------------
// EX1
// ---------------------

always_comb begin
  w_ex1_issue_next = i_ex0_issue;
  w_ex1_issue_next.valid = i_ex0_issue.valid & !w_commit_flush & !w_ex0_br_flush;
end

always_ff @(posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_ex1_issue.valid <= 1'b0;
  end else begin
    r_ex1_issue     <= w_ex1_issue_next;
    r_ex1_pipe_ctrl <= w_ex0_pipe_ctrl;

    r_ex1_rs1_data        <= ex0_xpr_regread_rs1.data;
    r_ex1_vpr_rs_data[0]  <= vec_phy_rd_if[0].data;
    r_ex1_vpr_rs_data[1]  <= vec_phy_rd_if[1].data;
    r_ex1_vpr_wr_old_data <= vec_phy_old_wr_if.data;

    if (i_ex0_issue.vec_step_index == 'h0) begin
      r_ex1_vpr_wr_old_data_step0 <= vec_phy_old_wr_if.data;
    end
  end // else: !if(!i_reset_n)
end // always_ff @ (posedge i_clk, negedge i_reset_n)


assign w_ex1_tlb_req.valid       = r_ex1_issue.valid; //  & ~r_ex1_issue.paddr_valid;
assign w_ex1_tlb_req.cmd         = r_ex1_pipe_ctrl.op == decoder_vlsu_ctrl_pkg::OP_LOAD ? M_XRD : M_XWR;
assign w_ex1_tlb_req.vaddr       = w_ex1_vaddr;
assign w_ex1_tlb_req.size        = r_ex1_pipe_ctrl.size == decoder_vlsu_ctrl_pkg::SIZE_DW ? 8 :
                                   r_ex1_pipe_ctrl.size == decoder_vlsu_ctrl_pkg::SIZE_W  ? 4 :
                                   r_ex1_pipe_ctrl.size == decoder_vlsu_ctrl_pkg::SIZE_H  ? 2 :
                                   r_ex1_pipe_ctrl.size == decoder_vlsu_ctrl_pkg::SIZE_B  ? 1 : 0;
assign w_ex1_tlb_req.passthrough = 1'b0;
assign w_ex1_addr = w_ex1_tlb_resp.paddr;

assign w_ex1_ld_except_valid = (r_ex1_pipe_ctrl.op == decoder_vlsu_ctrl_pkg::OP_LOAD)  & w_ex1_tlb_req.valid & (w_ex1_tlb_resp.pf.ld | w_ex1_tlb_resp.ae.ld | w_ex1_tlb_resp.ma.ld);
assign w_ex1_st_except_valid = (r_ex1_pipe_ctrl.op == decoder_vlsu_ctrl_pkg::OP_STORE) & w_ex1_tlb_req.valid & (w_ex1_tlb_resp.pf.st | w_ex1_tlb_resp.ae.st | w_ex1_tlb_resp.ma.st);
assign w_ex1_tlb_except_type = (r_ex1_pipe_ctrl.op == decoder_vlsu_ctrl_pkg::OP_LOAD)  & w_ex1_tlb_resp.ma.ld ? scariv_pkg::LOAD_ADDR_MISALIGN :
                               (r_ex1_pipe_ctrl.op == decoder_vlsu_ctrl_pkg::OP_LOAD)  & w_ex1_tlb_resp.pf.ld ? scariv_pkg::LOAD_PAGE_FAULT    :  // PF<-->AE priority is opposite, TLB generate
                               (r_ex1_pipe_ctrl.op == decoder_vlsu_ctrl_pkg::OP_LOAD)  & w_ex1_tlb_resp.ae.ld ? scariv_pkg::LOAD_ACC_FAULT     :  // PF and AE same time, PF is at first
                               (r_ex1_pipe_ctrl.op == decoder_vlsu_ctrl_pkg::OP_STORE) & w_ex1_tlb_resp.ma.st ? scariv_pkg::STAMO_ADDR_MISALIGN:
                               (r_ex1_pipe_ctrl.op == decoder_vlsu_ctrl_pkg::OP_STORE) & w_ex1_tlb_resp.pf.st ? scariv_pkg::STAMO_PAGE_FAULT   :  // PF and AE same time, PF is at first
                               (r_ex1_pipe_ctrl.op == decoder_vlsu_ctrl_pkg::OP_STORE) & w_ex1_tlb_resp.ae.st ? scariv_pkg::STAMO_ACC_FAULT    :  // PF<-->AE priority is opposite, TLB generate
                               scariv_pkg::SILENT_FLUSH;

scariv_vlsu_address_gen
u_address_gen
  (
   .i_clk     (i_clk),
   .i_reset_n (i_reset_n),

   .i_rs1_base (r_ex1_rs1_data),
   .o_vaddr    (w_ex1_vaddr)
   );

// TLB
tlb
  #(.USING_VM(1'b1))
u_tlb
(
 .i_clk    (i_clk),
 .i_reset_n(i_reset_n),

 .i_kill   (1'b0),
 .sfence_if(sfence_if),

 .i_csr_update (csr_info.update),
 .i_status_prv (csr_info.mstatus[`MSTATUS_MPRV] ? csr_info.mstatus[`MSTATUS_MPP] : csr_info.priv),
 .i_csr_status (csr_info.mstatus),
 .i_csr_satp   (csr_info.satp   ),

 .i_tlb_req (w_ex1_tlb_req ),
 .o_tlb_ready(),
 .o_tlb_resp(w_ex1_tlb_resp),

 .o_tlb_update(o_tlb_resolve),
 .o_tlb_resp_miss (),

 .ptw_if (ptw_if)
 );

assign l1d_rd_if.s0_valid         = r_ex1_issue.valid &
                                    (r_ex1_pipe_ctrl.op == decoder_vlsu_ctrl_pkg::OP_LOAD);
assign l1d_rd_if.s0_paddr         = {w_ex1_addr[riscv_pkg::PADDR_W-1:$clog2(DCACHE_DATA_B_W)], {$clog2(DCACHE_DATA_B_W){1'b0}}};
assign l1d_rd_if.s0_high_priority = 1'b0;  // r_ex1_issue.l1d_high_priority;

// ---------------------
// EX2
// ---------------------

assign w_ex1_br_flush = scariv_pkg::is_br_flush_target(r_ex1_issue.cmt_id, r_ex1_issue.grp_id, br_upd_if.cmt_id, br_upd_if.grp_id,
                                                       br_upd_if.dead, br_upd_if.mispredict) & br_upd_if.update & r_ex1_issue.valid;

always_comb begin
  w_ex2_issue_next       = r_ex1_issue;
  w_ex2_issue_next.valid = r_ex1_issue.valid & ~w_commit_flush & ~w_ex1_br_flush;
end

always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_ex2_issue.valid <= 1'b0;
  end else begin
    r_ex2_issue        <= w_ex2_issue_next;
    r_ex2_pipe_ctrl    <= r_ex1_pipe_ctrl;
    r_ex2_addr         <= w_ex1_ld_except_valid | w_ex1_st_except_valid ? w_ex1_vaddr : w_ex1_addr;
    r_ex2_is_uc        <= !w_ex1_tlb_resp.cacheable;

    r_ex2_except_valid <= w_ex1_ld_except_valid | w_ex1_st_except_valid;
    r_ex2_except_type  <= w_ex1_tlb_except_type;
  end // else: !if(!i_reset_n)
end // always_ff @ (posedge i_clk, negedge i_reset_n)

assign w_ex2_l1d_data   = l1d_rd_if.s1_data;
assign w_ex2_l1d_missed     = r_ex2_issue.valid & l1d_rd_if.s1_miss & ~l1d_rd_if.s1_conflict;
assign w_ex2_l1d_conflicted = r_ex2_issue.valid & l1d_rd_if.s1_conflict;
assign w_ex2_hazard         = w_ex2_l1d_missed | w_ex2_l1d_conflicted;

assign l1d_missu_if.load              = w_ex2_l1d_missed &
                                        !r_ex2_except_valid & !(l1d_rd_if.s1_conflict | l1d_rd_if.s1_hit);
assign l1d_missu_if.req_payload.paddr = r_ex2_addr;
assign l1d_missu_if.req_payload.is_uc = r_ex2_is_uc;
assign l1d_missu_if.req_payload.way   = l1d_rd_if.s1_hit_way;

// Interface to Replay Queue
assign lsu_pipe_haz_if.valid                  = r_ex2_issue.valid & ~r_ex2_except_valid & w_ex2_hazard & ~w_commit_flush & ~w_ex2_br_flush;
assign lsu_pipe_haz_if.payload.inst           = r_ex2_issue.inst;
assign lsu_pipe_haz_if.payload.cmt_id         = r_ex2_issue.cmt_id;
assign lsu_pipe_haz_if.payload.grp_id         = r_ex2_issue.grp_id;
assign lsu_pipe_haz_if.payload.cat            = r_ex2_issue.cat;
assign lsu_pipe_haz_if.payload.oldest_valid   = 1'b0;
assign lsu_pipe_haz_if.payload.hazard_typ     = l1d_rd_if.s1_conflict ? EX2_HAZ_L1D_CONFLICT : EX2_HAZ_MISSU_ASSIGNED;
assign lsu_pipe_haz_if.payload.rd_reg         = r_ex2_issue.rd_regs[0];
assign lsu_pipe_haz_if.payload.wr_reg         = r_ex2_issue.wr_reg;
assign lsu_pipe_haz_if.payload.paddr          = r_ex2_addr;
assign lsu_pipe_haz_if.payload.is_uc          = 1'b0;
assign lsu_pipe_haz_if.payload.hazard_index   = l1d_missu_if.resp_payload.missu_index_oh;

// ---------------------
// EX3
// ---------------------
assign w_ex2_br_flush = scariv_pkg::is_br_flush_target(r_ex2_issue.cmt_id, r_ex2_issue.grp_id, br_upd_if.cmt_id, br_upd_if.grp_id,
                                                       br_upd_if.dead, br_upd_if.mispredict) & br_upd_if.update & r_ex2_issue.valid;

always_comb begin
  w_ex3_issue_next       = r_ex2_issue;
  w_ex3_issue_next.valid = r_ex2_issue.valid & ~w_ex2_hazard & ~w_commit_flush & ~w_ex2_br_flush;
end

always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_ex3_issue.valid <= 1'b0;
  end else begin
    r_ex3_issue     <= w_ex3_issue_next;
    r_ex3_pipe_ctrl <= r_ex2_pipe_ctrl;
    r_ex3_addr      <= r_ex2_addr;
    r_ex3_mis_valid <= w_ex2_hazard;
    r_ex3_aligned_data <= w_ex2_l1d_data >> {r_ex2_addr[$clog2(DCACHE_DATA_B_W)-1: 0], 3'b000};

    r_ex3_except_valid <= r_ex2_except_valid;
    r_ex3_except_type  <= r_ex2_except_type;
  end
end


assign o_done_report.valid                = r_ex3_issue.valid;
assign o_done_report.cmt_id               = r_ex3_issue.cmt_id;
assign o_done_report.grp_id               = r_ex3_issue.grp_id;
assign o_done_report.except_valid         = r_ex3_except_valid;
assign o_done_report.except_type          = r_ex3_except_type;
assign o_done_report.except_tval          = {{(riscv_pkg::XLEN_W-riscv_pkg::VADDR_W){r_ex3_addr[riscv_pkg::VADDR_W-1]}}, r_ex3_addr[riscv_pkg::VADDR_W-1: 0]};
// assign o_done_report.another_flush_valid  = 'h0; // ldq_haz_check_if.ex3_haz_valid;
// assign o_done_report.another_flush_cmt_id = 'h0; // ldq_haz_check_if.ex3_haz_cmt_id;
// assign o_done_report.another_flush_grp_id = 'h0; // ldq_haz_check_if.ex3_haz_grp_id;
assign o_done_report.cmt_id               = r_ex3_issue.cmt_id;
assign o_done_report.grp_id               = r_ex3_issue.grp_id;

assign vec_phy_wr_if.valid   = r_ex3_issue.valid & r_ex3_issue.wr_reg.valid & ~r_ex3_mis_valid;
assign vec_phy_wr_if.rd_rnid = r_ex3_issue.wr_reg.rnid;
assign vec_phy_wr_if.rd_data = r_ex3_aligned_data;

assign vec_phy_fwd_if[0].valid   = vec_phy_wr_if.valid;
assign vec_phy_fwd_if[0].rd_rnid = r_ex3_issue.wr_reg.rnid;

assign vlsu_ldq_req_if.valid  = r_ex3_issue.valid & r_ex3_pipe_ctrl.op == decoder_vlsu_ctrl_pkg::OP_LOAD;
assign vlsu_ldq_req_if.paddr  = r_ex3_addr;
assign vlsu_ldq_req_if.cmt_id = r_ex3_issue.cmt_id;
assign vlsu_ldq_req_if.grp_id = r_ex3_issue.grp_id;

assign vlsu_stq_req_if.valid  = r_ex3_issue.valid & r_ex3_pipe_ctrl.op == decoder_vlsu_ctrl_pkg::OP_STORE;
assign vlsu_stq_req_if.paddr  = r_ex3_addr;
assign vlsu_stq_req_if.cmt_id = r_ex3_issue.cmt_id;
assign vlsu_stq_req_if.grp_id = r_ex3_issue.grp_id;

endmodule // scariv_vec_lsu_pipe
