// ------------------------------------------------------------------------
// NAME : scariv_lsu_pipe
// TYPE : module
// ------------------------------------------------------------------------
// LSU Pipeline
// ------------------------------------------------------------------------
//
// ------------------------------------------------------------------------

module scariv_lsu_pipe
  import decoder_lsu_ctrl_pkg::*;
  import scariv_lsu_pkg::*;
#(
  parameter LSU_PIPE_IDX = 0,
  parameter RV_ENTRY_SIZE = 32
  )
(
 input logic                           i_clk,
 input logic                           i_reset_n,

 /* CSR information */
 csr_info_if.slave                     csr_info,
 /* SFENCE update information */
 sfence_if.slave                       sfence_if_slave,

 // Commit notification
 input scariv_pkg::commit_blk_t        i_commit,
 br_upd_if.slave                       br_upd_if,

 input scariv_pkg::phy_wr_t             ex1_i_phy_wr[scariv_pkg::TGT_BUS_SIZE],

 input scariv_pkg::mispred_t            i_mispred_lsu[scariv_conf_pkg::LSU_INST_NUM],

 input scariv_lsu_pkg::lsu_pipe_issue_t i_ex0_replay_issue,
 input [MEM_Q_SIZE-1: 0]                i_ex0_replay_index_oh,

 regread_if.master                     ex0_regread_rs1,

 output scariv_pkg::early_wr_t         o_ex1_early_wr,
 output scariv_pkg::phy_wr_t           o_ex3_phy_wr,

 l1d_rd_if.master                      ex1_l1d_rd_if,
 output scariv_pkg::mispred_t          o_ex2_mispred,

 // Forwarding checker
 fwd_check_if.master                   ex2_fwd_check_if,     // STQ
 fwd_check_if.master                   stbuf_fwd_check_if,   // ST-Buffer
 fwd_check_if.master                   streq_fwd_check_if,   // Store Requestor
 ldq_haz_check_if.master               ldq_haz_check_if,
 stq_haz_check_if.master               stq_haz_check_if,
 missu_fwd_if.master                   missu_fwd_if,

 // RMW Ordere Hazard Check
 rmw_order_check_if.master             rmw_order_check_if,

 l1d_missu_if.master                   l1d_missu_if,

 // LRSC update Logic
 lrsc_if.master                        lrsc_if,

 // Feedbacks to LDQ / STQ
 output ex1_q_update_t                 o_ex1_q_updates,
 output logic                          o_tlb_resolve,
 output ex2_q_update_t                 o_ex2_q_updates,

  // Interface for Replay Queue
  lsu_pipe_haz_if.master                 lsu_pipe_haz_if,

  /* SFENCE update information */
  sfence_if.master                  sfence_if_master,
  /* FENCE.I update */
  output logic                      o_fence_i,

  output scariv_pkg::cmt_id_t          o_ex3_cmt_id,
  output scariv_pkg::grp_id_t          o_ex3_grp_id,
 done_if.master                        ex3_done_if,

 // Page Table Walk I/O
 tlb_ptw_if.master ptw_if
);

`include "scariv_csr_def.svh"

typedef struct packed {
  size_t  size;
  sign_t  sign;
  op_t    op;
  is_amo_t is_amo;
  rmwop_t rmwop;
} lsu_pipe_ctrl_t;


// Selected signal
scariv_lsu_pkg::lsu_pipe_issue_t        w_ex0_issue;
logic [MEM_Q_SIZE-1: 0]  w_ex0_index_oh;
lsu_pipe_ctrl_t          w_ex0_pipe_ctrl;

riscv_pkg::xlen_t                    w_ex0_rs1_fwd_data;
riscv_pkg::xlen_t                    w_ex0_rs1_selected_data;

logic                    w_ex0_rs1_lsu_mispred;
logic                    w_ex0_rs2_lsu_mispred;
logic                    w_ex0_rs1_mispred;
logic                    w_ex0_rs2_mispred;
logic w_ex0_commit_flush;
logic w_ex0_br_flush;

//
// EX1 stage
//
scariv_lsu_pkg::lsu_pipe_issue_t        r_ex1_issue, w_ex1_issue_next;
logic [MEM_Q_SIZE-1: 0]  r_ex1_index_oh;

riscv_pkg::xlen_t        r_ex1_rs1;
riscv_pkg::xlen_t        w_ex1_rs1_selected_data;

scariv_pkg::vaddr_t      w_ex1_vaddr;
tlb_req_t                w_ex1_tlb_req;
tlb_resp_t               w_ex1_tlb_resp;
lsu_pipe_ctrl_t          r_ex1_pipe_ctrl;
logic                    w_ex1_readmem_op;

logic                    w_ex1_haz_detected;

scariv_pkg::maxaddr_t    w_ex1_addr;
logic w_ex1_commit_flush;
logic w_ex1_br_flush;


riscv_pkg::xlen_t                  w_ex1_rs1_fwd_data;

//
// EX2 stage
//
scariv_lsu_pkg::lsu_pipe_issue_t       r_ex2_issue, w_ex2_issue_next;
logic [MEM_Q_SIZE-1: 0] r_ex2_index_oh;
scariv_pkg::maxaddr_t   r_ex2_addr;
lsu_pipe_ctrl_t         r_ex2_pipe_ctrl;
scariv_pkg::alen_t      w_ex2_data_tmp;
scariv_pkg::alen_t      w_ex2_data_sign_ext;
logic                   r_ex2_is_uc;
logic                   w_ex2_load_mispredicted;
logic                   r_ex2_haz_detected_from_ex1;
logic                   w_ex2_l1d_missed;
logic                   w_ex2_readmem_op;
logic                   r_ex2_except_valid;
scariv_pkg::except_t    r_ex2_except_type;

scariv_pkg::alenb_t       w_stbuf_fwd_dw;
scariv_pkg::alen_t        w_stbuf_fwd_aligned_data;

scariv_pkg::alenb_t       w_streq_fwd_dw;
scariv_pkg::alen_t        w_streq_fwd_aligned_data;

scariv_pkg::alenb_t       w_ex2_expected_fwd_valid;
scariv_pkg::alenb_t       w_ex2_fwd_success;

logic                   w_ex2_sc_success;
logic                   r_ex2_is_lr;
logic                   r_ex2_is_sc;

logic w_ex2_commit_flush;
logic w_ex2_br_flush;

//
// EX3 stage
//
scariv_lsu_pkg::lsu_pipe_issue_t r_ex3_issue, w_ex3_issue_next;
lsu_pipe_ctrl_t                  r_ex3_pipe_ctrl;
scariv_pkg::alen_t               r_ex3_aligned_data;
logic                            r_ex3_mis_valid;
logic                            r_ex3_except_valid;
scariv_pkg::except_t             r_ex3_except_type;
scariv_pkg::maxaddr_t            r_ex3_addr;

logic                 w_ex2_haz_detected;
assign w_ex2_readmem_op = (r_ex2_pipe_ctrl.op == OP_LOAD) | r_ex2_pipe_ctrl.is_amo | r_ex2_is_lr;
assign w_ex2_haz_detected = r_ex2_haz_detected_from_ex1 |
                            (o_ex2_q_updates.hazard_typ != EX2_HAZ_NONE) |
                            (w_ex2_readmem_op ? w_ex2_load_mispredicted : 1'b0);

//
// Pipeline Logic
//
always_comb begin
  w_ex1_issue_next       = w_ex0_issue;
  w_ex1_issue_next.valid = w_ex0_issue.valid & ~w_ex0_rs1_mispred & ~w_ex0_rs2_mispred & ~w_ex0_commit_flush & ~w_ex0_br_flush;
  if (br_upd_if.update) begin
  end

  w_ex2_issue_next       = r_ex1_issue;
  w_ex2_issue_next.valid = r_ex1_issue.valid & ~w_ex1_haz_detected & ~w_ex1_commit_flush & ~w_ex1_br_flush;
  if (br_upd_if.update) begin
  end

  w_ex3_issue_next       = r_ex2_issue;
  w_ex3_issue_next.valid = r_ex2_issue.valid & (r_ex2_except_valid | ~w_ex2_haz_detected) & ~w_ex2_commit_flush & ~w_ex2_br_flush;
end

select_mispred_bus ex0_rs1_mispred_select
(
 .i_entry_rnid (w_ex0_issue.rd_regs[0].rnid),
 .i_entry_type (w_ex0_issue.rd_regs[0].typ),
 .i_mispred    (i_mispred_lsu),

 .o_mispred    (w_ex0_rs1_lsu_mispred)
 );


select_mispred_bus ex0_rs2_mispred_select
(
 .i_entry_rnid (w_ex0_issue.rd_regs[1].rnid),
 .i_entry_type (w_ex0_issue.rd_regs[1].typ),
 .i_mispred    (i_mispred_lsu),

 .o_mispred    (w_ex0_rs2_lsu_mispred)
 );

assign w_ex0_rs1_mispred = w_ex0_issue.rd_regs[0].valid & w_ex0_issue.rd_regs[0].predict_ready ? w_ex0_rs1_lsu_mispred : 1'b0;
assign w_ex0_rs2_mispred = w_ex0_issue.rd_regs[1].valid & w_ex0_issue.rd_regs[1].predict_ready ? w_ex0_rs2_lsu_mispred : 1'b0;

assign w_ex0_commit_flush = scariv_pkg::is_commit_flush_target(w_ex0_issue.cmt_id, w_ex0_issue.grp_id, i_commit) & w_ex0_issue.valid;
assign w_ex0_br_flush     = scariv_pkg::is_br_flush_target(w_ex0_issue.cmt_id, w_ex0_issue.grp_id, br_upd_if.cmt_id, br_upd_if.grp_id,
                                                           br_upd_if.dead, br_upd_if.mispredict) & br_upd_if.update & w_ex0_issue.valid;


riscv_pkg::xlen_t w_ex0_tgt_data [scariv_pkg::TGT_BUS_SIZE];
for (genvar tgt_idx = 0; tgt_idx < scariv_pkg::TGT_BUS_SIZE; tgt_idx++) begin : ex0_rs_tgt_loop
  assign w_ex0_tgt_data[tgt_idx] = ex1_i_phy_wr[tgt_idx].rd_data;
end
assign w_ex0_rs1_fwd_data  = w_ex0_tgt_data[w_ex0_issue.rd_regs[0].early_index];

assign w_ex0_rs1_selected_data = w_ex0_issue.rd_regs[0].predict_ready[1] ? w_ex0_rs1_fwd_data : ex0_regread_rs1.data;

always_ff @(posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_ex1_issue   <= 'h0;
    r_ex1_index_oh   <= 'h0;

    r_ex2_issue     <= 'h0;
    r_ex2_index_oh  <= 'h0;
    r_ex2_haz_detected_from_ex1  <= 1'b0;

    r_ex2_is_uc     <= 1'b0;
  end else begin
    r_ex1_rs1 <= w_ex0_rs1_selected_data;

    r_ex1_issue     <= w_ex1_issue_next;
    r_ex1_index_oh  <= w_ex0_index_oh;
    r_ex1_pipe_ctrl <= w_ex0_pipe_ctrl;

    r_ex2_issue     <= w_ex2_issue_next;
    r_ex2_index_oh  <= r_ex1_index_oh;
    r_ex2_pipe_ctrl <= r_ex1_pipe_ctrl;
    r_ex2_haz_detected_from_ex1  <= r_ex1_issue.valid & w_ex1_haz_detected;

    r_ex2_is_uc     <= r_ex1_issue.paddr_valid ? r_ex1_issue.is_uc : !w_ex1_tlb_resp.cacheable;
    r_ex2_sfence_vma_illegal <= w_ex1_sfence_vma_illegal;

    r_ex3_issue     <= w_ex3_issue_next;
    r_ex3_pipe_ctrl <= r_ex2_pipe_ctrl;
    r_ex3_sfence_vma_illegal <= r_ex2_sfence_vma_illegal;
  end // else: !if(!i_reset_n)
end // always_ff @ (posedge i_clk, negedge i_reset_n)


// TLB
tlb
  #(
    .USING_VM(1'b1)
    )
u_tlb
(
 .i_clk    (i_clk),
 .i_reset_n(i_reset_n),

 .i_kill(1'b0),
 .sfence_if(sfence_if_slave),

 .i_csr_update (csr_info.update),
 .i_status_prv(csr_info.mstatus[`MSTATUS_MPRV] ? csr_info.mstatus[`MSTATUS_MPP] : csr_info.priv),
 .i_csr_status(csr_info.mstatus),
 .i_csr_satp  (csr_info.satp   ),

 .i_tlb_req (w_ex1_tlb_req ),
 .o_tlb_ready(),
 .o_tlb_resp(w_ex1_tlb_resp),

 .o_tlb_update(o_tlb_resolve),
 .o_tlb_resp_miss (),

 .ptw_if (ptw_if)
 );

assign w_ex1_addr = r_ex1_issue.paddr_valid ? r_ex1_issue.paddr : w_ex1_tlb_resp.paddr;

decoder_lsu_ctrl
u_decoder_ls_ctrl
  (
   .inst   (w_ex0_issue.inst      ),
   .size   (w_ex0_pipe_ctrl.size  ),
   .sign   (w_ex0_pipe_ctrl.sign  ),
   .op     (w_ex0_pipe_ctrl.op    ),
   .rmwop  (w_ex0_pipe_ctrl.rmwop ),
   .is_amo (w_ex0_pipe_ctrl.is_amo)
   );

//
// EX0 stage pipeline
//
// Pipe selection
assign w_ex0_issue    = i_ex0_replay_issue;
assign w_ex0_index_oh = i_ex0_replay_index_oh;

//
// EX1 stage pipeline
//
riscv_pkg::xlen_t w_ex1_tgt_data [scariv_pkg::TGT_BUS_SIZE];
for (genvar tgt_idx = 0; tgt_idx < scariv_pkg::TGT_BUS_SIZE; tgt_idx++) begin : ex1_rs_tgt_loop
  assign w_ex1_tgt_data[tgt_idx] = ex1_i_phy_wr[tgt_idx].rd_data;
end
assign w_ex1_rs1_fwd_data  = w_ex1_tgt_data[r_ex1_issue.rd_regs[0].early_index];

assign ex0_regread_rs1.valid = w_ex0_issue.valid & w_ex0_issue.rd_regs[0].valid;
assign ex0_regread_rs1.rnid  = w_ex0_issue.rd_regs[0].rnid;

assign w_ex1_rs1_selected_data = r_ex1_issue.rd_regs[0].predict_ready[0] ? w_ex1_rs1_fwd_data : r_ex1_rs1;

assign w_ex1_vaddr = w_ex1_rs1_selected_data[riscv_pkg::VADDR_W-1:0] + mem_offset(r_ex1_pipe_ctrl.op, r_ex1_issue.inst);

logic w_ex1_readmem_cmd;
logic w_ex1_writemem_cmd;
logic w_ex1_is_lr;
logic w_ex1_is_sc;
logic r_ex2_readmem_op;
logic r_ex2_writemem_op;
assign w_ex1_is_lr = (r_ex1_pipe_ctrl.op == OP_RMW) & ((r_ex1_pipe_ctrl.rmwop == RMWOP_LR32) |
                                                       (r_ex1_pipe_ctrl.rmwop == RMWOP_LR64));
assign w_ex1_readmem_cmd = (r_ex1_pipe_ctrl.op == OP_LOAD) | w_ex1_is_lr;

assign w_ex1_is_sc = (r_ex1_pipe_ctrl.op == OP_RMW) & ((r_ex1_pipe_ctrl.rmwop == RMWOP_SC32) |
                                                       (r_ex1_pipe_ctrl.rmwop == RMWOP_SC64));
assign w_ex1_writemem_cmd = (r_ex1_pipe_ctrl.op == OP_STORE) | r_ex1_pipe_ctrl.is_amo | w_ex1_is_sc;


assign w_ex1_tlb_req.valid       = r_ex1_issue.valid & (w_ex1_writemem_cmd | w_ex1_readmem_cmd) & ~r_ex1_issue.paddr_valid;
assign w_ex1_tlb_req.cmd         = w_ex1_readmem_cmd ? M_XRD : M_XWR;
assign w_ex1_tlb_req.vaddr       = w_ex1_vaddr;
assign w_ex1_tlb_req.size        =
                                   r_ex1_pipe_ctrl.size == SIZE_DW ? 8 :
                                   r_ex1_pipe_ctrl.size == SIZE_W  ? 4 :
                                   r_ex1_pipe_ctrl.size == SIZE_H  ? 2 :
                                   r_ex1_pipe_ctrl.size == SIZE_B  ? 1 : 0;
assign w_ex1_tlb_req.passthrough = 1'b0;

assign o_ex1_early_wr.valid       = r_ex1_issue.valid & r_ex1_issue.wr_reg.valid & !r_ex1_issue.oldest_valid & (o_ex1_q_updates.hazard_typ == EX1_HAZ_NONE);
assign o_ex1_early_wr.rd_rnid     = r_ex1_issue.wr_reg.rnid;
assign o_ex1_early_wr.rd_type     = r_ex1_issue.wr_reg.typ;
assign o_ex1_early_wr.may_mispred = r_ex1_issue.valid & r_ex1_issue.wr_reg.valid;

logic w_ex1_ld_except_valid;
logic w_ex1_st_except_valid;
scariv_pkg::except_t w_ex1_tlb_except_type;

logic w_ex1_sfence_vma_illegal;
logic r_ex2_sfence_vma_illegal;
logic r_ex3_sfence_vma_illegal;
assign w_ex1_sfence_vma_illegal = (r_ex1_pipe_ctrl.op == OP_SFENCE_VMA) & csr_info.mstatus[`MSTATUS_TVM];

assign w_ex1_ld_except_valid = w_ex1_readmem_cmd  & (w_ex1_tlb_resp.pf.ld | w_ex1_tlb_resp.ae.ld | w_ex1_tlb_resp.ma.ld);
assign w_ex1_st_except_valid = w_ex1_writemem_cmd & (w_ex1_tlb_resp.pf.st | w_ex1_tlb_resp.ae.st | w_ex1_tlb_resp.ma.st) |
                               (r_ex1_pipe_ctrl.op == OP_FENCE_I)    |
                               (r_ex1_pipe_ctrl.op == OP_FENCE)      |
                               (r_ex1_pipe_ctrl.op == OP_SFENCE_VMA) |
                               w_ex1_sfence_vma_illegal              |
                               'h0;

assign w_ex1_tlb_except_type = w_ex1_sfence_vma_illegal                  ? scariv_pkg::ILLEGAL_INST   :
                               w_ex1_readmem_cmd  & w_ex1_tlb_resp.ma.ld ? scariv_pkg::LOAD_ADDR_MISALIGN :
                               w_ex1_readmem_cmd  & w_ex1_tlb_resp.pf.ld ? scariv_pkg::LOAD_PAGE_FAULT    :  // PF<-->AE priority is opposite, TLB generate
                               w_ex1_readmem_cmd  & w_ex1_tlb_resp.ae.ld ? scariv_pkg::LOAD_ACC_FAULT     :  // PF and AE same time, PF is at first
                               w_ex1_writemem_cmd & w_ex1_tlb_resp.ma.st ? scariv_pkg::STAMO_ADDR_MISALIGN:
                               w_ex1_writemem_cmd & w_ex1_tlb_resp.pf.st ? scariv_pkg::STAMO_PAGE_FAULT   :  // PF and AE same time, PF is at first
                               w_ex1_writemem_cmd & w_ex1_tlb_resp.ae.st ? scariv_pkg::STAMO_ACC_FAULT    :  // PF<-->AE priority is opposite, TLB generate
                               scariv_pkg::SILENT_FLUSH;

assign w_ex1_haz_detected = o_ex1_q_updates.hazard_typ != EX1_HAZ_NONE;

// Interface to EX1 updates
assign o_ex1_q_updates.update              = r_ex1_issue.valid;
assign o_ex1_q_updates.cmt_id              = r_ex1_issue.cmt_id;
assign o_ex1_q_updates.grp_id              = r_ex1_issue.grp_id;
assign o_ex1_q_updates.hazard_typ          = w_ex1_tlb_req.valid & w_ex1_tlb_resp.miss ? EX1_HAZ_TLB_MISS :
                                             w_ex1_tlb_req.valid & ~w_ex1_tlb_resp.cacheable & ~r_ex1_issue.oldest_valid & ~(w_ex1_ld_except_valid | w_ex1_st_except_valid) ? EX1_HAZ_UC_ACCESS :
                                             EX1_HAZ_NONE;
assign o_ex1_q_updates.tlb_uc              = ~w_ex1_tlb_resp.cacheable;
assign o_ex1_q_updates.tlb_except_valid    = !w_ex1_tlb_resp.miss & (w_ex1_ld_except_valid | w_ex1_st_except_valid);
assign o_ex1_q_updates.tlb_except_type     = w_ex1_tlb_except_type;
assign o_ex1_q_updates.index_oh            = r_ex1_index_oh;
assign o_ex1_q_updates.vaddr               = w_ex1_vaddr;
assign o_ex1_q_updates.paddr               = w_ex1_tlb_resp.paddr;
assign o_ex1_q_updates.size                = r_ex1_pipe_ctrl.size;
assign o_ex1_q_updates.is_rmw              = (r_ex1_pipe_ctrl.op == OP_RMW);
assign o_ex1_q_updates.rmwop               = r_ex1_pipe_ctrl.rmwop;

`ifdef SIMULATION
always_ff @ (negedge i_clk, negedge i_reset_n) begin
  if (i_reset_n) begin
    // if (o_ex1_q_updates.update &
    //     !$onehot(o_ex1_q_updates.pipe_sel_idx_oh)) begin
    //   $fatal(0, "LSU Pipeline : o_ex1_q_updates.pipe_sel_idx_oh should be one-hot Value=%x\n",
    //          o_ex1_q_updates.pipe_sel_idx_oh);
    // end
    if (o_ex1_q_updates.update &
        !$onehot0(o_ex1_q_updates.index_oh)) begin
      $fatal(0, "LSU Pipeline : o_ex1_q_updates.index_oh should be one-hot. Value=%x\n",
             o_ex1_q_updates.index_oh);
    end
  end
end
`endif // SIMULATION


// Interface to L1D cache
assign w_ex1_readmem_op = (r_ex1_pipe_ctrl.op == OP_LOAD) | r_ex1_pipe_ctrl.is_amo | w_ex1_is_lr;

assign ex1_l1d_rd_if.s0_valid = r_ex1_issue.valid &
                                w_ex1_readmem_op & !w_ex1_haz_detected;
assign ex1_l1d_rd_if.s0_paddr = {w_ex1_addr[riscv_pkg::PADDR_W-1:$clog2(DCACHE_DATA_B_W)],
                                 {$clog2(DCACHE_DATA_B_W){1'b0}}};
assign ex1_l1d_rd_if.s0_high_priority = r_ex1_issue.l1d_high_priority;

assign w_ex1_commit_flush = scariv_pkg::is_commit_flush_target(r_ex1_issue.cmt_id, r_ex1_issue.grp_id, i_commit) & r_ex1_issue.valid;
assign w_ex1_br_flush     = scariv_pkg::is_br_flush_target(r_ex1_issue.cmt_id, r_ex1_issue.grp_id, br_upd_if.cmt_id, br_upd_if.grp_id,
                                                           br_upd_if.dead, br_upd_if.mispredict) & br_upd_if.update & r_ex1_issue.valid;


//
// EX2 stage pipeline
//
always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_ex2_addr <= 'h0;

    r_ex2_is_lr <= 1'b0;
    r_ex2_is_sc <= 1'b0;
  end else begin
    r_ex2_addr         <= w_ex1_ld_except_valid | w_ex1_st_except_valid ? w_ex1_vaddr : w_ex1_addr;
    r_ex2_except_valid <= w_ex1_ld_except_valid | w_ex1_st_except_valid;
    r_ex2_except_type  <= w_ex1_tlb_except_type;

    r_ex2_is_lr <= r_ex1_issue.valid & w_ex1_is_lr;
    r_ex2_is_sc <= r_ex1_issue.valid & w_ex1_is_sc;
  end // else: !if(!i_reset_n)
end // always_ff @ (posedge i_clk, negedge i_reset_n)

assign lrsc_if.lr_update_valid = r_ex2_issue.valid & r_ex2_is_lr & ~w_ex2_haz_detected;
assign lrsc_if.sc_check_valid  = r_ex2_issue.valid & r_ex2_is_sc & ~w_ex2_haz_detected;
assign lrsc_if.paddr           = r_ex2_addr;
assign w_ex2_sc_success        = lrsc_if.sc_success;


logic w_ex2_rmw_haz_vld;
assign w_ex2_rmw_haz_vld = rmw_order_check_if.ex2_stq_haz_vld | rmw_order_check_if.ex2_stbuf_haz_vld;

assign w_ex2_load_mispredicted = r_ex2_issue.valid &
                                 w_ex2_readmem_op &
                                 (w_ex2_rmw_haz_vld | stq_haz_check_if.ex2_haz_valid |
                                  (ex1_l1d_rd_if.s1_miss | ex1_l1d_rd_if.s1_conflict) & ~(&w_ex2_fwd_success));
assign w_ex2_l1d_missed = r_ex2_issue.valid &
                          w_ex2_readmem_op &
                          ~w_ex2_rmw_haz_vld &
                          ex1_l1d_rd_if.s1_miss &
                          ~ex1_l1d_rd_if.s1_conflict &
                          ~(&w_ex2_fwd_success);

assign l1d_missu_if.load              = w_ex2_l1d_missed & !r_ex2_haz_detected_from_ex1 &
                                        !stq_haz_check_if.ex2_haz_valid & !w_ex2_rmw_haz_vld &
                                        !r_ex2_except_valid & !(ex1_l1d_rd_if.s1_conflict | ex1_l1d_rd_if.s1_hit);
assign l1d_missu_if.req_payload.paddr = r_ex2_addr;
assign l1d_missu_if.req_payload.is_uc = r_ex2_is_uc;
assign l1d_missu_if.req_payload.way   = ex1_l1d_rd_if.s1_hit_way;
// L1D replace information

// Interface to EX2 updates
assign o_ex2_q_updates.update     = r_ex2_issue.valid;
assign o_ex2_q_updates.cmt_id     = r_ex2_issue.cmt_id;
assign o_ex2_q_updates.grp_id     = r_ex2_issue.grp_id;
assign o_ex2_q_updates.hazard_typ = stq_haz_check_if.ex2_haz_valid    ? EX2_HAZ_STQ_NONFWD_HAZ :
                                    w_ex2_rmw_haz_vld                 ? EX2_HAZ_RMW_ORDER_HAZ :
                                    &w_ex2_fwd_success                ? EX2_HAZ_NONE          :
                                    ex1_l1d_rd_if.s1_conflict         ? EX2_HAZ_L1D_CONFLICT  :
                                    l1d_missu_if.load ?
                                    (l1d_missu_if.resp_payload.full   ? EX2_HAZ_MISSU_FULL       :
                                     /* l1d_missu_if.resp_payload.allocated ? */ EX2_HAZ_MISSU_ASSIGNED) :
                                    EX2_HAZ_NONE;
assign o_ex2_q_updates.missu_index_oh = l1d_missu_if.resp_payload.missu_index_oh;
// assign o_ex2_q_updates.index_oh     = r_ex2_index_oh;
assign o_ex2_q_updates.hazard_index = stq_haz_check_if.ex2_haz_index;
assign o_ex2_q_updates.is_amo     = r_ex2_pipe_ctrl.is_amo;
assign o_ex2_q_updates.is_lr      = r_ex2_is_lr;
assign o_ex2_q_updates.is_sc      = r_ex2_is_sc;
assign o_ex2_q_updates.sc_success = w_ex2_sc_success;

// Interface to Replay Queue
always_comb begin
  lsu_pipe_haz_if.valid                  = r_ex2_issue.valid & (o_ex2_q_updates.hazard_typ != EX2_HAZ_NONE) & ~w_ex2_commit_flush & ~w_ex2_br_flush;
  lsu_pipe_haz_if.payload.inst           = r_ex2_issue.inst;
  lsu_pipe_haz_if.payload.cmt_id         = r_ex2_issue.cmt_id;
  lsu_pipe_haz_if.payload.grp_id         = r_ex2_issue.grp_id;
  if (br_upd_if.update) begin
  end
  lsu_pipe_haz_if.payload.cat            = r_ex2_issue.cat;
  lsu_pipe_haz_if.payload.oldest_valid   = r_ex2_issue.oldest_valid;
  lsu_pipe_haz_if.payload.hazard_typ     = o_ex2_q_updates.hazard_typ;
  lsu_pipe_haz_if.payload.rd_reg         = r_ex2_issue.rd_regs[0];
  lsu_pipe_haz_if.payload.wr_reg         = r_ex2_issue.wr_reg;
  lsu_pipe_haz_if.payload.paddr          = r_ex2_addr;
  lsu_pipe_haz_if.payload.is_uc          = r_ex2_is_uc;
  lsu_pipe_haz_if.payload.hazard_index   = o_ex2_q_updates.hazard_typ == EX2_HAZ_MISSU_ASSIGNED ? l1d_missu_if.resp_payload.missu_index_oh :
                                                stq_haz_check_if.ex2_haz_index;
end

// ---------------------
// Misprediction Update
// ---------------------
always_comb begin
  o_ex2_mispred.mis_valid = w_ex2_load_mispredicted | r_ex2_haz_detected_from_ex1;
  o_ex2_mispred.rd_type   = r_ex2_issue.wr_reg.typ;
  o_ex2_mispred.rd_rnid   = r_ex2_issue.wr_reg.rnid;
end


// `ifdef SIMULATION
// always_ff @ (negedge i_clk, negedge i_reset_n) begin
//   if (i_reset_n) begin
//     if (o_ex2_q_updates.update &
//         (r_ex2_pipe_ctrl.op == OP_LOAD) &
//         (o_ex2_q_updates.hazard_typ == EX2_HAZ_MISSU_ASSIGNED) &
//         !$onehot(o_ex2_q_updates.missu_index_oh)) begin
//       $fatal(0, "LSU Pipeline : o_ex2_q_updates.missu_index_oh should be one-hot. Value=%x\n",
//              o_ex2_q_updates.missu_index_oh);
//     end
//   end // if (i_reset_n)
// end
// `endif // SIMULATION

// Forwarding check
logic w_ex2_fwd_check_type;
assign w_ex2_fwd_check_type = (r_ex2_issue.cat == decoder_inst_cat_pkg::INST_CAT_LD) |
                              r_ex2_pipe_ctrl.is_amo | r_ex2_is_lr;

assign ex2_fwd_check_if.valid  = r_ex2_issue.valid & w_ex2_fwd_check_type;
assign ex2_fwd_check_if.cmt_id = r_ex2_issue.cmt_id;
assign ex2_fwd_check_if.grp_id = r_ex2_issue.grp_id;
assign ex2_fwd_check_if.paddr  = r_ex2_addr;
assign ex2_fwd_check_if.paddr_dw = gen_dw(r_ex2_pipe_ctrl.size, r_ex2_addr[$clog2(scariv_pkg::ALEN_W/8)-1:0]);

assign stbuf_fwd_check_if.valid  = r_ex2_issue.valid & w_ex2_fwd_check_type;
assign stbuf_fwd_check_if.cmt_id = r_ex2_issue.cmt_id;
assign stbuf_fwd_check_if.grp_id = r_ex2_issue.grp_id;
assign stbuf_fwd_check_if.paddr  = r_ex2_addr;
assign stbuf_fwd_check_if.paddr_dw = gen_dw(r_ex2_pipe_ctrl.size, r_ex2_addr[$clog2(scariv_pkg::ALEN_W/8)-1:0]);

assign streq_fwd_check_if.valid  = r_ex2_issue.valid & w_ex2_fwd_check_type;
assign streq_fwd_check_if.cmt_id = r_ex2_issue.cmt_id;
assign streq_fwd_check_if.grp_id = r_ex2_issue.grp_id;
assign streq_fwd_check_if.paddr  = r_ex2_addr;
assign streq_fwd_check_if.paddr_dw = gen_dw(r_ex2_pipe_ctrl.size, r_ex2_addr[$clog2(scariv_pkg::ALEN_W/8)-1:0]);

// LDQ Speculative Load Hazard Check
assign ldq_haz_check_if.ex2_valid  = r_ex2_issue.valid & (r_ex2_issue.cat == decoder_inst_cat_pkg::INST_CAT_ST);
assign ldq_haz_check_if.ex2_paddr  = r_ex2_addr;
assign ldq_haz_check_if.ex2_cmt_id = r_ex2_issue.cmt_id;
assign ldq_haz_check_if.ex2_grp_id = r_ex2_issue.grp_id;
assign ldq_haz_check_if.ex2_size   = r_ex2_pipe_ctrl.size;

// STQ Speculative Load Hazard Check
assign stq_haz_check_if.ex2_valid  = r_ex2_issue.valid & (r_ex2_issue.cat == decoder_inst_cat_pkg::INST_CAT_LD);
assign stq_haz_check_if.ex2_paddr  = r_ex2_addr;
assign stq_haz_check_if.ex2_cmt_id = r_ex2_issue.cmt_id;
assign stq_haz_check_if.ex2_grp_id = r_ex2_issue.grp_id;
assign stq_haz_check_if.ex2_size   = r_ex2_pipe_ctrl.size;

assign rmw_order_check_if.ex2_valid  = r_ex2_issue.valid;
assign rmw_order_check_if.ex2_cmt_id = r_ex2_issue.cmt_id;
assign rmw_order_check_if.ex2_grp_id = r_ex2_issue.grp_id;

// MISSU Hazard Check
assign missu_fwd_if.ex2_valid  = r_ex2_issue.valid & w_ex2_fwd_check_type;
assign missu_fwd_if.ex2_paddr  = r_ex2_addr;

scariv_pkg::alenb_t                  w_ex2_fwd_dw;
scariv_pkg::alen_t                    w_ex2_fwd_aligned_data;

scariv_pkg::alenb_t                  w_ex2_missu_fwd_dw;
scariv_pkg::alen_t                    w_ex2_missu_fwd_aligned_data;

scariv_pkg::alen_t                    w_ex2_fwd_final_data;

always_comb begin
  {w_ex2_fwd_dw, w_ex2_fwd_aligned_data} = fwd_align (r_ex2_pipe_ctrl.size,
                                                      ex2_fwd_check_if.fwd_dw, ex2_fwd_check_if.fwd_data,
                                                      r_ex2_addr[$clog2(scariv_pkg::ALEN_W/8)-1:0]);
  w_ex2_missu_fwd_aligned_data = missu_fwd_if.ex2_fwd_data >> {r_ex2_addr[$clog2(DCACHE_DATA_B_W)-1: 0], 3'b000};
  w_ex2_missu_fwd_dw           = {8{missu_fwd_if.ex2_fwd_valid}};
end


always_comb begin
  {w_stbuf_fwd_dw, w_stbuf_fwd_aligned_data} = fwd_align (r_ex2_pipe_ctrl.size,
                                                          stbuf_fwd_check_if.fwd_dw, stbuf_fwd_check_if.fwd_data,
                                                          r_ex2_addr[$clog2(scariv_pkg::ALEN_W/8)-1:0]);
  // {w_streq_fwd_dw, w_streq_fwd_aligned_data} = fwd_align (r_ex2_pipe_ctrl.size,
  //                                                         streq_fwd_check_if.fwd_dw, streq_fwd_check_if.fwd_data,
  //                                                         r_ex2_addr[$clog2(scariv_pkg::ALEN_W/8)-1:0]);
  w_streq_fwd_dw = streq_fwd_check_if.fwd_dw;
  w_streq_fwd_aligned_data = streq_fwd_check_if.fwd_data[scariv_pkg::ALEN_W-1: 0];

  case (r_ex2_pipe_ctrl.size)
    SIZE_DW : begin w_ex2_expected_fwd_valid     = {8{1'b1}}; end
    SIZE_W  : begin w_ex2_expected_fwd_valid     = 8'h0f;     end
    SIZE_H  : begin w_ex2_expected_fwd_valid     = 8'h03;     end
    SIZE_B  : begin w_ex2_expected_fwd_valid     = 8'h01;     end
    default : begin w_ex2_expected_fwd_valid     = 8'h00;     end
  endcase // case (r_ex2_pipe_ctrl.size)
end

scariv_pkg::alen_t w_ex2_l1d_data;
assign w_ex2_l1d_data = ex1_l1d_rd_if.s1_data[{r_ex2_addr[$clog2(DCACHE_DATA_B_W)-1:0], 3'b000} +: scariv_pkg::ALEN_W];

generate for (genvar b_idx = 0; b_idx < scariv_pkg::ALEN_W / 8; b_idx++) begin
  assign w_ex2_fwd_final_data[b_idx*8 +: 8] = w_ex2_fwd_dw    [b_idx] ? w_ex2_fwd_aligned_data    [b_idx*8 +: 8] :
                                              w_stbuf_fwd_dw  [b_idx] ? w_stbuf_fwd_aligned_data  [b_idx*8 +: 8] :
                                              w_ex2_missu_fwd_dw[b_idx] ? w_ex2_missu_fwd_aligned_data[b_idx*8 +: 8] :
                                              w_streq_fwd_dw  [b_idx] ? w_streq_fwd_aligned_data  [b_idx*8 +: 8] :
                                                                        w_ex2_l1d_data            [b_idx*8 +: 8];
  assign w_ex2_fwd_success[b_idx] = w_ex2_expected_fwd_valid[b_idx] ? (w_ex2_fwd_dw     [b_idx] |
                                                                       w_stbuf_fwd_dw   [b_idx] |
                                                                       w_ex2_missu_fwd_dw [b_idx] |
                                                                       w_streq_fwd_dw   [b_idx]) : 1'b1;
end
endgenerate

always_comb begin
  case(r_ex2_pipe_ctrl.size)
    SIZE_DW : w_ex2_data_tmp = w_ex2_fwd_final_data;
    SIZE_W  : w_ex2_data_tmp = {{(scariv_pkg::ALEN_W-32){1'b0}}, w_ex2_fwd_final_data[31: 0]};
    SIZE_H  : w_ex2_data_tmp = {{(scariv_pkg::ALEN_W-16){1'b0}}, w_ex2_fwd_final_data[15: 0]};
    SIZE_B  : w_ex2_data_tmp = {{(scariv_pkg::ALEN_W- 8){1'b0}}, w_ex2_fwd_final_data[ 7: 0]};
    default : w_ex2_data_tmp = 'h0;
  endcase // case (r_ex2_pipe_ctrl.size)
  if (r_ex2_issue.wr_reg.typ == scariv_pkg::FPR) begin
    if (r_ex2_pipe_ctrl.size == SIZE_W) begin
      w_ex2_data_sign_ext = {{(scariv_pkg::ALEN_W-32){1'b1}}, w_ex2_data_tmp[31: 0]};
    end else begin // r_ex2_pipe_ctrl.size == SIZE_DW
      w_ex2_data_sign_ext = w_ex2_data_tmp;
    end
  end else if (r_ex2_pipe_ctrl.sign == SIGN_S) begin  // INT Register
    case(r_ex2_pipe_ctrl.size)
      SIZE_W  : w_ex2_data_sign_ext = {{(scariv_pkg::ALEN_W-32){w_ex2_data_tmp[31]}}, w_ex2_data_tmp[31: 0]};
      SIZE_H  : w_ex2_data_sign_ext = {{(scariv_pkg::ALEN_W-16){w_ex2_data_tmp[15]}}, w_ex2_data_tmp[15: 0]};
      SIZE_B  : w_ex2_data_sign_ext = {{(scariv_pkg::ALEN_W- 8){w_ex2_data_tmp[ 7]}}, w_ex2_data_tmp[ 7: 0]};
      default : w_ex2_data_sign_ext = w_ex2_data_tmp;
    endcase // case (r_ex2_pipe_ctrl.size)
  end else begin
    w_ex2_data_sign_ext = w_ex2_data_tmp;
  end
end // always_comb

assign w_ex2_commit_flush = scariv_pkg::is_commit_flush_target(r_ex2_issue.cmt_id, r_ex2_issue.grp_id, i_commit) & r_ex2_issue.valid;
assign w_ex2_br_flush     = scariv_pkg::is_br_flush_target(r_ex2_issue.cmt_id, r_ex2_issue.grp_id, br_upd_if.cmt_id, br_upd_if.grp_id,
                                                           br_upd_if.dead, br_upd_if.mispredict) & br_upd_if.update & r_ex2_issue.valid;

//
// EX3 stage pipeline
//
always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_ex3_aligned_data <= 'h0;
    r_ex3_mis_valid <= 1'b0;
  end else begin
    r_ex3_aligned_data <= (r_ex2_pipe_ctrl.op == OP_RMW) &
                          ((r_ex2_pipe_ctrl.rmwop == RMWOP_SC32) | (r_ex2_pipe_ctrl.rmwop == RMWOP_SC64)) ? !w_ex2_sc_success : w_ex2_data_sign_ext;
    r_ex3_mis_valid <= o_ex2_mispred.mis_valid;
    r_ex3_addr      <= r_ex2_addr;

    r_ex3_except_valid <= r_ex2_except_valid;
    r_ex3_except_type  <= r_ex2_except_type;
  end
end // always_ff @ (posedge i_clk, negedge i_reset_n)

assign ex3_done_if.done          = r_ex3_issue.valid;
assign ex3_done_if.index_oh      = 'h0;
assign ex3_done_if.payload.except_valid  = r_ex3_except_valid;
assign ex3_done_if.payload.except_type   = r_ex3_except_type;
assign ex3_done_if.payload.except_tval   = r_ex3_sfence_vma_illegal ? r_ex3_issue.inst :
                                           {{(riscv_pkg::XLEN_W-riscv_pkg::VADDR_W){r_ex3_addr[riscv_pkg::VADDR_W-1]}}, r_ex3_addr[riscv_pkg::VADDR_W-1: 0]};
assign ex3_done_if.payload.another_flush_valid  = ldq_haz_check_if.ex3_haz_valid;
assign ex3_done_if.payload.another_flush_cmt_id = ldq_haz_check_if.ex3_haz_cmt_id;
assign ex3_done_if.payload.another_flush_grp_id = ldq_haz_check_if.ex3_haz_grp_id;
assign o_ex3_cmt_id = r_ex3_issue.cmt_id;
assign o_ex3_grp_id = r_ex3_issue.grp_id;

assign o_ex3_phy_wr.valid   = r_ex3_issue.valid &
                              r_ex3_issue.wr_reg.valid &
                              (r_ex3_issue.wr_reg.typ == scariv_pkg::GPR ? (r_ex3_issue.wr_reg.regidx != 'h0) :
                               r_ex3_issue.wr_reg.typ == scariv_pkg::FPR ? 1'b1 :
                               1'b1) &
                              ~r_ex3_mis_valid;
assign o_ex3_phy_wr.rd_rnid = r_ex3_issue.wr_reg.rnid;
assign o_ex3_phy_wr.rd_type = r_ex3_issue.wr_reg.typ;
assign o_ex3_phy_wr.rd_data = r_ex3_aligned_data;


// ------------
// SFENCE Update
// ------------
logic r_sfence_vma_commit_wait;
scariv_pkg::cmt_id_t r_sfence_vma_cmt_id;
scariv_pkg::grp_id_t r_sfence_vma_grp_id;
logic                                r_sfence_vma_is_rs1_x0;
logic                                r_sfence_vma_is_rs2_x0;
scariv_pkg::vaddr_t      r_sfence_vma_vaddr;

logic                                w_sfence_vma_sfence_commit_match;
assign w_sfence_vma_sfence_commit_match = r_sfence_vma_commit_wait & i_commit.commit &
                                          (i_commit.cmt_id == r_sfence_vma_cmt_id) &
                                          |(i_commit.grp_id & r_sfence_vma_grp_id);

always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_sfence_vma_commit_wait <= 'h0;
  end else begin
    if (w_sfence_vma_sfence_commit_match) begin
      r_sfence_vma_commit_wait <= 1'b0;
    end else if (r_ex3_issue.valid & (r_ex3_pipe_ctrl.op == OP_SFENCE_VMA) & ~r_ex3_sfence_vma_illegal) begin
      r_sfence_vma_commit_wait <= 1'b1;
      r_sfence_vma_cmt_id <= r_ex3_issue.cmt_id;
      r_sfence_vma_grp_id <= r_ex3_issue.grp_id;
      r_sfence_vma_is_rs1_x0 <= r_ex3_issue.rd_regs[0].regidx == 'h0;
      r_sfence_vma_is_rs2_x0 <= r_ex3_issue.rd_regs[1].regidx == 'h0;
      r_sfence_vma_vaddr     <= r_ex3_addr[riscv_pkg::VADDR_W-1:0];
    end
  end // else: !if(i_reset_n)
end // always_ff @ (posedge i_clk, negedge i_reset_n)

assign sfence_if_master.valid     = r_sfence_vma_commit_wait & w_sfence_vma_sfence_commit_match;
assign sfence_if_master.is_rs1_x0 = r_sfence_vma_is_rs1_x0;
assign sfence_if_master.is_rs2_x0 = r_sfence_vma_is_rs2_x0;
assign sfence_if_master.vaddr     = r_sfence_vma_vaddr[riscv_pkg::VADDR_W-1:0];

// ---------------
// FENCE_I update
// ---------------
logic                r_fencei_commit_wait;
logic                w_fencei_commit_match;
scariv_pkg::cmt_id_t r_fencei_cmt_id;
scariv_pkg::grp_id_t r_fencei_grp_id;
assign w_fencei_commit_match = r_fencei_commit_wait & i_commit.commit &
                               (i_commit.cmt_id == r_fencei_cmt_id) &
                               |(i_commit.grp_id & r_fencei_grp_id);
always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_fencei_commit_wait <= 'h0;
  end else begin
    if (w_fencei_commit_match) begin
      r_fencei_commit_wait <= 1'b0;
    end else if (r_ex3_issue.valid & (r_ex3_pipe_ctrl.op == OP_FENCE_I)) begin
      r_fencei_commit_wait <= 1'b1;
      r_fencei_cmt_id <= r_ex3_issue.cmt_id;
      r_fencei_grp_id <= r_ex3_issue.grp_id;
    end
  end // else: !if(!i_reset_n)
end // always_ff @ (posedge i_clk, negedge i_reset_n)


assign o_fence_i = w_fencei_commit_match;


`ifdef SIMULATION
// Kanata
import "DPI-C" function void log_stage
(
 input longint id,
 input string stage
);

always_ff @ (negedge i_clk, negedge i_reset_n) begin
  if (i_reset_n) begin
    if (w_ex0_issue.valid) begin
      log_stage (w_ex0_issue.kanata_id, "EX0");
    end
    if (r_ex1_issue.valid) begin
      log_stage (r_ex1_issue.kanata_id, "EX1");
    end
    if (r_ex2_issue.valid) begin
      log_stage (r_ex2_issue.kanata_id, "EX2");
    end
    if (r_ex3_issue.valid) begin
      log_stage (r_ex3_issue.kanata_id, "EX3");
    end
  end
end
`endif // SIMULATION


endmodule // scariv_lsu_pipe
