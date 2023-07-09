// ------------------------------------------------------------------------
// NAME : scariv_lsu
// TYPE : module
// ------------------------------------------------------------------------
// LSU Top Module
// ------------------------------------------------------------------------
//
// ------------------------------------------------------------------------

module scariv_lsu
  import scariv_lsu_pkg::*;
  #(
    parameter LSU_PIPE_IDX = 0,
    parameter PORT_BASE = 0
    )
(
    input logic i_clk,
    input logic i_reset_n,

    /* CSR information */
    csr_info_if.slave                     csr_info,
    /* SFENCE update information */
    sfence_if.slave                       sfence_if,
    /* ROB notification interface */
    rob_info_if.slave                     rob_info_if,

    input logic [scariv_conf_pkg::DISP_SIZE-1:0] disp_valid,
    scariv_front_if.watch                        disp,
    cre_ret_if.slave                             cre_ret_if,

    regread_if.master ex1_regread_rs1,
    regread_if.master ex1_int_regread_rs2,
    regread_if.master ex1_fp_regread_rs2,

    /* Forwarding path */
    input scariv_pkg::early_wr_t i_early_wr[scariv_pkg::REL_BUS_SIZE],
    input scariv_pkg::phy_wr_t   i_phy_wr  [scariv_pkg::TGT_BUS_SIZE],
    input scariv_pkg::mispred_t  i_mispred_lsu[scariv_conf_pkg::LSU_INST_NUM],

    // STQ Forwarding checker
    fwd_check_if.master           ex2_fwd_check_if,
    // STBuf Forward checker
    fwd_check_if.master           stbuf_fwd_check_if,
    // Store Requestor Forward checker
    fwd_check_if.master           streq_fwd_check_if,

    /* L1D Interface */
    l1d_rd_if.master              l1d_rd_if,

    /* Load Requester Interface */
    l1d_missu_if.master          l1d_missu_if,
    // MISSU Forward Check
    missu_fwd_if.master    missu_fwd_if,
    // STQ -> LDQ check
    ldq_haz_check_if.master    ldq_haz_check_if,

    // RMW Ordere Hazard Check
    rmw_order_check_if.master  rmw_order_check_if,

    // LRSC update Logic
    lrsc_if.master             lrsc_if,

    // STQ Hazard Check
    stq_haz_check_if.master stq_haz_check_if,

    // Page Table Walk I/O
    tlb_ptw_if.master ptw_if,

    // Feedbacks to LDQ / STQ
    output ex1_q_update_t   o_ex1_q_updates,
    output logic            o_tlb_resolve,
    output ex2_q_update_t   o_ex2_q_updates,

    input logic             i_st_buffer_empty,
    input logic             i_st_requester_empty,

    input missu_resolve_t   i_missu_resolve,
    input logic             i_missu_is_full,
    input logic             i_missu_is_empty,

    /* write output */
    output scariv_pkg::early_wr_t o_ex1_early_wr,
    output scariv_pkg::phy_wr_t   o_ex3_phy_wr,

    // Commit notification
    input scariv_pkg::commit_blk_t i_commit,

    output scariv_pkg::mispred_t       o_ex2_mispred,
    output scariv_pkg::done_rpt_t      o_done_report,
    output scariv_pkg::another_flush_t o_another_flush_report,

    br_upd_if.slave                br_upd_if
   );

localparam MEM_PORT_SIZE = scariv_conf_pkg::MEM_DISP_SIZE / scariv_conf_pkg::LSU_INST_NUM;

done_if ex3_internal_done_if();

scariv_lsu_pkg::lsu_pipe_issue_t w_ex0_replay_issue;
logic [MEM_Q_SIZE-1: 0]          w_ex0_replay_index_oh;
logic                            w_replay_selected;

logic [MEM_PORT_SIZE-1:0] disp_picked_inst_valid;
scariv_pkg::disp_t        disp_picked_inst  [MEM_PORT_SIZE];
scariv_pkg::grp_id_t      disp_picked_grp_id[MEM_PORT_SIZE];

scariv_lsu_pkg::lsu_issue_entry_t               w_issue_from_iss;
logic [scariv_conf_pkg::RV_LSU_ENTRY_SIZE-1: 0] w_issue_index_from_iss;

lsu_pipe_haz_if w_lsu_pipe_haz_if ();
lsu_pipe_req_if w_lsu_pipe_req_if ();

done_if              w_ex3_done_if();
scariv_pkg::cmt_id_t w_ex3_cmt_id;
scariv_pkg::grp_id_t w_ex3_grp_id;

logic w_replay_queue_full;

scariv_disp_pickup
  #(
    .PORT_BASE(PORT_BASE),
    .PORT_SIZE(MEM_PORT_SIZE)
    )
u_scariv_disp_pickup
  (
   .i_disp_valid  (disp_valid),
   .i_disp        (disp),
   .o_disp_valid  (disp_picked_inst_valid),
   .o_disp        (disp_picked_inst      ),
   .o_disp_grp_id (disp_picked_grp_id    )
   );

scariv_lsu_issue_unit
#(
  .ENTRY_SIZE (scariv_conf_pkg::RV_LSU_ENTRY_SIZE),
  .IN_PORT_SIZE(MEM_PORT_SIZE)
)
u_issue_unit
(
  .i_clk    (i_clk    ),
  .i_reset_n(i_reset_n),

  .rob_info_if  (rob_info_if),

  .i_disp_valid (disp_picked_inst_valid),
  .i_cmt_id     (disp.payload.cmt_id   ),
  .i_grp_id     (disp_picked_grp_id    ),
  .i_disp_info  (disp_picked_inst      ),
  .cre_ret_if   (cre_ret_if            ),

  .i_stall      (w_replay_selected     ),

  .o_issue        (w_issue_from_iss      ),
  .o_iss_index_oh (w_issue_index_from_iss),

  .i_ex1_updates        (o_ex1_q_updates     ),
  .i_tlb_resolve        (o_tlb_resolve       ),
  .i_ex2_updates        (o_ex2_q_updates     ),
  .i_st_buffer_empty    (i_st_buffer_empty   ),
  .i_st_requester_empty (i_st_requester_empty),
  .i_replay_queue_full  (w_replay_queue_full ),

  .i_missu_is_empty     (i_missu_is_empty    ),

  .pipe_done_if (ex3_internal_done_if),

  .o_done_report (),

  .i_commit  (i_commit),
  .br_upd_if (br_upd_if),

  // .request_if (request_if),

  .i_early_wr    (i_early_wr),
  .i_phy_wr      (i_phy_wr  ),
  .i_mispred_lsu (i_mispred_lsu)
);


// Replay Queue
scariv_lsu_replay_queue
u_replay_queue
(
  .i_clk (i_clk),
  .i_reset_n (i_reset_n),

  .i_commit  (i_commit),
  .br_upd_if (br_upd_if),

  .lsu_pipe_haz_if (w_lsu_pipe_haz_if),

  .i_missu_resolve (i_missu_resolve ),
  .i_missu_is_full (i_missu_is_full ),

  .o_full (w_replay_queue_full),

  .lsu_pipe_req_if (w_lsu_pipe_req_if)
);

assign w_replay_selected = w_lsu_pipe_req_if.valid;
assign w_lsu_pipe_req_if.ready = 1'b1;

always_comb begin
  if (w_replay_selected) begin
    w_ex0_replay_issue.valid        = w_lsu_pipe_req_if.valid       ;
    w_ex0_replay_issue.cmt_id       = w_lsu_pipe_req_if.payload.cmt_id      ;
    w_ex0_replay_issue.grp_id       = w_lsu_pipe_req_if.payload.grp_id      ;
    w_ex0_replay_issue.br_mask      = w_lsu_pipe_req_if.payload.br_mask     ;
    w_ex0_replay_issue.inst         = w_lsu_pipe_req_if.payload.inst        ;
    w_ex0_replay_issue.rd_regs[0]   = w_lsu_pipe_req_if.payload.rd_reg      ;
    w_ex0_replay_issue.wr_reg       = w_lsu_pipe_req_if.payload.wr_reg      ;
    w_ex0_replay_issue.oldest_valid = w_lsu_pipe_req_if.payload.oldest_valid;
    w_ex0_replay_issue.cat          = w_lsu_pipe_req_if.payload.cat         ;
`ifdef SIMULATION
    w_ex0_replay_issue.kanata_id    = 'h0;  // w_lsu_pipe_req_if.kanata_id   ;
`endif // SIMULATION
    w_ex0_replay_index_oh           = 'h0;
  end else begin
    w_ex0_replay_issue.valid        = w_issue_from_iss.valid;
    w_ex0_replay_issue.cmt_id       = w_issue_from_iss.cmt_id;
    w_ex0_replay_issue.grp_id       = w_issue_from_iss.grp_id;
    w_ex0_replay_issue.br_mask      = w_issue_from_iss.br_mask;
    w_ex0_replay_issue.inst         = w_issue_from_iss.inst;
    w_ex0_replay_issue.rd_regs      = w_issue_from_iss.rd_regs;
    w_ex0_replay_issue.wr_reg       = w_issue_from_iss.wr_reg;
    w_ex0_replay_issue.oldest_valid = w_issue_from_iss.oldest_valid;
    w_ex0_replay_issue.cat          = w_issue_from_iss.cat;
`ifdef SIMULATION
    w_ex0_replay_issue.kanata_id    = w_issue_from_iss.kanata_id;
`endif // SIMULATION
    w_ex0_replay_index_oh           = w_issue_index_from_iss;
  end
end // always_comb


// ===========================
// LSU Pipeline
// ===========================

scariv_lsu_pipe
  #(
    .LSU_PIPE_IDX(LSU_PIPE_IDX),
    .RV_ENTRY_SIZE(MEM_Q_SIZE)
    )
u_lsu_pipe
  (
   .i_clk    (i_clk),
   .i_reset_n(i_reset_n),

   .csr_info (csr_info),
   .sfence_if(sfence_if),

   .ex1_i_phy_wr (i_phy_wr),

   .i_ex0_replay_issue    (w_ex0_replay_issue   ),
   .i_ex0_replay_index_oh (w_ex0_replay_index_oh),

   .ex1_regread_rs1(ex1_regread_rs1),
   .ex1_int_regread_rs2(ex1_int_regread_rs2),
   .ex1_fp_regread_rs2 (ex1_fp_regread_rs2),

   .i_mispred_lsu (i_mispred_lsu),

   .o_ex1_early_wr(o_ex1_early_wr),
   .o_ex3_phy_wr (o_ex3_phy_wr),

   .ex1_l1d_rd_if (l1d_rd_if),
   .o_ex2_mispred (o_ex2_mispred),

   .ptw_if(ptw_if),
   .l1d_missu_if (l1d_missu_if),
   .missu_fwd_if (missu_fwd_if),
   .ldq_haz_check_if (ldq_haz_check_if),

   .rmw_order_check_if (rmw_order_check_if),

   .stq_haz_check_if (stq_haz_check_if),

   .ex2_fwd_check_if (ex2_fwd_check_if),
   .stbuf_fwd_check_if (stbuf_fwd_check_if),
   .streq_fwd_check_if (streq_fwd_check_if),

   .lrsc_if (lrsc_if),

   .o_ex1_q_updates  (o_ex1_q_updates ),
   .o_tlb_resolve    (o_tlb_resolve   ),
   .o_ex2_q_updates  (o_ex2_q_updates ),
    .lsu_pipe_haz_if (w_lsu_pipe_haz_if),

   .ex3_done_if (w_ex3_done_if),
   .o_ex3_cmt_id (w_ex3_cmt_id),
   .o_ex3_grp_id (w_ex3_grp_id)
);

assign o_done_report.valid               = w_ex3_done_if.done;
assign o_done_report.cmt_id              = w_ex3_cmt_id;
assign o_done_report.grp_id              = w_ex3_grp_id;
assign o_done_report.except_valid        = w_ex3_done_if.payload.except_valid       ;
assign o_done_report.except_type         = w_ex3_done_if.payload.except_type        ;
assign o_done_report.except_tval         = w_ex3_done_if.payload.except_tval        ;
assign o_done_report.fflags_update_valid = w_ex3_done_if.payload.fflags_update_valid;
assign o_done_report.fflags              = w_ex3_done_if.payload.fflags             ;

assign o_another_flush_report.valid  = w_ex3_done_if.payload.another_flush_valid ;
assign o_another_flush_report.cmt_id = w_ex3_done_if.payload.another_flush_cmt_id;
assign o_another_flush_report.grp_id = w_ex3_done_if.payload.another_flush_grp_id;

endmodule // scariv_lsu
