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

    // input logic         [scariv_conf_pkg::DISP_SIZE-1:0] disp_valid,
    // disp_if.slave                          disp,
    // cre_ret_if.slave                       cre_ret_if,

    // Replay from LDQ
    ldq_replay_if.slave ldq_replay_if,
    // Replay from STQ
    stq_replay_if.slave stq_replay_if,

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

    /* write output */
    output scariv_pkg::early_wr_t o_ex1_early_wr,
    output scariv_pkg::phy_wr_t   o_ex3_phy_wr,

    // Commit notification
    input scariv_pkg::commit_blk_t i_commit,

    output scariv_pkg::mispred_t   o_ex2_mispred,
    done_if.master               ex3_done_if
   );

scariv_pkg::disp_t w_disp_inst[scariv_conf_pkg::DISP_SIZE];
scariv_pkg::disp_t disp_picked_inst[2];
logic [1:0] disp_picked_inst_valid;
scariv_pkg::grp_id_t disp_picked_grp_id[2];


scariv_lsu_pkg::lsu_pipe_issue_t w_rv0_issue;
logic [MEM_Q_SIZE-1: 0]          w_rv0_index_oh;

scariv_lsu_pkg::lsu_pipe_issue_t w_ex0_replay_issue;
logic [MEM_Q_SIZE-1: 0]          w_ex0_replay_index_oh;
logic                            w_ld_is_older_than_st;
logic                            w_ld_selected;

assign w_ld_selected = ldq_replay_if.valid & ~stq_replay_if.valid |
                       ldq_replay_if.valid &  stq_replay_if.valid & w_ld_is_older_than_st;

always_comb begin
  if (w_ld_selected) begin
    w_ex0_replay_issue.valid        = ldq_replay_if.valid       ;
    w_ex0_replay_issue.cmt_id       = ldq_replay_if.issue.cmt_id      ;
    w_ex0_replay_issue.grp_id       = ldq_replay_if.issue.grp_id      ;
    w_ex0_replay_issue.inst         = ldq_replay_if.issue.inst        ;
    w_ex0_replay_issue.rd_regs      = ldq_replay_if.issue.rd_regs     ;
    w_ex0_replay_issue.wr_reg       = ldq_replay_if.issue.wr_reg      ;
    w_ex0_replay_issue.oldest_valid = ldq_replay_if.issue.oldest_valid;
    w_ex0_replay_issue.cat          = ldq_replay_if.issue.cat         ;
`ifdef SIMULATION
    w_ex0_replay_issue.kanata_id    = ldq_replay_if.issue.kanata_id   ;
`endif // SIMULATION

    w_ex0_replay_index_oh           = ldq_replay_if.index_oh;
  end else begin // if (w_ld_selected)
    w_ex0_replay_issue.valid        = stq_replay_if.valid;
    w_ex0_replay_issue.cmt_id       = stq_replay_if.issue.cmt_id;
    w_ex0_replay_issue.grp_id       = stq_replay_if.issue.grp_id;
    w_ex0_replay_issue.inst         = stq_replay_if.issue.inst;
    w_ex0_replay_issue.rd_regs      = stq_replay_if.issue.rd_regs;
    w_ex0_replay_issue.wr_reg       = stq_replay_if.issue.wr_reg;
    w_ex0_replay_issue.oldest_valid = stq_replay_if.issue.oldest_valid;
    w_ex0_replay_issue.cat          = stq_replay_if.issue.cat;
`ifdef SIMULATION
    w_ex0_replay_issue.kanata_id    = stq_replay_if.issue.kanata_id;
`endif // SIMULATION
    w_ex0_replay_index_oh = stq_replay_if.index_oh;
  end // else: !if(w_ld_selected)
end // always_comb


scariv_rough_older_check
u_pipe_age
  (
   .i_cmt_id0 (ldq_replay_if.issue.cmt_id),
   .i_grp_id0 (ldq_replay_if.issue.grp_id),

   .i_cmt_id1 (stq_replay_if.issue.cmt_id),
   .i_grp_id1 (stq_replay_if.issue.grp_id),

   .o_0_older_than_1 (w_ld_is_older_than_st)
   );


assign ldq_replay_if.conflict = ~w_ld_selected;
assign stq_replay_if.conflict =  w_ld_selected;


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

   .i_rv0_issue('h0),
   .i_rv0_index_oh('h0),
   .ex1_i_phy_wr (i_phy_wr),

   .o_ex0_rs_conflicted    (),
   .o_ex0_rs_conf_index_oh (),

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

   .ex3_done_if (ex3_done_if)
);

endmodule // scariv_lsu
