module msrh_lsu
  import msrh_lsu_pkg::*;
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

    // input logic         [msrh_conf_pkg::DISP_SIZE-1:0] disp_valid,
    // disp_if.slave                          disp,
    // cre_ret_if.slave                       cre_ret_if,

    // Replay from LDQ
    lsu_replay_if.slave ldq_replay_if,
    // Replay from STQ
    lsu_replay_if.slave stq_replay_if,

    regread_if.master ex1_regread_rs1,
    regread_if.master ex1_regread_rs2,

    /* Forwarding path */
    input msrh_pkg::early_wr_t i_early_wr[msrh_pkg::REL_BUS_SIZE],
    input msrh_pkg::phy_wr_t   i_phy_wr  [msrh_pkg::TGT_BUS_SIZE],
    input msrh_pkg::mispred_t  i_mispred_lsu[msrh_conf_pkg::LSU_INST_NUM],

    // STQ Forwarding checker
    fwd_check_if.master           ex2_fwd_check_if,
    // STBuf Forward checker
    fwd_check_if.master           stbuf_fwd_check_if,

    /* L1D Interface */
    l1d_rd_if.master              l1d_rd_if,

    /* Load Requester Interface */
    l1d_lrq_if.master          l1d_lrq_if,
    // LRQ Hazard Check
    lrq_haz_check_if.master    lrq_haz_check_if,
    // STQ -> LDQ check
    ldq_haz_check_if.master    ldq_haz_check_if,

    // Page Table Walk I/O
    tlb_ptw_if.master ptw_if,

    // Feedbacks to LDQ / STQ
    output ex1_q_update_t   o_ex1_q_updates,
    output logic            o_tlb_resolve,
    output ex2_q_update_t   o_ex2_q_updates,
    output ex2_addr_check_t o_ex2_addr_check,

    /* write output */
    output msrh_pkg::early_wr_t o_ex1_early_wr,
    output msrh_pkg::phy_wr_t   o_ex3_phy_wr,

    // Commit notification
    input msrh_pkg::commit_blk_t i_commit,

    output msrh_pkg::mispred_t   o_ex2_mispred,
    output logic  o_ex3_done
   );

msrh_pkg::disp_t w_disp_inst[msrh_conf_pkg::DISP_SIZE];
msrh_pkg::disp_t disp_picked_inst[2];
logic [1:0] disp_picked_inst_valid;
logic [msrh_conf_pkg::DISP_SIZE-1:0] disp_picked_grp_id[2];


msrh_pkg::issue_t w_rv0_issue;
logic [MEM_Q_SIZE-1: 0] w_rv0_index_oh;

done_if #(.RV_ENTRY_SIZE(MEM_Q_SIZE)) w_ex3_ldq_stq_done_if();
done_if #(.RV_ENTRY_SIZE(MEM_Q_SIZE)) w_ex0_sched_done_if();

// generate for(genvar d_idx = 0; d_idx < msrh_conf_pkg::DISP_SIZE; d_idx++) begin : d_loop
//   assign w_disp_inst[d_idx] = disp.inst[d_idx];
// end
// endgenerate
//
// generate
//   for (genvar p_idx = 0; p_idx < 2; p_idx++) begin : pick_loop
//     bit_pick_1_index #(
//         .NUM(PORT_BASE + p_idx),
//         .SEL_WIDTH(msrh_conf_pkg::DISP_SIZE),
//         .DATA_WIDTH($size(msrh_pkg::disp_t))
//     ) u_bit_pick_1_index (
//         .i_valids(disp_valid),
//         .i_data  (w_disp_inst),
//         .o_valid (disp_picked_inst_valid[p_idx]),
//         .o_data  (disp_picked_inst[p_idx]),
//         .o_picked_pos (disp_picked_grp_id[p_idx])
//     );
//   end  // block: d_loop
// endgenerate
//
// msrh_scheduler #(
//     .IS_STORE(1'b1),
//     .ENTRY_SIZE  (MEM_Q_SIZE),
//     .IN_PORT_SIZE(2)
// ) u_msrh_scheduler
//   (
//    .i_clk    (i_clk),
//    .i_reset_n(i_reset_n),
//
//    .rob_info_if (rob_info_if),
//
//    .i_disp_valid(disp_picked_inst_valid),
//    .i_cmt_id    (disp.cmt_id),
//    .i_grp_id    (disp_picked_grp_id),
//    .i_disp_info (disp_picked_inst),
//    .cre_ret_if  (cre_ret_if),
//
//    .i_early_wr(i_early_wr),
//    .i_phy_wr  (i_phy_wr),
//    .i_mispred_lsu (i_mispred_lsu),
//
//    .o_issue       (w_rv0_issue),
//    .o_iss_index_oh(w_rv0_index_oh),
//
//    .i_ex0_rs_conflicted   (w_ex0_rs_conflicted),
//    .i_ex0_rs_conf_index_oh(w_ex0_rs_conf_index_oh),
//
//    .pipe_done_if (w_ex0_sched_done_if),
//
//    .i_commit (i_commit),
//
//    .o_done_report ()
// );


msrh_pkg::issue_t                     w_ex0_replay_issue;
logic [MEM_Q_SIZE-1: 0] w_ex0_replay_index_oh;
logic                   w_ld_is_older_than_st;
logic                   w_ld_selected;

assign w_ld_selected = ldq_replay_if.valid & ~stq_replay_if.valid |
                       ldq_replay_if.valid &  stq_replay_if.valid & w_ld_is_older_than_st;

assign w_ex0_replay_issue    = w_ld_selected ? ldq_replay_if.issue    : stq_replay_if.issue   ;
assign w_ex0_replay_index_oh = w_ld_selected ? ldq_replay_if.index_oh : stq_replay_if.index_oh;

msrh_rough_older_check
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

msrh_lsu_pipe
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

   .o_ex0_rs_conflicted    (),
   .o_ex0_rs_conf_index_oh (),

   .i_ex0_replay_issue    (w_ex0_replay_issue   ),
   .i_ex0_replay_index_oh (w_ex0_replay_index_oh),

   .o_ex1_tlb_miss_hazard(),
   .o_ex2_l1d_miss_hazard(),

   .ex1_regread_rs1(ex1_regread_rs1),
   .ex1_regread_rs2(ex1_regread_rs2),

   .i_mispred_lsu (i_mispred_lsu),

   .o_ex1_early_wr(o_ex1_early_wr),
   .o_ex3_phy_wr (o_ex3_phy_wr),

   .ex1_l1d_rd_if (l1d_rd_if),
   .o_ex2_mispred (o_ex2_mispred),

   .ptw_if(ptw_if),
   .l1d_lrq_if (l1d_lrq_if),
   .lrq_haz_check_if (lrq_haz_check_if),
   .ldq_haz_check_if (ldq_haz_check_if),

   .ex2_fwd_check_if (ex2_fwd_check_if),
   .stbuf_fwd_check_if (stbuf_fwd_check_if),

   .o_ex1_q_updates  (o_ex1_q_updates ),
   .o_tlb_resolve    (o_tlb_resolve   ),
   .o_ex2_q_updates  (o_ex2_q_updates ),
   .o_ex2_addr_check (o_ex2_addr_check),

   .ex0_sched_done_if   (w_ex0_sched_done_if),
   .ex3_ldq_stq_done_if (w_ex3_ldq_stq_done_if)
);

assign o_ex3_done = w_ex3_ldq_stq_done_if.done;

endmodule // msrh_lsu
