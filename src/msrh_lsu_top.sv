module msrh_lsu_top
  (
    input logic i_clk,
    input logic i_reset_n,

    input logic         [msrh_pkg::DISP_SIZE-1:0] disp_valid,
    disp_if.slave                          disp,

    regread_if.master   ex1_regread[msrh_pkg::LSU_INST_NUM * 2-1:0],

    l2_req_if.master  l1d_ext_req,
    l2_resp_if.slave  l1d_ext_resp,

    /* Forwarding path */
    input msrh_pkg::early_wr_t i_early_wr[msrh_pkg::REL_BUS_SIZE],
    input msrh_pkg::phy_wr_t   i_phy_wr [msrh_pkg::TGT_BUS_SIZE],

    /* write output */
    output msrh_pkg::early_wr_t o_ex1_early_wr[msrh_pkg::LSU_INST_NUM],
    output msrh_pkg::phy_wr_t   o_ex3_phy_wr  [msrh_pkg::LSU_INST_NUM],

    output msrh_pkg::done_rpt_t o_done_report[2],  // LDQ done report, STQ done report

    // Commit notification
    input msrh_pkg::commit_blk_t i_commit
   );

l1d_rd_if  w_l1d_rd_if [msrh_pkg::LSU_INST_NUM + 1] ();
l1d_wr_if  w_l1d_wr_if();
l1d_lrq_if w_l1d_lrq_if[msrh_pkg::LSU_INST_NUM] ();
l1d_lrq_if w_l1d_lrq_from_stq_miss ();

lrq_search_if w_lrq_search_if ();
msrh_lsu_pkg::lrq_resolve_t w_lrq_resolve;

// Feedbacks to LDQ / STQ
msrh_lsu_pkg::ex1_q_update_t        w_ex1_q_updates[msrh_pkg::LSU_INST_NUM];
logic [msrh_pkg::LSU_INST_NUM-1: 0] w_tlb_resolve;
msrh_lsu_pkg::ex2_q_update_t        w_ex2_q_updates[msrh_pkg::LSU_INST_NUM];

logic [msrh_pkg::LSU_INST_NUM-1: 0] w_ldq_replay_valid;
msrh_pkg::issue_t                   w_ldq_replay_issue[msrh_pkg::LSU_INST_NUM];
logic [msrh_lsu_pkg::LDQ_SIZE-1: 0] w_ldq_replay_index_oh[msrh_pkg::LSU_INST_NUM];
logic [msrh_pkg::LSU_INST_NUM-1: 0] w_ldq_replay_conflict;

logic [msrh_pkg::LSU_INST_NUM-1: 0] w_stq_replay_valid;
msrh_pkg::issue_t                   w_stq_replay_issue[msrh_pkg::LSU_INST_NUM];
logic [msrh_lsu_pkg::LDQ_SIZE-1: 0] w_stq_replay_index_oh[msrh_pkg::LSU_INST_NUM];
logic [msrh_pkg::LSU_INST_NUM-1: 0] w_stq_replay_conflict;

logic [msrh_pkg::LSU_INST_NUM-1: 0]   w_ex3_done;

logic [msrh_pkg::DISP_SIZE-1: 0]      w_ldq_disp_valid;
logic [msrh_pkg::DISP_SIZE-1: 0]      w_stq_disp_valid;

generate for (genvar lsu_idx = 0; lsu_idx < msrh_pkg::LSU_INST_NUM; lsu_idx++) begin : lsu_loop

  msrh_lsu
  #(
    .LSU_PIPE_IDX(lsu_idx),
    .PORT_BASE(lsu_idx * 2)
    )
  u_msrh_lsu
  (
    .i_clk    (i_clk    ),
    .i_reset_n(i_reset_n),

    .disp_valid (disp_valid),
    .disp (disp),

    .ex1_regread_rs1 (ex1_regread[lsu_idx * 2 + 0]),
    .ex1_regread_rs2 (ex1_regread[lsu_idx * 2 + 1]),

    .i_early_wr(i_early_wr),

    .l1d_rd_if (w_l1d_rd_if[lsu_idx]),
    .l1d_lrq_if (w_l1d_lrq_if[lsu_idx]),

    .i_ldq_replay_valid    (w_ldq_replay_valid[lsu_idx]),
    .i_ldq_replay_issue    (w_ldq_replay_issue[lsu_idx]),
    .i_ldq_replay_index_oh (w_ldq_replay_index_oh[lsu_idx]),
    .o_ldq_replay_conflict (w_ldq_replay_conflict[lsu_idx]),

    .i_stq_replay_valid    (w_stq_replay_valid[lsu_idx]),
    .i_stq_replay_issue    (w_stq_replay_issue[lsu_idx]),
    .i_stq_replay_index_oh (w_stq_replay_index_oh[lsu_idx]),
    .o_stq_replay_conflict (w_stq_replay_conflict[lsu_idx]),

    .o_ex1_q_updates (w_ex1_q_updates[lsu_idx]),
    .o_tlb_resolve   (w_tlb_resolve  [lsu_idx]),
    .o_ex2_q_updates (w_ex2_q_updates[lsu_idx]),

    .o_ex1_early_wr(o_ex1_early_wr[lsu_idx]),
    .o_ex3_phy_wr  (o_ex3_phy_wr  [lsu_idx]),

    .o_ex3_done (w_ex3_done [lsu_idx])
   );

end // block: lsu_loop
endgenerate

generate for (genvar d_idx = 0; d_idx < msrh_pkg::DISP_SIZE; d_idx++) begin : disp_loop
  assign w_ldq_disp_valid[d_idx] = disp_valid[d_idx] & disp.inst[d_idx].cat == msrh_pkg::CAT_LD;
  assign w_stq_disp_valid[d_idx] = disp_valid[d_idx] & disp.inst[d_idx].cat == msrh_pkg::CAT_ST;
end
endgenerate

// -----------------------------------
// Ldq
// -----------------------------------
msrh_ldq
  u_ldq
(
 .i_clk    (i_clk    ),
 .i_reset_n(i_reset_n),

 .i_disp_valid (w_ldq_disp_valid),
 .disp         (disp      ),

 .i_tlb_resolve  (w_tlb_resolve  ),
 .i_ex1_q_updates(w_ex1_q_updates),
 .i_ex2_q_updates(w_ex2_q_updates),

 .i_lrq_resolve (w_lrq_resolve),

 .o_ldq_replay_valid    (w_ldq_replay_valid   ),
 .o_ldq_replay_issue    (w_ldq_replay_issue   ),
 .o_ldq_replay_index_oh (w_ldq_replay_index_oh),
 .i_ldq_replay_conflict (w_ldq_replay_conflict),

 .i_ex3_done (w_ex3_done),

 .o_done_report(o_done_report[0])
 );


// -----------------------------------
// STQ
// -----------------------------------
msrh_stq
  u_stq
(
 .i_clk    (i_clk    ),
 .i_reset_n(i_reset_n),

 .i_disp_valid (w_stq_disp_valid),
 .disp         (disp      ),

 .i_early_wr (i_early_wr),

 .i_tlb_resolve  (w_tlb_resolve  ),
 .i_ex1_q_updates(w_ex1_q_updates),
 .i_ex2_q_updates(w_ex2_q_updates),

 .o_stq_replay_valid    (w_stq_replay_valid   ),
 .o_stq_replay_issue    (w_stq_replay_issue   ),
 .o_stq_replay_index_oh (w_stq_replay_index_oh),
 .i_stq_replay_conflict (w_stq_replay_conflict),

 .i_ex3_done (w_ex3_done),

 .i_commit (i_commit),
 .l1d_rd_if (w_l1d_rd_if[msrh_pkg::LSU_INST_NUM]),
 .l1d_lrq_stq_miss_if (w_l1d_lrq_from_stq_miss),

 .i_lrq_resolve (w_lrq_resolve),

 .l1d_wr_if (w_l1d_wr_if),

 .o_done_report(o_done_report[1])
 );


msrh_l1d_load_requester
  u_msrh_l1d_load_requester
(
 .i_clk    (i_clk    ),
 .i_reset_n(i_reset_n),
 .l1d_lrq  (w_l1d_lrq_if),

 .l1d_ext_req  (l1d_ext_req ),
 .l1d_ext_resp (l1d_ext_resp),

 .l1d_lrq_stq_miss_if (w_l1d_lrq_from_stq_miss),

 .lrq_search_if (w_lrq_search_if),
 .o_lrq_resolve (w_lrq_resolve)
 );


msrh_dcache
u_msrh_dcache
  (
   .i_clk(i_clk),
   .i_reset_n(i_reset_n),
   .l1d_rd_if (w_l1d_rd_if),
   .l1d_wr_if (w_l1d_wr_if),

   .l1d_ext_resp (l1d_ext_resp),

   .lrq_search_if (w_lrq_search_if)
   );

endmodule // mrsh_lsu_top
