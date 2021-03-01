module msrh_lsu
  #(
    parameter LSU_PIPE_IDX = 0,
    parameter PORT_BASE = 0
    )
(
    input logic i_clk,
    input logic i_reset_n,

    input logic         [msrh_pkg::DISP_SIZE-1:0] disp_valid,
    disp_if.slave                          disp,

    // Replay from LDQ
    input logic             i_ldq_replay_valid,
    input msrh_pkg::issue_t i_ldq_replay_issue,
    input [msrh_lsu_pkg::MEM_Q_SIZE-1: 0] i_ldq_replay_index_oh,

    regread_if.master ex1_regread_rs1,
    regread_if.master ex1_regread_rs2,

    /* Forwarding path */
    input msrh_pkg::early_wr_t i_early_wr[msrh_pkg::REL_BUS_SIZE],

    /* L1D Interface */
    l1d_if.master              l1d_if,

    /* Load Requester Interface */
    l1d_lrq_if.master          l1d_lrq_if,

    // Feedbacks to LDQ / STQ
    output msrh_lsu_pkg::ex1_q_update_t o_ex1_q_updates,
    output logic                      o_tlb_resolve,
    output msrh_lsu_pkg::ex2_q_update_t o_ex2_q_updates,

    /* write output */
    output msrh_pkg::early_wr_t o_ex1_early_wr,
    output msrh_pkg::phy_wr_t   o_ex3_phy_wr,

    output logic                                 o_ex3_done,
    output logic [msrh_lsu_pkg::MEM_Q_SIZE-1: 0] o_ex3_index_oh
   );

msrh_pkg::disp_t w_disp_inst[msrh_pkg::DISP_SIZE];
msrh_pkg::disp_t disp_picked_inst[2];
logic [1:0] disp_picked_inst_valid;
logic [msrh_pkg::DISP_SIZE-1:0] disp_picked_grp_id[2];

msrh_pkg::issue_t w_rv0_issue;
logic [$clog2(msrh_lsu_pkg::MEM_Q_SIZE)-1:0] w_rv0_index;

logic         w_ex3_done;
logic [$clog2(msrh_lsu_pkg::MEM_Q_SIZE)-1:0] w_ex3_index;

generate for(genvar d_idx = 0; d_idx < msrh_pkg::DISP_SIZE; d_idx++) begin : d_loop
  assign w_disp_inst[d_idx] = disp.inst[d_idx];
end
endgenerate

generate
  for (genvar p_idx = 0; p_idx < 2; p_idx++) begin : pick_loop
    bit_pick_1_index #(
        .NUM(PORT_BASE + p_idx),
        .SEL_WIDTH(msrh_pkg::DISP_SIZE),
        .DATA_WIDTH($size(msrh_pkg::disp_t))
    ) u_bit_pick_1_index (
        .i_valids(disp_valid),
        .i_data  (w_disp_inst),
        .o_valid (disp_picked_inst_valid[p_idx]),
        .o_data  (disp_picked_inst[p_idx]),
        .o_picked_pos (disp_picked_grp_id[p_idx])
    );
  end  // block: d_loop
endgenerate

msrh_scheduler #(
    .ENTRY_SIZE  (msrh_lsu_pkg::MEM_Q_SIZE),
    .IN_PORT_SIZE(2)
) u_msrh_scheduler
  (
   .i_clk    (i_clk),
   .i_reset_n(i_reset_n),

   .i_disp_valid(disp_picked_inst_valid),
   .i_cmt_id    (disp.cmt_id),
   .i_grp_id    (disp_picked_grp_id),
   .i_disp_info (disp_picked_inst),

   .i_early_wr(i_early_wr),

   .o_issue(w_rv0_issue),
   .o_iss_index(),

   .i_pipe_done (),
   .i_done_index(),

   .o_done_report ()
);


// ===========================
// LSU Pipeline
// ===========================

msrh_lsu_pipe
  #(
    .LSU_PIPE_IDX(LSU_PIPE_IDX),
    .RV_ENTRY_SIZE(msrh_pkg::RV_ALU_ENTRY_SIZE)
    )
u_lsu_pipe
  (
   .i_clk    (i_clk),
   .i_reset_n(i_reset_n),

   .rv0_issue(w_rv0_issue),
   .rv0_is_store(1'b0),
   .i_q_index_oh('h1),  // temporary

   .i_ex0_replay_issue (i_ldq_replay_issue),
   .i_ex0_replay_index_oh (i_ldq_replay_index_oh),

   .o_ex1_tlb_miss_hazard(),
   .o_ex2_l1d_miss_hazard(),

   .ex1_regread_rs1(ex1_regread_rs1),
   .ex1_regread_rs2(ex1_regread_rs2),

   .o_ex1_early_wr(o_ex1_early_wr),
   .o_ex3_phy_wr (o_ex3_phy_wr),

   .ex1_l1d_if (l1d_if),
   .o_ex2_l1d_mispredicted (),

   .l1d_lrq_if (l1d_lrq_if),

   .o_ex1_q_updates (o_ex1_q_updates),
   .o_tlb_resolve   (o_tlb_resolve  ),
   .o_ex2_q_updates (o_ex2_q_updates),

   .o_ex3_done     (o_ex3_done    ),
   .o_ex3_index_oh (o_ex3_index_oh)
);

endmodule // msrh_lsu
