module msrh_csu
(
  input logic i_clk,
  input logic i_reset_n,

  input logic [msrh_conf_pkg::DISP_SIZE-1:0] disp_valid,
  disp_if.watch                              disp,
  cre_ret_if.slave                       cre_ret_if,

  regread_if.master                          ex1_regread_rs1,

  /* Forwarding path */
  input msrh_pkg::early_wr_t i_early_wr[msrh_pkg::REL_BUS_SIZE],
  input msrh_pkg::phy_wr_t   i_phy_wr [msrh_pkg::TGT_BUS_SIZE],
  input msrh_pkg::mispred_t  i_mispred_lsu[msrh_conf_pkg::LSU_INST_NUM],

  /* write output */
  output msrh_pkg::early_wr_t o_ex1_early_wr,
  output msrh_pkg::phy_wr_t   o_ex3_phy_wr,

  /* CSR information */
  csr_info_if.master          csr_info,
  /* Interrupt Request information */
  interrupt_if.master         int_if,
  /* ROB notification interface */
  rob_info_if.slave           rob_info_if,

  output msrh_pkg::done_rpt_t o_done_report,

  /* SFENCE update information */
  sfence_if.master            sfence_if,
  /* FENCE.I update */
  output logic                      o_fence_i,

  // Commit notification
  input msrh_pkg::commit_blk_t i_commit,
  br_upd_if.slave              br_upd_if
);

msrh_pkg::disp_t w_disp_inst[msrh_conf_pkg::DISP_SIZE];
msrh_pkg::disp_t disp_picked_inst[msrh_conf_pkg::CSU_DISP_SIZE];
logic [msrh_conf_pkg::CSU_DISP_SIZE-1:0] disp_picked_inst_valid;
logic [msrh_conf_pkg::DISP_SIZE-1:0] disp_picked_grp_id[msrh_conf_pkg::CSU_DISP_SIZE];

msrh_pkg::issue_t w_rv0_issue;
logic [msrh_conf_pkg::RV_CSU_ENTRY_SIZE-1:0] w_rv0_index_oh;

done_if #(.RV_ENTRY_SIZE(msrh_conf_pkg::RV_CSU_ENTRY_SIZE)) w_ex3_done_if();

logic         w_ex3_done;
logic [msrh_conf_pkg::RV_CSU_ENTRY_SIZE-1:0] w_ex3_index;

// CSR Read Write interface
csr_rd_if w_csr_read ();
csr_wr_if w_csr_write();


msrh_disp_pickup
  #(
    .PORT_BASE(0),
    .PORT_SIZE(msrh_conf_pkg::CSU_DISP_SIZE)
    )
u_msrh_disp_pickup
  (
   .i_disp_valid (disp_valid),
   .i_disp (disp),

   .o_disp_valid  (disp_picked_inst_valid),
   .o_disp        (disp_picked_inst),
   .o_disp_grp_id (disp_picked_grp_id)
   );

msrh_scheduler
  #(
    .ENTRY_SIZE  (msrh_conf_pkg::RV_CSU_ENTRY_SIZE),
    .IN_PORT_SIZE(msrh_conf_pkg::CSU_DISP_SIZE),
    .EN_OLDEST(1'b1)
    )
u_msrh_scheduler
  (
   .i_clk    (i_clk),
   .i_reset_n(i_reset_n),

   .rob_info_if (rob_info_if),

   .i_disp_valid(disp_picked_inst_valid),
   .i_cmt_id    (disp.cmt_id),
   .i_grp_id    (disp_picked_grp_id),
   .i_disp_info (disp_picked_inst),
   .cre_ret_if  (cre_ret_if),

   .i_stall (1'b0),

   .i_early_wr(i_early_wr),
   .i_phy_wr  (i_phy_wr),
   .i_mispred_lsu (i_mispred_lsu),

   .o_issue(w_rv0_issue),
   .o_iss_index_oh(w_rv0_index_oh),

   .pipe_done_if(w_ex3_done_if),
   .i_commit      (i_commit),
   .br_upd_if     (br_upd_if),
   .o_done_report (o_done_report)
   );


msrh_csu_pipe
  #(
    .RV_ENTRY_SIZE(msrh_conf_pkg::RV_CSU_ENTRY_SIZE)
    )
u_csu_pipe
  (
   .i_clk    (i_clk),
   .i_reset_n(i_reset_n),

   .rv0_issue(w_rv0_issue),
   .rv0_index(w_rv0_index_oh),
   .ex1_i_phy_wr(i_phy_wr),

   .ex1_regread_rs1(ex1_regread_rs1),

   .o_ex1_early_wr(o_ex1_early_wr),
   .o_ex3_phy_wr (o_ex3_phy_wr),

   .i_status_priv (csr_info.priv),
   .i_mstatus     (csr_info.mstatus),
   .read_if (w_csr_read),
   .write_if (w_csr_write),
   .sfence_if (sfence_if),
   .o_fence_i (o_fence_i),

   .ex3_done_if   (w_ex3_done_if)
   );


msrh_csr
u_msrh_csr
  (
   .i_clk     (i_clk),
   .i_reset_n (i_reset_n),

   .read_if (w_csr_read),
   .write_if (w_csr_write),

   .csr_info (csr_info),
   .int_if   (int_if),

   .i_commit (i_commit),

   .o_xcpt ()
   );


endmodule  // msrh_csu
