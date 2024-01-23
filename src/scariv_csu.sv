// ------------------------------------------------------------------------
// NAME : scariv_csu
// TYPE : module
// ------------------------------------------------------------------------
// CSR Access Unit
// ------------------------------------------------------------------------
// CSR Instruction Scheduler
// CSR Pipeline
// ------------------------------------------------------------------------

module scariv_csu
(
  input logic i_clk,
  input logic i_reset_n,

  input scariv_pkg::grp_id_t disp_valid,
  scariv_front_if.watch                              disp,
  cre_ret_if.slave                       cre_ret_if,

  regread_if.master                          ex1_regread_rs1,

  /* Forwarding path */
  early_wr_if.slave     early_wr_in_if[scariv_pkg::REL_BUS_SIZE],
  phy_wr_if.slave       phy_wr_in_if [scariv_pkg::TGT_BUS_SIZE],
  lsu_mispred_if.slave  mispred_in_if[scariv_conf_pkg::LSU_INST_NUM],

  /* write output */
  early_wr_if.master early_wr_out_if,
  phy_wr_if.master   phy_wr_out_if,

  /* CSR information */
  csr_info_if.master          csr_info,
  /* Interrupt Request information */
  interrupt_if.master         int_if,
  /* ROB notification interface */
  rob_info_if.slave           rob_info_if,

  done_report_if.master done_report_if,

  fflags_update_if.slave      fflags_update_if,

  // CLINT connection
  clint_if.slave clint_if,
  // PLIC connection
  plic_if.slave plic_if,

  // Commit notification
  commit_if.monitor commit_if,
  br_upd_if.slave              br_upd_if
);

scariv_pkg::disp_t w_disp_inst[scariv_conf_pkg::DISP_SIZE];
scariv_pkg::disp_t disp_picked_inst[scariv_conf_pkg::CSU_DISP_SIZE];
logic [scariv_conf_pkg::CSU_DISP_SIZE-1:0] disp_picked_inst_valid;
scariv_pkg::grp_id_t disp_picked_grp_id[scariv_conf_pkg::CSU_DISP_SIZE];

scariv_pkg::issue_t w_rv0_issue;
logic [scariv_conf_pkg::RV_CSU_ENTRY_SIZE-1:0] w_rv0_index_oh;

logic         w_ex3_done;
logic [scariv_conf_pkg::RV_CSU_ENTRY_SIZE-1:0] w_ex3_index;

// CSR Read Write interface
csr_rd_if w_csr_read ();
csr_wr_if w_csr_write();


scariv_disp_pickup
  #(
    .PORT_BASE(0),
    .PORT_SIZE(scariv_conf_pkg::CSU_DISP_SIZE)
    )
u_scariv_disp_pickup
  (
   .i_disp_valid (disp_valid),
   .i_disp (disp),

   .o_disp_valid  (disp_picked_inst_valid),
   .o_disp        (disp_picked_inst),
   .o_disp_grp_id (disp_picked_grp_id)
   );

scariv_csu_issue_unit
  #(
    .ENTRY_SIZE  (scariv_conf_pkg::RV_CSU_ENTRY_SIZE),
    .IN_PORT_SIZE(scariv_conf_pkg::CSU_DISP_SIZE),
    .EN_OLDEST(1'b1)
    )
u_scariv_issue_unit
  (
   .i_clk    (i_clk),
   .i_reset_n(i_reset_n),

   .rob_info_if (rob_info_if),

   .i_disp_valid(disp_picked_inst_valid),
   .i_cmt_id    (disp.payload.cmt_id),
   .i_grp_id    (disp_picked_grp_id),
   .i_disp_info (disp_picked_inst),
   .cre_ret_if  (cre_ret_if),

   .i_stall (1'b0),

   .phy_wr_if  (phy_wr_in_if),

   .o_issue(w_rv0_issue),
   .o_iss_index_oh(w_rv0_index_oh),

   .commit_if      (commit_if),
   .br_upd_if     (br_upd_if)
   );


scariv_csu_pipe
  #(
    .RV_ENTRY_SIZE(scariv_conf_pkg::RV_CSU_ENTRY_SIZE)
    )
u_csu_pipe
  (
   .i_clk    (i_clk),
   .i_reset_n(i_reset_n),

   .commit_if (commit_if),

   .rv0_issue(w_rv0_issue),

   .ex1_regread_rs1(ex1_regread_rs1),

   .ex1_early_wr_if(early_wr_out_if),
   .ex3_phy_wr_if  (phy_wr_out_if),

   .i_status_priv (csr_info.priv),
   .i_mstatus     (csr_info.mstatus),
   .read_if (w_csr_read),
   .write_if (w_csr_write),

   .done_report_if (done_report_if)
   );


scariv_csr
u_scariv_csr
  (
   .i_clk     (i_clk),
   .i_reset_n (i_reset_n),

   .read_if (w_csr_read),
   .write_if (w_csr_write),

   .clint_if (clint_if),
   .plic_if  (plic_if),

   .csr_info (csr_info),
   .int_if   (int_if),
   .fflags_update_if (fflags_update_if),

   .commit_if (commit_if)
   );


endmodule  // scariv_csu
