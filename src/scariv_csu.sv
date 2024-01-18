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

  input scariv_pkg::grp_id_t              disp_valid,
  scariv_front_if.watch                   disp,
  input scariv_vec_pkg::vlvtype_ren_idx_t i_vlvtype_ren_idx,
  cre_ret_if.slave                        cre_ret_if,

  regread_if.master                          ex1_regread_rs1,
  regread_if.master                          ex1_regread_rs2,

  /* Forwarding path */
  input scariv_pkg::early_wr_t i_early_wr[scariv_pkg::REL_BUS_SIZE],
  input scariv_pkg::phy_wr_t   i_phy_wr [scariv_pkg::TGT_BUS_SIZE],
  input scariv_pkg::mispred_t  i_mispred_lsu[scariv_conf_pkg::LSU_INST_NUM],

  /* write output */
  output scariv_pkg::early_wr_t o_ex1_early_wr,
  output scariv_pkg::phy_wr_t   o_ex3_phy_wr,

  /* CSR information */
  csr_info_if.master          csr_info,
  /* Interrupt Request information */
  interrupt_if.master         int_if,
  /* ROB notification interface */
  rob_info_if.slave           rob_info_if,

  output scariv_pkg::done_rpt_t o_done_report,

  fflags_update_if.slave      fflags_update_if,

  output logic                o_lmul_exception_mode,
  vec_csr_if.master           vec_csr_if,
  vlvtype_upd_if.master       vlvtype_upd_if,
  vlmul_upd_if.master         vlmul_upd_if,

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

scariv_csu_pkg::issue_t w_rv0_issue;
logic [scariv_conf_pkg::RV_CSU_ENTRY_SIZE-1:0] w_rv0_index_oh;

logic         w_ex3_done;
logic [scariv_conf_pkg::RV_CSU_ENTRY_SIZE-1:0] w_ex3_index;

// CSR Read Write interface
csr_rd_if w_csr_read ();
csr_wr_if w_csr_write();

csr_rd_if  w_vec_csr_read_if ();
csr_wr_if  w_vec_csr_write_if();


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

   .i_oldest_mode (o_lmul_exception_mode),

   .rob_info_if (rob_info_if),

   .i_disp_valid(disp_picked_inst_valid),
   .i_cmt_id    (disp.payload.cmt_id),
   .i_grp_id    (disp_picked_grp_id),
   .i_disp_info (disp_picked_inst),
   .i_vlvtype_ren_idx (i_vlvtype_ren_idx),

   .cre_ret_if  (cre_ret_if),

   .i_stall (1'b0),

   .i_phy_wr  (i_phy_wr),

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

   .i_lmul_exception_mode (o_lmul_exception_mode),

   .rv0_issue(w_rv0_issue),

   .ex1_regread_rs1(ex1_regread_rs1),
   .ex1_regread_rs2(ex1_regread_rs2),

   .o_ex1_early_wr(o_ex1_early_wr),
   .o_ex3_phy_wr (o_ex3_phy_wr),

   .i_status_priv (csr_info.priv),
   .i_mstatus     (csr_info.mstatus),
   .read_if (w_csr_read),
   .write_if (w_csr_write),

   .read_vec_if  (w_vec_csr_read_if),
   .write_vec_if (w_vec_csr_write_if),
   .vec_csr_if   (vec_csr_if),
   .vlvtype_upd_if (vlvtype_upd_if),
   .vlmul_upd_if   (vlmul_upd_if),

   .o_done_report (o_done_report)
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

scariv_vec_csr
u_vec_csr
  (
   .i_clk     (i_clk    ),
   .i_reset_n (i_reset_n),

   .read_csr_vec_if  (w_vec_csr_read_if),
   .write_csr_vec_if (w_vec_csr_write_if),

   .commit_if (commit_if),

   .o_lmul_exception_mode (o_lmul_exception_mode)
   );



endmodule  // scariv_csu
