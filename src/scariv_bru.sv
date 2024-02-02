// ------------------------------------------------------------------------
// NAME : scariv_bru
// TYPE : module
// ------------------------------------------------------------------------
// Branch Unit Top Module
// ------------------------------------------------------------------------
// Scheduler: BRU Instruction Scheduler
// Pieline: Branch Instruction
// ------------------------------------------------------------------------

module scariv_bru
(
  input logic i_clk,
  input logic i_reset_n,

  /* ROB notification interface */
  rob_info_if.slave                     rob_info_if,

  input scariv_pkg::grp_id_t disp_valid,
  scariv_front_if.watch                              disp,
  cre_ret_if.slave                           cre_ret_if,

  regread_if.master ex1_regread_rs1,
  regread_if.master ex1_regread_rs2,

  /* Forwarding path */
  early_wr_if.slave     early_wr_in_if[scariv_pkg::REL_BUS_SIZE],
  phy_wr_if.slave       phy_wr_in_if [scariv_pkg::TGT_BUS_SIZE],
  lsu_mispred_if.slave  mispred_in_if[scariv_conf_pkg::LSU_INST_NUM],

  /* write output */
  early_wr_if.master early_wr_out_if,
  phy_wr_if.master   phy_wr_out_if,

  done_report_if.master         done_report_if,

  // Commit notification
  commit_if.monitor commit_if,

  br_upd_if.master            ex3_br_upd_if,
  br_upd_if.slave             ex3_br_upd_slave_if,

  brtag_if.master             brtag_if
);

scariv_pkg::disp_t w_disp_inst[scariv_conf_pkg::DISP_SIZE];
scariv_pkg::disp_t disp_picked_inst[scariv_conf_pkg::BRU_DISP_SIZE];
logic [scariv_conf_pkg::BRU_DISP_SIZE-1:0] disp_picked_inst_valid;
scariv_pkg::grp_id_t disp_picked_grp_id[scariv_conf_pkg::BRU_DISP_SIZE];

scariv_bru_pkg::issue_entry_t w_rv0_issue;

done_if #(.RV_ENTRY_SIZE(scariv_conf_pkg::RV_BRU_ENTRY_SIZE)) w_ex3_done_if[1]();

logic              w_ex3_done;

scariv_disp_pickup
  #(
    .PORT_BASE(0),
    .PORT_SIZE(scariv_conf_pkg::BRU_DISP_SIZE)
    )
u_scariv_disp_pickup
  (
   .i_disp_valid (disp_valid),
   .i_disp (disp),

   .o_disp_valid  (disp_picked_inst_valid),
   .o_disp        (disp_picked_inst),
   .o_disp_grp_id (disp_picked_grp_id)
   );

scariv_bru_issue_unit
  #(
    .ENTRY_SIZE  (scariv_conf_pkg::RV_BRU_ENTRY_SIZE),
    .IS_BRANCH (1'b1),
    .IN_PORT_SIZE(scariv_conf_pkg::BRU_DISP_SIZE)
    )
u_issue_unit
  (
   .i_clk    (i_clk),
   .i_reset_n(i_reset_n),

   .rob_info_if (rob_info_if),

   .i_disp_valid(disp_picked_inst_valid),
   .i_cmt_id    (disp.payload.cmt_id),
   .i_grp_id    (disp_picked_grp_id),
   .i_disp_info (disp_picked_inst),
   .i_basicblk_pc_vaddr (disp.payload.basicblk_pc_vaddr),

   .cre_ret_if  (cre_ret_if),

   .i_stall (1'b0),

   .early_wr_if(early_wr_in_if),
   .phy_wr_if  (phy_wr_in_if),
   .mispred_if (mispred_in_if),

   .o_issue(w_rv0_issue),
   .o_iss_index_oh(),

   .commit_if (commit_if),
   .br_upd_if (ex3_br_upd_slave_if),
   .brtag_if  (brtag_if)
   );


scariv_bru_pipe
  #(
    .RV_ENTRY_SIZE(scariv_conf_pkg::RV_BRU_ENTRY_SIZE)
    )
u_bru_pipe
  (
   .i_clk    (i_clk),
   .i_reset_n(i_reset_n),

   .rv0_issue(w_rv0_issue),
   .rv0_index({scariv_conf_pkg::RV_BRU_ENTRY_SIZE{1'b0}}),

   .ex1_phy_wr_if(phy_wr_in_if),
   .mispred_if   (mispred_in_if),

   .ex0_regread_rs1(ex1_regread_rs1),
   .ex0_regread_rs2(ex1_regread_rs2),

   .commit_if (commit_if),

   .ex1_early_wr_if(early_wr_out_if),
   .ex3_phy_wr_if  (phy_wr_out_if  ),

   .done_report_if (done_report_if),
   .ex3_br_upd_if (ex3_br_upd_if)
   );


endmodule  // scariv_bru
