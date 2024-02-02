// ------------------------------------------------------------------------
// NAME : scariv_fpu
// TYPE : module
// ------------------------------------------------------------------------
// FPU Top Module
// ------------------------------------------------------------------------
// SubUnit
//  Instruction Scheduler
//  FPU Pipeline
// ------------------------------------------------------------------------


module scariv_fpu #(
    parameter PORT_BASE = 0
) (
    input logic i_clk,
    input logic i_reset_n,

    /* ROB notification interface */
    rob_info_if.slave           rob_info_if,
    /* CSR information */
    csr_info_if.slave  csr_info,

    input logic         [scariv_conf_pkg::DISP_SIZE-1:0] disp_valid,
    scariv_front_if.watch                          disp,
    cre_ret_if.slave                       cre_ret_if,


    regread_if.master ex0_regread_int_rs1,

    regread_if.master ex0_regread_rs1,
    regread_if.master ex0_regread_rs2,
    regread_if.master ex0_regread_rs3,

    /* Forwarding path */
    early_wr_if.slave early_wr_if[scariv_pkg::REL_BUS_SIZE],
    phy_wr_if.slave   phy_wr_if [scariv_pkg::TGT_BUS_SIZE],
    lsu_mispred_if.slave  mispred_if[scariv_conf_pkg::LSU_INST_NUM],

    /* write output */
    early_wr_if.master mv_early_wr_if,
    phy_wr_if.master   mv_phy_wr_if,
    phy_wr_if.master   fpnew_phy_wr_if,

    done_report_if.master         mv_done_report_if,
    done_report_if.master         fp_done_report_if,

    // Commit notification
    commit_if.monitor commit_if,
    br_upd_if.slave                br_upd_if
);

localparam FPU_PORT_SIZE = scariv_conf_pkg::FPU_DISP_SIZE / scariv_conf_pkg::FPU_INST_NUM;

`ifdef SIMULATION
initial begin
  if (scariv_conf_pkg::FPU_DISP_SIZE != (scariv_conf_pkg::FPU_DISP_SIZE / scariv_conf_pkg::FPU_INST_NUM) * scariv_conf_pkg::FPU_INST_NUM ) begin
    $fatal(0, "FPU_DISP_SIZE must be multiple of FPU_INST_NUM");
  end
end
`endif // SIMULATION

scariv_pkg::disp_t w_disp_inst[scariv_conf_pkg::DISP_SIZE];
scariv_pkg::disp_t disp_picked_inst[FPU_PORT_SIZE];
logic [FPU_PORT_SIZE-1:0] disp_picked_inst_valid;
scariv_pkg::grp_id_t disp_picked_grp_id[FPU_PORT_SIZE];
scariv_pkg::issue_t                            w_ex0_issue;
logic [scariv_conf_pkg::RV_FPU_ENTRY_SIZE-1:0] w_ex0_index_oh;

logic                                          w_fpnew_block;

scariv_disp_pickup
  #(
    .PORT_BASE(0),
    .PORT_SIZE(FPU_PORT_SIZE)
    )
u_scariv_disp_pickup
  (
   .i_disp_valid (disp_valid),
   .i_disp (disp),

   .o_disp_valid  (disp_picked_inst_valid),
   .o_disp        (disp_picked_inst),
   .o_disp_grp_id (disp_picked_grp_id)
   );

scariv_issue_unit
  #(
    .ENTRY_SIZE  (scariv_conf_pkg::RV_FPU_ENTRY_SIZE),
    .IN_PORT_SIZE(FPU_PORT_SIZE),
    .NUM_OPERANDS (3),
    .NUM_DONE_PORT (2)
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

   .i_stall    (w_fpnew_block),

   .early_wr_if(early_wr_if),
   .phy_wr_if  (phy_wr_if),
   .mispred_if (mispred_if),

   .o_issue(w_ex0_issue),
   .o_iss_index_oh(w_ex0_index_oh),

   .commit_if      (commit_if),
   .br_upd_if     (br_upd_if)
   );


scariv_fpu_pipe
  #(
    .RV_ENTRY_SIZE(scariv_conf_pkg::RV_FPU_ENTRY_SIZE)
    )
u_fpu
  (
   .i_clk    (i_clk),
   .i_reset_n(i_reset_n),

   .csr_info (csr_info),

   .o_fpnew_block (w_fpnew_block),

   .commit_if      (commit_if),
   .br_upd_if     (br_upd_if),

   .ex0_issue(w_ex0_issue),
   .ex0_index(w_ex0_index_oh),
   .ex1_phy_wr_if(phy_wr_if),

   .ex0_regread_int_rs1(ex0_regread_int_rs1),

   .ex0_regread_rs1(ex0_regread_rs1),
   .ex0_regread_rs2(ex0_regread_rs2),
   .ex0_regread_rs3(ex0_regread_rs3),

   .mispred_if (mispred_if),

   .ex1_mv_early_wr_if (mv_early_wr_if   ),
   .ex3_mv_phy_wr_if   (mv_phy_wr_if     ),
   .mv_done_report_if  (mv_done_report_if),

   .fpnew_phy_wr_if   (fpnew_phy_wr_if   ),
   .fp_done_report_if (fp_done_report_if )
   );


endmodule // scariv_fpu
