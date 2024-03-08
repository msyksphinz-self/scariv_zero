// ------------------------------------------------------------------------
// NAME : scariv_alu
// TYPE : module
// ------------------------------------------------------------------------
// ALU top module
// ------------------------------------------------------------------------
// Scheduler, ALU Pipeline
// Input : Distpached instruction
// Output: Calculation result
// ------------------------------------------------------------------------


module scariv_alu #(
    parameter PORT_BASE = 0
) (
    input logic i_clk,
    input logic i_reset_n,

    /* ROB notification interface */
    rob_info_if.slave           rob_info_if,

    input logic         [scariv_conf_pkg::DISP_SIZE-1:0] disp_valid,
    scariv_front_if.watch                          disp,
    cre_ret_if.slave                       cre_ret_if,


    regread_if.master ex1_regread_rs1,
    regread_if.master ex1_regread_rs2,

    /* Forwarding path */
    early_wr_if.slave     early_wr_in_if[scariv_pkg::REL_BUS_SIZE],
    phy_wr_if.slave       phy_wr_in_if  [scariv_pkg::TGT_BUS_SIZE],
    lsu_mispred_if.slave  mispred_in_if [scariv_conf_pkg::LSU_INST_NUM],

    /* write output */
    early_wr_if.master early_wr_out_if,
    phy_wr_if.master   phy_wr_out_if,

    done_report_if.master done_report_if,
    // Commit notification
    commit_if.monitor commit_if,
    br_upd_if.slave              br_upd_if
);

localparam ALU_PORT_SIZE = scariv_conf_pkg::ARITH_DISP_SIZE / scariv_conf_pkg::ALU_INST_NUM;
localparam ALU_ISS_ENTRY_SIZE = scariv_conf_pkg::RV_ALU_ENTRY_SIZE / scariv_conf_pkg::ALU_INST_NUM;

`ifdef SIMULATION
initial begin
  if (scariv_conf_pkg::ARITH_DISP_SIZE != (scariv_conf_pkg::ARITH_DISP_SIZE / scariv_conf_pkg::ALU_INST_NUM) * scariv_conf_pkg::ALU_INST_NUM ) begin
    $fatal(0, "ARITH_DISP_SIZE must be multiple of ALU_INST_NUM");
  end
end
`endif // SIMULATION

scariv_pkg::disp_t w_disp_inst[scariv_conf_pkg::DISP_SIZE];
scariv_pkg::disp_t disp_picked_inst[ALU_PORT_SIZE];
logic [ALU_PORT_SIZE-1:0] disp_picked_inst_valid;
scariv_pkg::grp_id_t disp_picked_grp_id[ALU_PORT_SIZE];
scariv_alu_pkg::issue_t w_ex0_issue;
logic [ALU_ISS_ENTRY_SIZE-1:0] w_ex0_index_oh;

logic                                        w_muldiv_stall;

scariv_disp_pickup
  #(
    .PORT_BASE(0),
    .PORT_SIZE(ALU_PORT_SIZE)
    )
u_scariv_disp_pickup
  (
   .i_disp_valid (disp_valid),
   .i_disp (disp),

   .o_disp_valid  (disp_picked_inst_valid),
   .o_disp        (disp_picked_inst),
   .o_disp_grp_id (disp_picked_grp_id)
   );

scariv_alu_issue_unit
  #(
    .ENTRY_SIZE  (ALU_ISS_ENTRY_SIZE),
    .IN_PORT_SIZE(ALU_PORT_SIZE)
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

   .i_stall    (w_muldiv_stall),

   .early_wr_if(early_wr_in_if),
   .phy_wr_if  (phy_wr_in_if  ),
   .mispred_if (mispred_in_if ),

   .o_issue(w_ex0_issue),
   .o_iss_index_oh(w_ex0_index_oh),

   .commit_if      (commit_if),
   .br_upd_if     (br_upd_if)
   );


scariv_alu_pipe
  #(
    .RV_ENTRY_SIZE(ALU_ISS_ENTRY_SIZE)
    )
u_alu
  (
   .i_clk    (i_clk),
   .i_reset_n(i_reset_n),

   .commit_if  (commit_if),
   .br_upd_if (br_upd_if),

   .ex0_issue(w_ex0_issue),
   .ex0_index(w_ex0_index_oh),
   .ex1_phy_wr_if(phy_wr_in_if),

   .o_muldiv_stall(w_muldiv_stall),

   .ex0_regread_rs1(ex1_regread_rs1),
   .ex0_regread_rs2(ex1_regread_rs2),

   .mispred_lsu_if (mispred_in_if),

   .ex0_early_wr_if(early_wr_out_if),
   .ex2_phy_wr_if  (phy_wr_out_if  ),

   .done_report_if (done_report_if)
   );


endmodule  // scariv_alu
