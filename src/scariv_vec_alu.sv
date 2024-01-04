// ------------------------------------------------------------------------
// NAME : scariv_vec_alu
// TYPE : module
// ------------------------------------------------------------------------
// Vector ALU top module
// ------------------------------------------------------------------------
// Scheduler, Vector ALU Pipeline
// Input : Distpached instruction
// Output: Calculation result
// ------------------------------------------------------------------------


module scariv_vec_alu #(
    parameter PORT_BASE = 0
) (
    input logic i_clk,
    input logic i_reset_n,

   /* CSR information */
   csr_info_if.slave  csr_info,

    /* ROB notification interface */
    rob_info_if.slave          rob_info_if,

    input scariv_pkg::grp_id_t      disp_valid,
    scariv_front_if.watch           disp,
    vlvtype_info_if.monitor         vlvtype_info_if,
    vlvtype_upd_if.slave            vlvtype_upd_if,

    cre_ret_if.slave             cre_ret_if,

    regread_if.master            ex1_xpr_regread_rs1,
    regread_if.master            ex1_fpr_regread_rs1,

    /* Forwarding path */
    input scariv_pkg::phy_wr_t   i_phy_wr [scariv_pkg::TGT_BUS_SIZE],

    /* read output */
    vec_regread_if.master  vec_phy_rd_if[3],
    vec_regread_if.master  vec_phy_v0_if,
    vec_regread_if.master  vec_phy_old_wr_if,
    /* write output */
    vec_regwrite_if.master vec_phy_wr_if[2],
    // Vector Forwarding Notification Path
    vec_phy_fwd_if.master  vec_valu_phy_fwd_if[2],
    vec_phy_fwd_if.slave   vec_vlsu_phy_fwd_if[1],

    output scariv_pkg::done_rpt_t o_done_report[2],
    // Commit notification
    input scariv_pkg::commit_blk_t i_commit,
    br_upd_if.slave                br_upd_if
);

localparam VEC_ALU_PORT_SIZE = scariv_conf_pkg::VALU_DISP_SIZE / scariv_conf_pkg::VEC_ALU_INST_NUM;

`ifdef SIMULATION
initial begin
  if (scariv_conf_pkg::VALU_DISP_SIZE != (scariv_conf_pkg::VALU_DISP_SIZE / scariv_conf_pkg::VEC_ALU_INST_NUM) * scariv_conf_pkg::VEC_ALU_INST_NUM) begin
    $fatal(0, "VALU_DISP_SIZE must be multiple of VEC_ALU_INST_NUM");
  end
end
`endif // SIMULATION

scariv_pkg::disp_t            w_disp_inst[scariv_conf_pkg::DISP_SIZE];
scariv_pkg::disp_t            w_disp_picked_inst[VEC_ALU_PORT_SIZE];
logic [VEC_ALU_PORT_SIZE-1:0] w_disp_picked_inst_valid;
scariv_pkg::grp_id_t          w_disp_picked_grp_id[VEC_ALU_PORT_SIZE];
scariv_vec_pkg::issue_t       w_ex0_issue;
vec_phy_fwd_if                w_vec_phy_fwd_if[3]();

scariv_disp_pickup
  #(
    .PORT_BASE(0),
    .PORT_SIZE(VEC_ALU_PORT_SIZE)
    )
u_scariv_disp_pickup
  (
   .i_disp_valid (disp_valid),
   .i_disp       (disp),

   .o_disp_valid  (w_disp_picked_inst_valid),
   .o_disp        (w_disp_picked_inst),
   .o_disp_grp_id (w_disp_picked_grp_id)
   );

scariv_pkg::early_wr_t w_early_wr_zero[scariv_pkg::REL_BUS_SIZE];
generate for (genvar idx = 0; idx < scariv_pkg::REL_BUS_SIZE; idx++) begin : early_zero_fill
  assign w_early_wr_zero[idx] = 'h0;
end endgenerate

scariv_pkg::mispred_t  w_mispred_lsu[scariv_conf_pkg::LSU_INST_NUM];
generate for (genvar idx = 0; idx < scariv_conf_pkg::LSU_INST_NUM; idx++) begin : mispred_zero_fill
  assign w_mispred_lsu[idx] = 'h0;
end endgenerate

assign w_vec_phy_fwd_if[2].valid   = vec_vlsu_phy_fwd_if[0].valid;
assign w_vec_phy_fwd_if[2].rd_rnid = vec_vlsu_phy_fwd_if[0].rd_rnid;

scariv_valu_issue_unit
  #(
    .ENTRY_SIZE  (scariv_conf_pkg::RV_VALU_ENTRY_SIZE),
    .IN_PORT_SIZE(VEC_ALU_PORT_SIZE),
    .NUM_OPERANDS(3)
    )
u_scariv_issue_unit
  (
   .i_clk    (i_clk),
   .i_reset_n(i_reset_n),

   .rob_info_if (rob_info_if),

   .i_disp_valid(w_disp_picked_inst_valid),
   .i_cmt_id    (disp.payload.cmt_id),
   .i_grp_id    (w_disp_picked_grp_id),
   .i_disp_info (w_disp_picked_inst),
   .vlvtype_info_if (vlvtype_info_if),
   .vlvtype_upd_if  (vlvtype_upd_if),

   .cre_ret_if  (cre_ret_if),

   .i_stall    (1'b0),

   .i_early_wr    (w_early_wr_zero),
   .i_phy_wr      (i_phy_wr),
   .i_mispred_lsu (w_mispred_lsu),
   .vec_phy_fwd_if (w_vec_phy_fwd_if),

   .o_issue(w_ex0_issue),
   .o_iss_index_oh(),

   .i_commit      (i_commit),
   .br_upd_if     (br_upd_if)
   );


scariv_vec_alu_pipe
  #(
    .RV_ENTRY_SIZE(scariv_conf_pkg::RV_VALU_ENTRY_SIZE)
    )
u_alu_pipe
  (
   .i_clk    (i_clk),
   .i_reset_n(i_reset_n),

   .csr_info (csr_info),

   .i_commit  (i_commit),
   .br_upd_if (br_upd_if),

   .i_ex0_issue (w_ex0_issue),
   .ex1_i_phy_wr(i_phy_wr),

   .ex0_xpr_regread_rs1(ex1_xpr_regread_rs1),
   .ex0_fpr_regread_rs1(ex1_fpr_regread_rs1),

   .vec_phy_rd_if (vec_phy_rd_if),
   .vec_phy_v0_if (vec_phy_v0_if),
   .vec_phy_old_wr_if (vec_phy_old_wr_if),
   .vec_phy_wr_if (vec_phy_wr_if),
   .vec_phy_fwd_if (w_vec_phy_fwd_if[ 0: 1]),

   .o_done_report (o_done_report)
   );

assign vec_valu_phy_fwd_if[0].valid   = w_vec_phy_fwd_if[0].valid;
assign vec_valu_phy_fwd_if[0].rd_rnid = w_vec_phy_fwd_if[0].rd_rnid;

assign vec_valu_phy_fwd_if[1].valid   = w_vec_phy_fwd_if[1].valid;
assign vec_valu_phy_fwd_if[1].rd_rnid = w_vec_phy_fwd_if[1].rd_rnid;

endmodule  // scariv_vec_alu
