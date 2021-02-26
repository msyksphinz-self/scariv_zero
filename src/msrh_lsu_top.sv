module msrh_lsu_top
  (
    input logic i_clk,
    input logic i_reset_n,

    input logic         [msrh_pkg::DISP_SIZE-1:0] disp_valid,
    disp_if.slave                          disp,

    regread_if.master   ex1_regread[msrh_pkg::LSU_INST_NUM * 2-1:0],

    /* Forwarding path */
    input msrh_pkg::early_wr_t i_early_wr[msrh_pkg::REL_BUS_SIZE],
    input msrh_pkg::phy_wr_t   i_phy_wr [msrh_pkg::TGT_BUS_SIZE],

    /* write output */
    output msrh_pkg::early_wr_t o_ex1_early_wr[msrh_pkg::LSU_INST_NUM],
    output msrh_pkg::phy_wr_t   o_ex3_phy_wr  [msrh_pkg::LSU_INST_NUM],

    output msrh_pkg::done_rpt_t o_done_report[msrh_pkg::LSU_INST_NUM]
   );

l1d_if     w_l1d_if    [msrh_pkg::LSU_INST_NUM] ();
l1d_lrq_if w_l1d_lrq_if[msrh_pkg::LSU_INST_NUM] ();

generate for (genvar lsu_idx = 0; lsu_idx < msrh_pkg::LSU_INST_NUM; lsu_idx++) begin : lsu_loop

  msrh_lsu
  #(
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
    .i_phy_wr  (i_phy_wr),

    .l1d_if (w_l1d_if[lsu_idx]),
    .l1d_lrq_if (w_l1d_lrq_if[lsu_idx]),

    .o_ex1_early_wr(o_ex1_early_wr[lsu_idx]),
    .o_ex3_phy_wr  (o_ex3_phy_wr  [lsu_idx]),

    .o_done_report(o_done_report[lsu_idx])
   );

end // block: lsu_loop
endgenerate

msrh_l1d_load_requester
  u_msrh_l1d_load_requester
(
 .i_clk    (i_clk    ),
 .i_reset_n(i_reset_n),
 .l1d_lrq  (w_l1d_lrq_if),

 .o_l1d_ext_req ()
 );


msrh_dcache
u_msrh_dcache
  (
   .i_clk(i_clk),
   .i_reset_n(i_reset_n),
   .l1d_if (w_l1d_if)
   );

endmodule // mrsh_lsu_top
