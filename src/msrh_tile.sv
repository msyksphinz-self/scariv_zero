module msrh_tile (
    input logic i_clk,
    input logic i_reset_n,

    // L2 request from ICache
    l2_req_if.master ic_l2_req,
    l2_resp_if.slave ic_l2_resp
);

  l2_req_if l2_req ();
  l2_resp_if l2_resp ();

  disp_if w_iq_disp ();
  disp_if w_id_disp ();
  disp_if w_sc_disp ();

l1d_if     w_l1d_if    [msrh_pkg::LSU_INST_NUM] ();
l1d_lrq_if w_l1d_lrq_if[msrh_pkg::LSU_INST_NUM] ();

logic [msrh_pkg::DISP_SIZE-1:0] w_disp_valids;
logic [msrh_pkg::CMT_BLK_W-1:0] w_sc_new_cmt_id;

msrh_pkg::early_wr_t w_ex1_early_wr[msrh_pkg::REL_BUS_SIZE];
msrh_pkg::phy_wr_t   w_ex3_phy_wr  [msrh_pkg::TGT_BUS_SIZE];

regread_if regread[msrh_pkg::LSU_INST_NUM * 2 +
                   msrh_pkg::ALU_INST_NUM * 2] ();

msrh_pkg::done_rpt_t w_done_rpt[msrh_pkg::CMT_BUS_SIZE];

  msrh_frontend u_frontend (
      .i_clk(i_clk),
      .i_reset_n(i_reset_n),

      .ic_l2_req(ic_l2_req),
      .ic_l2_resp(ic_l2_resp),

      .s3_disp(w_iq_disp)
  );

  // msrh_decoder u_decoder (
  //     .i_clk(i_clk),
  //     .i_reset_n(i_reset_n),
  //
  //     .iq_disp(w_iq_disp),
  //     .id_disp(w_id_disp)
  // );


  msrh_rename u_rename (
      .i_clk(i_clk),
      .i_reset_n(i_reset_n),

      .iq_disp(w_iq_disp),
      .i_sc_new_cmt_id (w_sc_new_cmt_id),

      .i_phy_wr (w_ex3_phy_wr),
      .sc_disp  (w_sc_disp)
  );


  generate for (genvar d_idx = 0; d_idx < msrh_pkg::DISP_SIZE; d_idx++) begin : disp_vld_loop
    assign w_disp_valids[d_idx] = w_sc_disp.inst[d_idx].valid;
  end
  endgenerate

  generate
    for (genvar alu_idx = 0; alu_idx < msrh_pkg::ALU_INST_NUM; alu_idx++) begin : alu_loop
      msrh_alu #(
          .PORT_BASE(alu_idx * 2)
      ) u_msrh_alu (
          .i_clk(i_clk),
          .i_reset_n(i_reset_n),

          .disp_valid(w_disp_valids),
          .disp(w_sc_disp),

          .ex1_regread_rs1(regread[alu_idx * 2 + 0]),
          .ex1_regread_rs2(regread[alu_idx * 2 + 1]),

          .i_early_wr(w_ex1_early_wr),
          .i_phy_wr  (w_ex3_phy_wr),

          .o_ex1_early_wr(w_ex1_early_wr[alu_idx]),
          .o_ex3_phy_wr  (w_ex3_phy_wr  [alu_idx]),

          .o_done_report (w_done_rpt[alu_idx])
      );
    end
  endgenerate


generate for (genvar lsu_idx = 0; lsu_idx < msrh_pkg::LSU_INST_NUM; lsu_idx++) begin : lsu_loop

msrh_lsu
  #(
    .PORT_BASE(lsu_idx * 2)
    )
u_msrh_lsu
  (
    .i_clk    (i_clk    ),
    .i_reset_n(i_reset_n),

    .disp_valid (w_disp_valids),
    .disp (w_sc_disp),

    .ex1_regread_rs1 (regread[msrh_pkg::ALU_INST_NUM * 2 + lsu_idx * 2 + 0]),
    .ex1_regread_rs2 (regread[msrh_pkg::ALU_INST_NUM * 2 + lsu_idx * 2 + 1]),

    .i_release(w_ex1_early_wr),
    .i_phy_wr (w_ex3_phy_wr),

    .l1d_if (w_l1d_if[lsu_idx]),
    .l1d_lrq_if (w_l1d_lrq_if[lsu_idx]),

`ifdef QUESTA_SIM
    .o_ex1_early_wr(w_ex1_early_wr[2 + lsu_idx]),
    .o_ex3_phy_wr  (w_ex3_phy_wr  [2 + lsu_idx]),

    .o_done_report(w_done_rpt[2 + lsu_idx])
`else // QUESTA_SIM
    .o_ex1_early_wr(w_ex1_early_wr[msrh_pkg::ALU_INST_NUM + lsu_idx]),
    .o_ex3_phy_wr  (w_ex3_phy_wr  [msrh_pkg::ALU_INST_NUM + lsu_idx]),

    .o_done_report(w_done_rpt[msrh_pkg::ALU_INST_NUM + lsu_idx])
`endif // QUESTA_SIM
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

  msrh_phy_registers #(
      .RD_PORT_SIZE(msrh_pkg::LSU_INST_NUM * 2 +
                    msrh_pkg::ALU_INST_NUM * 2)
  ) u_int_phy_registers (
      .i_clk(i_clk),
      .i_reset_n(i_reset_n),

      .i_phy_wr(w_ex3_phy_wr),
      .regread(regread)
  );

  msrh_rob u_rob
    (
     .i_clk    (i_clk),
     .i_reset_n(i_reset_n),

     .sc_disp (w_sc_disp),
     .i_old_rd_valid (),
     .i_old_rd_rnid  (),

     .o_sc_new_cmt_id (w_sc_new_cmt_id),

     .i_done_rpt (w_done_rpt)
     );

endmodule  // msrh_tile
