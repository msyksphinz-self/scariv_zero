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

  logic [msrh_pkg::DISP_SIZE-1:0] w_disp_valids;
  logic [msrh_pkg::CMT_BLK_W-1:0] w_sc_new_cmt_id;

  msrh_pkg::release_t w_ex1_release[msrh_pkg::REL_BUS_SIZE];
  msrh_pkg::target_t w_ex3_target[msrh_pkg::TGT_BUS_SIZE];

  regread_if regread[4] ();

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

      .i_target (w_ex3_target),
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

          .release_in(w_ex1_release),
          .target_in(w_ex3_target),

          .ex1_release_out(w_ex1_release[alu_idx]),
          .ex3_target_out(w_ex3_target[alu_idx]),

                    .o_done_report (w_done_rpt[alu_idx])
      );
    end
  endgenerate

  msrh_phy_registers #(
      .RD_PORT_SIZE(4)
  ) u_int_phy_registers (
      .i_clk(i_clk),
      .i_reset_n(i_reset_n),

      .target_in(w_ex3_target),
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
