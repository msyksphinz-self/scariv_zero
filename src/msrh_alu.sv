module msrh_alu #(
    parameter PORT_BASE = 0
) (
    input logic i_clk,
    input logic i_reset_n,

    input logic         [msrh_pkg::DISP_SIZE-1:0] disp_valid,
          disp_if.slave                          disp,

    regread_if.master ex0_regread_rs1,
    regread_if.master ex0_regread_rs2,

    /* Forwarding path */
    input msrh_pkg::release_t release_in[msrh_pkg::REL_BUS_SIZE],
    input msrh_pkg::target_t  target_in [msrh_pkg::TGT_BUS_SIZE],

    /* write output */
    output msrh_pkg::release_t ex1_release_out,
    output msrh_pkg::target_t  ex3_target_out
);

  msrh_pkg::disp_t w_disp_inst[msrh_pkg::DISP_SIZE];
  msrh_pkg::disp_t disp_picked_inst[2];
  logic [1:0] disp_picked_inst_valid;
  msrh_pkg::issue_t w_rv0_issue;


  generate for(genvar d_idx = 0; d_idx < msrh_pkg::DISP_SIZE; d_idx++) begin : d_loop
  assign w_disp_inst[d_idx] = disp.inst[d_idx];
end
endgenerate

  generate
    for (genvar p_idx = 0; p_idx < 2; p_idx++) begin : pick_loop
      bit_pick_1_index #(
          .NUM(PORT_BASE + p_idx),
          .SEL_WIDTH(msrh_pkg::DISP_SIZE),
          .DATA_WIDTH($size(msrh_pkg::disp_t))
      ) u_bit_pick_1_index (
          .i_valids(disp_valid),
          .i_data  (w_disp_inst),
          .o_valid (disp_picked_inst_valid[p_idx]),
          .o_data  (disp_picked_inst[p_idx])
      );
    end  // block: d_loop
  endgenerate

  msrh_scheduler #(
      .ENTRY_SIZE  (32),
      .IN_PORT_SIZE(2)
  ) u_msrh_scheduler (
      .i_clk    (i_clk),
      .i_reset_n(i_reset_n),

      .i_disp_valid(disp_picked_inst_valid),
      .i_disp_info (disp_picked_inst),

      .release_in(release_in),

      .o_issue(w_rv0_issue)
  );


  msrh_alu_pipe u_alu (
      .i_clk    (i_clk),
      .i_reset_n(i_reset_n),

      .rv0_issue(w_rv0_issue),
      .ex1_target_in(target_in),

      .ex0_regread_rs1(ex0_regread_rs1),
      .ex0_regread_rs2(ex0_regread_rs2),

      .ex1_release_out(ex1_release_out),
      .ex3_target_out (ex3_target_out)
  );


endmodule  // msrh_alu
