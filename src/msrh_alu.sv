module msrh_alu #(
    parameter PORT_BASE = 0
) (
    input logic i_clk,
    input logic i_reset_n,

    input logic         [msrh_pkg::DISP_SIZE-1:0] disp_valid,
    disp_if.slave                          disp,

    regread_if.master ex1_regread_rs1,
    regread_if.master ex1_regread_rs2,

    /* Forwarding path */
    input msrh_pkg::early_wr_t i_early_wr[msrh_pkg::REL_BUS_SIZE],
    input msrh_pkg::phy_wr_t   i_phy_wr [msrh_pkg::TGT_BUS_SIZE],

    /* write output */
    output msrh_pkg::early_wr_t o_ex1_early_wr,
    output msrh_pkg::phy_wr_t   o_ex3_phy_wr,

    output msrh_pkg::done_rpt_t o_done_report
);

msrh_pkg::disp_t w_disp_inst[msrh_pkg::DISP_SIZE];
msrh_pkg::disp_t disp_picked_inst[2];
logic [1:0] disp_picked_inst_valid;
logic [msrh_pkg::DISP_SIZE-1:0] disp_picked_grp_id[2];

  msrh_pkg::issue_t w_rv0_issue;
logic [msrh_pkg::RV_ALU_ENTRY_SIZE-1:0] w_rv0_index;

logic         w_ex3_done;
logic [msrh_pkg::RV_ALU_ENTRY_SIZE-1:0] w_ex3_index;

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
          .o_data  (disp_picked_inst[p_idx]),
          .o_picked_pos (disp_picked_grp_id[p_idx])
      );
    end  // block: d_loop
  endgenerate

  msrh_scheduler #(
      .ENTRY_SIZE  (msrh_pkg::RV_ALU_ENTRY_SIZE),
      .IN_PORT_SIZE(2)
  ) u_msrh_scheduler
    (
     .i_clk    (i_clk),
     .i_reset_n(i_reset_n),

     .i_disp_valid(disp_picked_inst_valid),
     .i_cmt_id    (disp.cmt_id),
     .i_grp_id    (disp_picked_grp_id),
     .i_disp_info (disp_picked_inst),

     .i_early_wr(i_early_wr),

     .o_issue(w_rv0_issue),
     .o_iss_index(w_rv0_index),

     .i_pipe_done(w_ex3_done),
     .i_done_index(w_ex3_index),

     .o_done_report (o_done_report)
  );


  msrh_alu_pipe
    #(
      .RV_ENTRY_SIZE(msrh_pkg::RV_ALU_ENTRY_SIZE)
      )
  u_alu
    (
     .i_clk    (i_clk),
     .i_reset_n(i_reset_n),

     .rv0_issue(w_rv0_issue),
     .rv0_index(w_rv0_index),
     .ex1_i_phy_wr(i_phy_wr),

     .ex1_regread_rs1(ex1_regread_rs1),
     .ex1_regread_rs2(ex1_regread_rs2),

     .o_ex1_early_wr(o_ex1_early_wr),
     .o_ex3_phy_wr (o_ex3_phy_wr),

     .o_ex3_done (w_ex3_done),
     .o_ex3_index (w_ex3_index)
  );


endmodule  // msrh_alu
