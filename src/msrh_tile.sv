module msrh_tile (
    input logic i_clk,
    input logic i_reset_n,

    // L2 request from ICache
    l2_req_if.master ic_l2_req,
    l2_resp_if.slave ic_l2_resp,

    // L2 request from L1D
    l2_req_if.master l1d_ext_req,
    l2_resp_if.slave l1d_ext_resp
);

localparam ALU_INST_PORT_BASE = 0;
localparam LSU_INST_PORT_BASE = msrh_conf_pkg::ALU_INST_NUM;
localparam BRU_INST_PORT_BASE = LSU_INST_PORT_BASE + msrh_conf_pkg::LSU_INST_NUM;
localparam CSU_INST_PORT_BASE = BRU_INST_PORT_BASE + 1;

localparam ALU_DONE_PORT_BASE = 0;
localparam LSU_DONE_PORT_BASE = msrh_conf_pkg::ALU_INST_NUM;
localparam BRU_DONE_PORT_BASE = LSU_INST_PORT_BASE + 2;
localparam CSU_DONE_PORT_BASE = BRU_DONE_PORT_BASE + 1;

// ----------------------------------
// Global Components
// ----------------------------------
l2_req_if  l2_req ();
l2_resp_if l2_resp ();

disp_if w_iq_disp ();
disp_if w_id_disp ();
disp_if w_sc_disp ();

msrh_pkg::early_wr_t w_ex1_early_wr[msrh_pkg::REL_BUS_SIZE];
msrh_pkg::phy_wr_t   w_ex3_phy_wr  [msrh_pkg::TGT_BUS_SIZE];
logic [msrh_pkg::CMT_BLK_W-1:0] w_sc_new_cmt_id;

regread_if regread[msrh_pkg::REGPORT_NUM] ();

msrh_pkg::done_rpt_t w_done_rpt[msrh_pkg::CMT_BUS_SIZE];

csr_info_if w_csr_info ();

// ----------------------------------
// Committer Components
// ----------------------------------
/* verilator lint_off UNOPTFLAT */
msrh_pkg::commit_blk_t w_commit;
msrh_pkg::cmt_rnid_upd_t w_commit_rnid_update;

// ----------------------------------
// ALU Components
// ----------------------------------
logic [msrh_conf_pkg::DISP_SIZE-1:0] w_disp_alu_valids;
msrh_pkg::early_wr_t w_ex1_alu_early_wr[msrh_conf_pkg::ALU_INST_NUM];
msrh_pkg::phy_wr_t   w_ex3_alu_phy_wr  [msrh_conf_pkg::ALU_INST_NUM];
msrh_pkg::done_rpt_t w_alu_done_rpt    [msrh_conf_pkg::ALU_INST_NUM];

// ----------------------------------
// LSU Components
// ----------------------------------
logic [msrh_conf_pkg::DISP_SIZE-1:0] w_disp_lsu_valids;
msrh_pkg::early_wr_t w_ex1_lsu_early_wr[msrh_conf_pkg::LSU_INST_NUM];
msrh_pkg::phy_wr_t   w_ex3_lsu_phy_wr  [msrh_conf_pkg::LSU_INST_NUM];
msrh_pkg::done_rpt_t w_lsu_done_rpt    [2];
msrh_pkg::mispred_t  w_ex3_mispred_lsu [msrh_conf_pkg::LSU_INST_NUM] ;

// ----------------------------------
// BRU Components
// ----------------------------------
logic [msrh_conf_pkg::DISP_SIZE-1:0] w_disp_bru_valids;
msrh_pkg::early_wr_t w_ex1_bru_early_wr;
msrh_pkg::phy_wr_t   w_ex3_bru_phy_wr  ;
msrh_pkg::done_rpt_t w_bru_done_rpt;
br_upd_if w_ex3_br_upd_if();

// ----------------------------------
// CSU Components
// ----------------------------------
logic [msrh_conf_pkg::DISP_SIZE-1:0] w_disp_csu_valids;
msrh_pkg::early_wr_t w_ex1_csu_early_wr;
msrh_pkg::phy_wr_t   w_ex3_csu_phy_wr  ;
msrh_pkg::done_rpt_t w_csu_done_rpt;

// ----------------------------------
// Merging Forwarding / Done signals
// ----------------------------------
// ALU
generate for (genvar a_idx = 0; a_idx < msrh_conf_pkg::ALU_INST_NUM; a_idx++) begin : alu_reg_loop
  assign w_ex1_early_wr[a_idx] = w_ex1_alu_early_wr[a_idx];
  assign w_ex3_phy_wr  [a_idx] = w_ex3_alu_phy_wr  [a_idx];
  assign w_done_rpt    [a_idx] = w_alu_done_rpt    [a_idx];
end
endgenerate

// LSU
generate for (genvar l_idx = 0; l_idx < msrh_conf_pkg::LSU_INST_NUM; l_idx++) begin : lsu_reg_loop
  assign w_ex1_early_wr[LSU_INST_PORT_BASE + l_idx] = w_ex1_lsu_early_wr[l_idx];
  assign w_ex3_phy_wr  [LSU_INST_PORT_BASE + l_idx] = w_ex3_lsu_phy_wr  [l_idx];
end
endgenerate
assign w_done_rpt    [LSU_DONE_PORT_BASE + 0] = w_lsu_done_rpt[0];
assign w_done_rpt    [LSU_DONE_PORT_BASE + 1] = w_lsu_done_rpt[1];

// BRU
assign w_ex1_early_wr[BRU_INST_PORT_BASE] = w_ex1_bru_early_wr;
assign w_ex3_phy_wr  [BRU_INST_PORT_BASE] = w_ex3_bru_phy_wr  ;
assign w_done_rpt    [BRU_DONE_PORT_BASE] = w_bru_done_rpt;

// CSU
assign w_ex1_early_wr[CSU_INST_PORT_BASE] = w_ex1_csu_early_wr;
assign w_ex3_phy_wr  [CSU_INST_PORT_BASE] = w_ex3_csu_phy_wr  ;
assign w_done_rpt    [CSU_DONE_PORT_BASE] = w_csu_done_rpt;


msrh_frontend u_frontend (
  .i_clk(i_clk),
  .i_reset_n(i_reset_n),

  .ic_l2_req(ic_l2_req),
  .ic_l2_resp(ic_l2_resp),

  .i_commit (w_commit),

  .csr_info (w_csr_info),

  .s3_disp (w_iq_disp)
);

  // msrh_decoder u_decoder (
  //     .i_clk(i_clk),
  //     .i_reset_n(i_reset_n),
  //
  //     .iq_disp(w_iq_disp),
  //     .id_disp(w_id_disp)
  // );


msrh_rename u_msrh_rename (
  .i_clk(i_clk),
  .i_reset_n(i_reset_n),

  .iq_disp(w_iq_disp),
  .i_sc_new_cmt_id (w_sc_new_cmt_id),

  .i_commit_rnid_update (w_commit_rnid_update),

  .i_phy_wr (w_ex3_phy_wr),
  .sc_disp  (w_sc_disp)
);


  generate for (genvar d_idx = 0; d_idx < msrh_conf_pkg::DISP_SIZE; d_idx++) begin : disp_valid_loop
    assign w_disp_alu_valids[d_idx] = w_sc_disp.valid && w_sc_disp.inst[d_idx].valid &&
                                      (w_sc_disp.inst[d_idx].cat == decoder_inst_cat_pkg::INST_CAT_ARITH);
    assign w_disp_lsu_valids[d_idx] = w_sc_disp.valid && w_sc_disp.inst[d_idx].valid &&
                                      (w_sc_disp.inst[d_idx].cat == decoder_inst_cat_pkg::INST_CAT_LD ||
                                       w_sc_disp.inst[d_idx].cat == decoder_inst_cat_pkg::INST_CAT_ST);
    assign w_disp_bru_valids[d_idx] = w_sc_disp.valid && w_sc_disp.inst[d_idx].valid &&
                                      (w_sc_disp.inst[d_idx].cat == decoder_inst_cat_pkg::INST_CAT_BR);
    assign w_disp_csu_valids[d_idx] = w_sc_disp.valid && w_sc_disp.inst[d_idx].valid &&
                                      (w_sc_disp.inst[d_idx].cat == decoder_inst_cat_pkg::INST_CAT_CSU);
  end
  endgenerate

  generate
    for (genvar alu_idx = 0; alu_idx < msrh_conf_pkg::ALU_INST_NUM; alu_idx++) begin : alu_loop
      msrh_alu #(
          .PORT_BASE(alu_idx * 2)
      ) u_msrh_alu (
          .i_clk(i_clk),
          .i_reset_n(i_reset_n),

          .disp_valid(w_disp_alu_valids),
          .disp(w_sc_disp),

          .ex1_regread_rs1(regread[alu_idx * 2 + 0]),
          .ex1_regread_rs2(regread[alu_idx * 2 + 1]),

          .i_early_wr(w_ex1_early_wr),
          .i_phy_wr  (w_ex3_phy_wr),
          .i_mispred_lsu (w_ex3_mispred_lsu),

          .o_ex1_early_wr(w_ex1_alu_early_wr[alu_idx]),
          .o_ex3_phy_wr  (w_ex3_alu_phy_wr  [alu_idx]),

          .i_commit (w_commit),

          .o_done_report (w_alu_done_rpt[alu_idx])
      );
    end
  endgenerate


msrh_lsu_top
u_msrh_lsu_top
  (
    .i_clk    (i_clk    ),
    .i_reset_n(i_reset_n),

    .disp_valid (w_disp_lsu_valids),
    .disp (w_sc_disp),

    .ex1_regread (regread[(msrh_conf_pkg::ALU_INST_NUM * 2) +: (msrh_conf_pkg::LSU_INST_NUM * 2)]),

    .l1d_ext_req  (l1d_ext_req ),
    .l1d_ext_resp (l1d_ext_resp),

    .i_early_wr(w_ex1_early_wr),
    .i_phy_wr  (w_ex3_phy_wr),

    .o_ex1_early_wr(w_ex1_lsu_early_wr),
    .o_ex3_phy_wr  (w_ex3_lsu_phy_wr  ),

    .o_done_report(w_lsu_done_rpt),
    .o_ex3_mispred (w_ex3_mispred_lsu),

    .i_commit (w_commit)
   );


msrh_bru
u_msrh_bru (
    .i_clk(i_clk),
    .i_reset_n(i_reset_n),

    .disp_valid(w_disp_bru_valids),
    .disp(w_sc_disp),

    .ex1_regread_rs1(regread[msrh_conf_pkg::ALU_INST_NUM * 2 +
                             msrh_conf_pkg::LSU_INST_NUM * 2 +
                             0]),
    .ex1_regread_rs2(regread[msrh_conf_pkg::ALU_INST_NUM * 2 +
                             msrh_conf_pkg::LSU_INST_NUM * 2 +
                             1]),

    .i_early_wr(w_ex1_early_wr),
    .i_phy_wr  (w_ex3_phy_wr),
    .i_mispred_lsu (w_ex3_mispred_lsu),

    .o_ex1_early_wr(w_ex1_bru_early_wr),
    .o_ex3_phy_wr  (w_ex3_bru_phy_wr  ),

    .o_done_report (w_bru_done_rpt),
    .i_commit      (w_commit),
    .ex3_br_upd_if (w_ex3_br_upd_if)
);


msrh_csu
u_msrh_csu (
    .i_clk(i_clk),
    .i_reset_n(i_reset_n),

    .disp_valid(w_disp_csu_valids),
    .disp(w_sc_disp),

    .ex1_regread_rs1(regread[msrh_conf_pkg::ALU_INST_NUM * 2 +
                             msrh_conf_pkg::LSU_INST_NUM * 2 +
                             + 2]),

    .i_early_wr(w_ex1_early_wr),
    .i_phy_wr  (w_ex3_phy_wr),

    .o_ex1_early_wr(w_ex1_csu_early_wr),
    .o_ex3_phy_wr  (w_ex3_csu_phy_wr  ),
    .i_mispred_lsu (w_ex3_mispred_lsu),

    .csr_info (w_csr_info),

    .o_done_report (w_csu_done_rpt),

    .i_commit (w_commit)

);


msrh_phy_registers #(
    .RD_PORT_SIZE(msrh_pkg::REGPORT_NUM)
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

   .o_sc_new_cmt_id (w_sc_new_cmt_id),

   .i_done_rpt (w_done_rpt),

   .o_commit (w_commit),
   .o_commit_rnid_update (w_commit_rnid_update),

   .ex3_br_upd_if (w_ex3_br_upd_if)
   );

endmodule  // msrh_tile
