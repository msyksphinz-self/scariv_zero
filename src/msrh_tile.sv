module msrh_tile (
    input logic i_clk,
    input logic i_reset_n,

    // L2 request from ICache
    l2_req_if.master ic_l2_req,
    l2_resp_if.slave ic_l2_resp,

    // L2 request from L1D
    l2_req_if.master l1d_ext_req,
    l2_resp_if.slave l1d_ext_resp,

    // Cache Coherent Interface
    snoop_if.slave snoop_if,

    // PTW interconnection
    l2_req_if.master ptw_req,
    l2_resp_if.slave ptw_resp
);

localparam ALU_INST_PORT_BASE = 0;
localparam LSU_INST_PORT_BASE = msrh_conf_pkg::ALU_INST_NUM;
localparam BRU_INST_PORT_BASE = LSU_INST_PORT_BASE + msrh_conf_pkg::LSU_INST_NUM;
localparam CSU_INST_PORT_BASE = BRU_INST_PORT_BASE + 1;
localparam FPU_INST_PORT_BASE = CSU_INST_PORT_BASE + 1;

localparam ALU_DONE_PORT_BASE = 0;
localparam LSU_DONE_PORT_BASE = msrh_conf_pkg::ALU_INST_NUM;
localparam BRU_DONE_PORT_BASE = LSU_INST_PORT_BASE + msrh_conf_pkg::LSU_INST_NUM;
localparam CSU_DONE_PORT_BASE = BRU_DONE_PORT_BASE + 1;
localparam FPU_DONE_PORT_BASE = CSU_DONE_PORT_BASE + 1;

// ----------------------------------
// Global Components
// ----------------------------------
l2_req_if  l2_req ();
l2_resp_if l2_resp ();

disp_if w_iq_disp ();
disp_if w_iq_dist_disp[2]();  // Int/FP
disp_if w_id_disp ();
disp_if w_sc_int_disp ();
disp_if w_sc_fp_disp ();
disp_if w_sc_disp ();

msrh_pkg::early_wr_t w_ex1_early_wr[msrh_pkg::REL_BUS_SIZE];
msrh_pkg::phy_wr_t   w_ex3_phy_wr  [msrh_pkg::TGT_BUS_SIZE];
msrh_pkg::cmt_id_t w_sc_new_cmt_id;

regread_if int_regread[msrh_pkg::INT_REGPORT_NUM] ();
regread_if fp_regread [msrh_pkg::FP_REGPORT_NUM] ();

msrh_pkg::done_rpt_t w_done_rpt[msrh_pkg::CMT_BUS_SIZE];

csr_info_if w_csr_info ();
interrupt_if w_int_if();
rob_info_if w_rob_info_if();
tlb_ptw_if  w_ptw_if[1 + msrh_conf_pkg::LSU_INST_NUM]();
lsu_access_if w_lsu_access();
sfence_if     w_sfence_if();
logic                          w_fence_i;

logic [$clog2(msrh_conf_pkg::RAS_ENTRY_SIZE)-1: 0] w_sc_ras_index;
logic [riscv_pkg::VADDR_W-1: 0]                    w_sc_ras_vaddr;

// ----------------------------------
// Committer Components
// ----------------------------------
/* verilator lint_off UNOPTFLAT */
msrh_pkg::commit_blk_t     w_commit;
msrh_pkg::cmt_rnid_upd_t   w_commit_rnid_update;

// ----------------------------------
// ALU Components
// ----------------------------------
msrh_pkg::grp_id_t   w_disp_alu_valids [msrh_conf_pkg::ALU_INST_NUM];
msrh_pkg::early_wr_t w_ex1_alu_early_wr[msrh_conf_pkg::ALU_INST_NUM];
msrh_pkg::phy_wr_t   w_ex3_alu_phy_wr  [msrh_conf_pkg::ALU_INST_NUM];
msrh_pkg::done_rpt_t w_alu_done_rpt    [msrh_conf_pkg::ALU_INST_NUM];


// ----------------------------------
// LSU Components
// ----------------------------------
msrh_pkg::grp_id_t        w_disp_lsu_valids;
msrh_pkg::early_wr_t      w_ex1_lsu_early_wr      [msrh_conf_pkg::LSU_INST_NUM];
msrh_pkg::phy_wr_t        w_ex3_lsu_phy_wr        [msrh_conf_pkg::LSU_INST_NUM];
msrh_pkg::done_rpt_t      w_lsu_done_rpt          [msrh_conf_pkg::LSU_INST_NUM];
msrh_pkg::mispred_t       w_ex2_mispred_lsu       [msrh_conf_pkg::LSU_INST_NUM];
msrh_pkg::another_flush_t w_lsu_another_flush_rpt [msrh_conf_pkg::LSU_INST_NUM];
// ----------------------------------
// BRU Components
// ----------------------------------
msrh_pkg::grp_id_t   w_disp_bru_valids;
msrh_pkg::early_wr_t w_ex1_bru_early_wr;
msrh_pkg::phy_wr_t   w_ex3_bru_phy_wr  ;
msrh_pkg::done_rpt_t w_bru_done_rpt;
br_upd_if w_ex3_br_upd_if();
br_upd_if br_upd_fe_if ();

// ----------------------------------
// CSU Components
// ----------------------------------
msrh_pkg::grp_id_t   w_disp_csu_valids;
msrh_pkg::early_wr_t w_ex1_csu_early_wr;
msrh_pkg::phy_wr_t   w_ex3_csu_phy_wr  ;
msrh_pkg::done_rpt_t w_csu_done_rpt;

// ----------------------------------
// FPU Components
// ----------------------------------
msrh_pkg::grp_id_t   w_disp_fpu_valids [msrh_conf_pkg::FPU_INST_NUM];
msrh_pkg::early_wr_t w_ex1_fpu_early_wr[msrh_conf_pkg::FPU_INST_NUM];
msrh_pkg::phy_wr_t   w_ex3_fpu_phy_wr  [msrh_conf_pkg::FPU_INST_NUM];
msrh_pkg::done_rpt_t w_fpu_done_rpt    [msrh_conf_pkg::FPU_INST_NUM];

// -------------------------------
// Internal Broadcast Interface
// -------------------------------
l1d_snoop_if l1d_snoop_if();
stq_snoop_if stq_snoop_if();

// ----------------------------------
// Credit/Return Management
// ----------------------------------
logic                                w_resource_ok;
cre_ret_if #(.MAX_INC(msrh_conf_pkg::CMT_ENTRY_SIZE   )) rob_cre_ret_if();
cre_ret_if #(.MAX_INC(msrh_conf_pkg::RV_ALU_ENTRY_SIZE)) alu_cre_ret_if[msrh_conf_pkg::ALU_INST_NUM]();
cre_ret_if #(.MAX_INC(msrh_conf_pkg::LDQ_SIZE         )) ldq_cre_ret_if();
cre_ret_if #(.MAX_INC(msrh_conf_pkg::STQ_SIZE         )) stq_cre_ret_if();
cre_ret_if #(.MAX_INC(msrh_conf_pkg::RV_BRU_ENTRY_SIZE)) bru_cre_ret_if();
cre_ret_if #(.MAX_INC(msrh_conf_pkg::RV_CSU_ENTRY_SIZE)) csu_cre_ret_if();
cre_ret_if #(.MAX_INC(msrh_conf_pkg::RV_FPU_ENTRY_SIZE)) fpu_cre_ret_if[msrh_conf_pkg::FPU_INST_NUM]();

// ----------------------------------
// Branch Tag
// ----------------------------------

msrh_pkg::brtag_t  w_iq_brtag  [msrh_conf_pkg::DISP_SIZE];
msrh_pkg::brmask_t w_iq_brmask [msrh_conf_pkg::DISP_SIZE];
cmt_brtag_if w_cmt_brtag_if();

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
  assign w_done_rpt    [LSU_DONE_PORT_BASE + l_idx] = w_lsu_done_rpt    [l_idx];
end
endgenerate

// BRU
assign w_ex1_early_wr[BRU_INST_PORT_BASE] = w_ex1_bru_early_wr;
assign w_ex3_phy_wr  [BRU_INST_PORT_BASE] = w_ex3_bru_phy_wr  ;
assign w_done_rpt    [BRU_DONE_PORT_BASE] = w_bru_done_rpt;

// CSU
assign w_ex1_early_wr[CSU_INST_PORT_BASE] = w_ex1_csu_early_wr;
assign w_ex3_phy_wr  [CSU_INST_PORT_BASE] = w_ex3_csu_phy_wr  ;
assign w_done_rpt    [CSU_DONE_PORT_BASE] = w_csu_done_rpt;

// FPU
generate for (genvar f_idx = 0; f_idx < msrh_conf_pkg::FPU_INST_NUM; f_idx++) begin : fpu_reg_loop
  assign w_ex1_early_wr[FPU_INST_PORT_BASE + f_idx] = w_ex1_fpu_early_wr[f_idx];
  assign w_ex3_phy_wr  [FPU_INST_PORT_BASE + f_idx] = w_ex3_fpu_phy_wr  [f_idx];
  assign w_done_rpt    [FPU_INST_PORT_BASE + f_idx] = w_fpu_done_rpt    [f_idx];
end
endgenerate


msrh_frontend u_frontend (
  .i_clk(i_clk),
  .i_reset_n(i_reset_n),

  .sfence_if (w_sfence_if),
  .i_fence_i (w_fence_i),

  .ic_l2_req(ic_l2_req),
  .ic_l2_resp(ic_l2_resp),

  .i_commit (w_commit),
  .br_upd_if (w_ex3_br_upd_if),

  .csr_info (w_csr_info),
  .int_if   (w_int_if),

  .iq_disp (w_iq_disp),
  .sc_disp (w_sc_int_disp),
  .o_sc_ras_index  (w_sc_ras_index),
  .o_sc_ras_vaddr (w_sc_ras_vaddr),

   // Fetch Target Queue
  .br_upd_fe_if (br_upd_fe_if),

  .ptw_if (w_ptw_if[0])
);


msrh_disp_distribute
u_iq_dist
(
 .i_disp (w_iq_disp),
 .o_disp (w_iq_dist_disp)
 );

msrh_rename
  #(.REG_TYPE(msrh_pkg::GPR))
u_msrh_int_rename (
  .i_clk(i_clk),
  .i_reset_n(i_reset_n),

  .iq_disp(w_iq_dist_disp[0]),
  .i_sc_new_cmt_id (w_sc_new_cmt_id),

  .i_commit             (w_commit),
  .i_commit_rnid_update (w_commit_rnid_update),

  .i_resource_ok (w_resource_ok),
  .i_brtag  (w_iq_brtag),
  .i_brmask (w_iq_brmask),

  .br_upd_if (br_upd_fe_if /* w_ex3_br_upd_if*/),

  .i_phy_wr (w_ex3_phy_wr),
  .sc_disp  (w_sc_int_disp),
  .i_sc_ras_index (w_sc_ras_index),
  .i_sc_ras_vaddr (w_sc_ras_vaddr)
);


msrh_rename
  #(.REG_TYPE(msrh_pkg::FPR))
u_msrh_fp_rename (
  .i_clk(i_clk),
  .i_reset_n(i_reset_n),

  .iq_disp(w_iq_dist_disp[1]),
  .i_sc_new_cmt_id (w_sc_new_cmt_id),

  .i_commit             (w_commit),
  .i_commit_rnid_update (w_commit_rnid_update),

  .i_resource_ok (w_resource_ok),
  .i_brtag  (w_iq_brtag),
  .i_brmask (w_iq_brmask),

  .br_upd_if (br_upd_fe_if /* w_ex3_br_upd_if*/),

  .i_phy_wr (w_ex3_phy_wr),
  .sc_disp  (w_sc_fp_disp),
  .i_sc_ras_index (w_sc_ras_index),
  .i_sc_ras_vaddr (w_sc_ras_vaddr)
);




msrh_resource_alloc u_msrh_resource_alloc
(
  .i_clk(i_clk),
  .i_reset_n(i_reset_n),

  .iq_disp(w_iq_disp),

  .rob_cre_ret_if (rob_cre_ret_if),
  .alu_cre_ret_if (alu_cre_ret_if),
  .ldq_cre_ret_if (ldq_cre_ret_if),
  .stq_cre_ret_if (stq_cre_ret_if),
  .csu_cre_ret_if (csu_cre_ret_if),
  .bru_cre_ret_if (bru_cre_ret_if),
  .fpu_cre_ret_if (fpu_cre_ret_if),

  .br_upd_if (br_upd_fe_if /* w_ex3_br_upd_if */),

  .i_commit (w_commit),
  .cmt_brtag_if (w_cmt_brtag_if),

  .o_brtag  (w_iq_brtag),
  .o_brmask (w_iq_brmask),

  .o_resource_ok (w_resource_ok)
 );

msrh_disp_merge
u_sc_merge
  (
   .i_int_disp (w_sc_int_disp),
   .i_fp_disp  (w_sc_fp_disp),
   .o_disp     (w_sc_disp)
   );

localparam ALU_PORT_SIZE = msrh_conf_pkg::ARITH_DISP_SIZE / msrh_conf_pkg::ALU_INST_NUM;
localparam FPU_PORT_SIZE = msrh_conf_pkg::FPU_DISP_SIZE / msrh_conf_pkg::FPU_INST_NUM;

generate for (genvar d_idx = 0; d_idx < msrh_conf_pkg::DISP_SIZE; d_idx++) begin : disp_valid_loop
  for (genvar a_idx = 0; a_idx < msrh_conf_pkg::ALU_INST_NUM; a_idx++) begin: alu_disp_valid_loop
    assign w_disp_alu_valids[a_idx][d_idx] = w_sc_disp.valid & w_sc_disp.inst[d_idx].valid & !w_sc_disp.inst[d_idx].illegal_valid &
                                             w_sc_disp.resource_cnt.alu_inst_valid[a_idx][d_idx];
  end

  assign w_disp_lsu_valids[d_idx] = w_sc_disp.valid && w_sc_disp.inst[d_idx].valid && !w_sc_disp.inst[d_idx].illegal_valid &&
                                    (w_sc_disp.inst[d_idx].cat == decoder_inst_cat_pkg::INST_CAT_LD ||
                                     w_sc_disp.inst[d_idx].cat == decoder_inst_cat_pkg::INST_CAT_ST);
  assign w_disp_bru_valids[d_idx] = w_sc_disp.valid && w_sc_disp.inst[d_idx].valid && !w_sc_disp.inst[d_idx].illegal_valid &&
                                    (w_sc_disp.inst[d_idx].cat == decoder_inst_cat_pkg::INST_CAT_BR);
  assign w_disp_csu_valids[d_idx] = w_sc_disp.valid && w_sc_disp.inst[d_idx].valid && !w_sc_disp.inst[d_idx].illegal_valid &&
                                    (w_sc_disp.inst[d_idx].cat == decoder_inst_cat_pkg::INST_CAT_CSU);
  for (genvar f_idx = 0; f_idx < msrh_conf_pkg::FPU_INST_NUM; f_idx++) begin: fpu_disp_valid_loop
    assign w_disp_fpu_valids[f_idx][d_idx] = w_sc_disp.valid & w_sc_disp.inst[d_idx].valid & !w_sc_disp.inst[d_idx].illegal_valid &&
                                             w_sc_disp.resource_cnt.fpu_inst_valid[f_idx][d_idx];
  end
end
endgenerate


generate for (genvar alu_idx = 0; alu_idx < msrh_conf_pkg::ALU_INST_NUM; alu_idx++) begin : alu_loop
  msrh_alu #(
      .PORT_BASE(alu_idx)
  ) u_msrh_alu (
      .i_clk(i_clk),
      .i_reset_n(i_reset_n),

      .rob_info_if   (w_rob_info_if),

      .disp_valid(w_disp_alu_valids[alu_idx]),
      .disp(w_sc_disp),
      .cre_ret_if (alu_cre_ret_if[alu_idx]),

      .ex1_regread_rs1(int_regread[alu_idx * 2 + 0]),
      .ex1_regread_rs2(int_regread[alu_idx * 2 + 1]),

      .i_early_wr(w_ex1_early_wr),
      .i_phy_wr  (w_ex3_phy_wr),
      .i_mispred_lsu (w_ex2_mispred_lsu),

      .o_ex1_early_wr(w_ex1_alu_early_wr[alu_idx]),
      .o_ex3_phy_wr  (w_ex3_alu_phy_wr  [alu_idx]),

      .i_commit  (w_commit),
      .br_upd_if (br_upd_fe_if /* w_ex3_br_upd_if*/),

      .o_done_report (w_alu_done_rpt[alu_idx])
  );
end
endgenerate


msrh_lsu_top
u_msrh_lsu_top
  (
    .i_clk    (i_clk    ),
    .i_reset_n(i_reset_n),

    .rob_info_if   (w_rob_info_if),
    .sfence_if     (w_sfence_if),

    .csr_info (w_csr_info),

    .disp_valid (w_disp_lsu_valids),
    .disp (w_sc_disp),
    // .sch_cre_ret_if (lsu_cre_ret_if),
    .ldq_cre_ret_if (ldq_cre_ret_if),
    .stq_cre_ret_if (stq_cre_ret_if),

    .ex1_regread (int_regread[(msrh_conf_pkg::ALU_INST_NUM * 2) +: (msrh_conf_pkg::LSU_INST_NUM * 2)]),

    .ptw_if       (w_ptw_if[1 +: msrh_conf_pkg::LSU_INST_NUM]),
    .lsu_access   (w_lsu_access),

    .l1d_ext_req  (l1d_ext_req ),
    .l1d_ext_resp (l1d_ext_resp),

    .i_early_wr(w_ex1_early_wr),
    .i_phy_wr  (w_ex3_phy_wr),

    .o_ex1_early_wr(w_ex1_lsu_early_wr),
    .o_ex3_phy_wr  (w_ex3_lsu_phy_wr  ),

    .o_done_report(w_lsu_done_rpt),
    .o_another_flush_report(w_lsu_another_flush_rpt),
    .o_ex2_mispred (w_ex2_mispred_lsu),

    .l1d_snoop_if (l1d_snoop_if),
    .stq_snoop_if (stq_snoop_if),

    .i_commit  (w_commit),
    .br_upd_if (br_upd_fe_if /* w_ex3_br_upd_if*/)
   );


msrh_bru
u_msrh_bru (
    .i_clk(i_clk),
    .i_reset_n(i_reset_n),

    .rob_info_if   (w_rob_info_if),

    .disp_valid(w_disp_bru_valids),
    .disp(w_sc_disp),
    .cre_ret_if (bru_cre_ret_if),

    .ex1_regread_rs1(int_regread[msrh_conf_pkg::ALU_INST_NUM * 2 +
                                 msrh_conf_pkg::LSU_INST_NUM * 2 +
                                 0]),
    .ex1_regread_rs2(int_regread[msrh_conf_pkg::ALU_INST_NUM * 2 +
                                 msrh_conf_pkg::LSU_INST_NUM * 2 +
                                 1]),

    .i_early_wr(w_ex1_early_wr),
    .i_phy_wr  (w_ex3_phy_wr),
    .i_mispred_lsu (w_ex2_mispred_lsu),

    .o_ex1_early_wr(w_ex1_bru_early_wr),
    .o_ex3_phy_wr  (w_ex3_bru_phy_wr  ),

    .o_done_report (w_bru_done_rpt),
    .i_commit      (w_commit),
    .ex3_br_upd_if (w_ex3_br_upd_if),
    .ex3_br_upd_slave_if (br_upd_fe_if)
);


msrh_csu
u_msrh_csu (
    .i_clk(i_clk),
    .i_reset_n(i_reset_n),

    .disp_valid(w_disp_csu_valids),
    .disp(w_sc_disp),
    .cre_ret_if (csu_cre_ret_if),

    .ex1_regread_rs1(int_regread[msrh_conf_pkg::ALU_INST_NUM * 2 +
                                 msrh_conf_pkg::LSU_INST_NUM * 2 +
                                 2]),

    .i_early_wr(w_ex1_early_wr),
    .i_phy_wr  (w_ex3_phy_wr),

    .o_ex1_early_wr(w_ex1_csu_early_wr),
    .o_ex3_phy_wr  (w_ex3_csu_phy_wr  ),
    .i_mispred_lsu (w_ex2_mispred_lsu),

    .csr_info    (w_csr_info   ),
    .int_if      (w_int_if),
    .rob_info_if (w_rob_info_if),

    .sfence_if (w_sfence_if),
    .o_fence_i (w_fence_i),

    .o_done_report (w_csu_done_rpt),

    .i_commit (w_commit),
    .br_upd_if (br_upd_fe_if /* w_ex3_br_upd_if*/)
);


msrh_phy_registers
  #(
    .REG_TYPE(msrh_pkg::GPR),
    .RD_PORT_SIZE(msrh_pkg::INT_REGPORT_NUM)
    )
u_int_phy_registers (
    .i_clk(i_clk),
    .i_reset_n(i_reset_n),

    .i_phy_wr(w_ex3_phy_wr),
    .regread(int_regread)
);


// =========================
// FPU: Flaoting Point Unit
// =========================
generate for (genvar fpu_idx = 0; fpu_idx < msrh_conf_pkg::FPU_INST_NUM; fpu_idx++) begin : fpu_loop
  msrh_fpu #(
    .PORT_BASE(fpu_idx)
  ) u_msrh_fpu (
    .i_clk(i_clk),
    .i_reset_n(i_reset_n),

    .rob_info_if   (w_rob_info_if),

    .disp_valid(w_disp_fpu_valids[fpu_idx]),
    .disp(w_sc_disp),
    .cre_ret_if (fpu_cre_ret_if[fpu_idx]),

    .ex1_regread_int_rs1(int_regread[msrh_conf_pkg::ALU_INST_NUM * 2 +
                                     msrh_conf_pkg::LSU_INST_NUM * 2 +
                                     2 + 1 +
                                     fpu_idx]),

    .ex1_regread_rs1(fp_regread[fpu_idx * 3 + 0]),
    .ex1_regread_rs2(fp_regread[fpu_idx * 3 + 1]),
    .ex1_regread_rs3(fp_regread[fpu_idx * 3 + 2]),

    .i_early_wr(w_ex1_early_wr),
    .i_phy_wr  (w_ex3_phy_wr),
    .i_mispred_lsu (w_ex2_mispred_lsu),

    .o_ex1_early_wr(w_ex1_fpu_early_wr[fpu_idx]),
    .o_ex3_phy_wr  (w_ex3_fpu_phy_wr  [fpu_idx]),

    .i_commit  (w_commit),
    .br_upd_if (w_ex3_br_upd_if),

    .o_done_report (w_fpu_done_rpt[fpu_idx])
  );
end
endgenerate

// --------------------------------------
// FPU: Floating Point Physical Register
// --------------------------------------
msrh_phy_registers
  #(
    .REG_TYPE(msrh_pkg::FPR),
    .RD_PORT_SIZE(msrh_pkg::FP_REGPORT_NUM)
    )
u_fp_phy_registers
  (
   .i_clk(i_clk),
   .i_reset_n(i_reset_n),

   .i_phy_wr(w_ex3_phy_wr),
   .regread(fp_regread)
   );


msrh_rob u_rob
  (
   .i_clk    (i_clk),
   .i_reset_n(i_reset_n),

   .sc_disp    (w_sc_disp     ),
   .cre_ret_if (rob_cre_ret_if),

   .o_sc_new_cmt_id (w_sc_new_cmt_id),

   .i_done_rpt (w_done_rpt),
   .i_another_flush_report(w_lsu_another_flush_rpt),

   .o_commit (w_commit),
   .o_commit_rnid_update (w_commit_rnid_update),
   .cmt_brtag_if (w_cmt_brtag_if),

   .rob_info_if   (w_rob_info_if),

   .ex3_br_upd_if (br_upd_fe_if /* w_ex3_br_upd_if*/)
   );


msrh_ptw u_ptw
  (
   .i_clk    (i_clk),
   .i_reset_n(i_reset_n),

   .ptw_if   (w_ptw_if),

   .lsu_access (w_lsu_access),

   .ptw_req  (ptw_req ),
   .ptw_resp (ptw_resp)
   );


// Snoop Unit
msrh_snoop_top u_snoop_top
(
 .i_clk     (i_clk    ),
 .i_reset_n (i_reset_n),

 .snoop_if       (snoop_if),

 .l1d_snoop_if (l1d_snoop_if),
 .stq_snoop_if (stq_snoop_if)
 );


endmodule  // msrh_tile
