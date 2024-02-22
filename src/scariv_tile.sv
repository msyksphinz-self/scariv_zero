// ------------------------------------------------------------------------
// NAME : scariv_tile
// TYPE : module
// ------------------------------------------------------------------------
// Tile top
// ------------------------------------------------------------------------
//
// ------------------------------------------------------------------------

module scariv_tile (
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
    l2_resp_if.slave ptw_resp,

    // CLINT connection
    clint_if.slave clint_if,
    // PLIC connection
    plic_if.slave plic_if
);

localparam ALU_INST_PORT_BASE = 0;
localparam LSU_INST_PORT_BASE = scariv_conf_pkg::ALU_INST_NUM;
localparam BRU_INST_PORT_BASE = LSU_INST_PORT_BASE + scariv_conf_pkg::LSU_INST_NUM;
localparam CSU_INST_PORT_BASE = BRU_INST_PORT_BASE + 1;
localparam FPU_INST_PORT_BASE = CSU_INST_PORT_BASE + 1;

localparam ALU_DONE_PORT_BASE = 0;
localparam LSU_DONE_PORT_BASE = scariv_conf_pkg::ALU_INST_NUM;
localparam BRU_DONE_PORT_BASE = LSU_INST_PORT_BASE + scariv_conf_pkg::LSU_INST_NUM;
localparam CSU_DONE_PORT_BASE = BRU_DONE_PORT_BASE + 1;
localparam FPU_DONE_PORT_BASE = CSU_DONE_PORT_BASE + 1;

localparam ALU_INT_REGWR_PORT_BASE = 0;
localparam LSU_INT_REGWR_PORT_BASE = scariv_conf_pkg::ALU_INST_NUM;
localparam BRU_INT_REGWR_PORT_BASE = LSU_INT_REGWR_PORT_BASE + scariv_conf_pkg::LSU_INST_NUM;
localparam CSU_INT_REGWR_PORT_BASE = BRU_INT_REGWR_PORT_BASE + 1;
localparam FPU_INT_REGWR_PORT_BASE = CSU_INT_REGWR_PORT_BASE + 1;

localparam LSU_FP_REGWR_PORT_BASE = 0;
localparam FPU_FP_REGWR_PORT_BASE = LSU_FP_REGWR_PORT_BASE + scariv_conf_pkg::LSU_INST_NUM;

// ----------------------------------
// Global Components
// ----------------------------------
l2_req_if  l2_req ();
l2_resp_if l2_resp ();

scariv_front_if w_ibuf_front_if();
scariv_front_if w_rn_front_if ();

early_wr_if    w_early_wr_if[scariv_pkg::REL_BUS_SIZE]();
phy_wr_if      w_phy_wr_if  [scariv_pkg::TGT_BUS_SIZE]();
lsu_mispred_if w_mispred_if [scariv_conf_pkg::LSU_INST_NUM]();

scariv_pkg::cmt_id_t   w_sc_new_cmt_id;

regread_if  #(.REG_TYPE(scariv_pkg::GPR)) int_regread[scariv_pkg::INT_REGRD_PORT_NUM] ();
regread_if  #(.REG_TYPE(scariv_pkg::FPR)) fp_regread [scariv_pkg::FP_REGRD_PORT_NUM ] ();
regwrite_if #(.REG_TYPE(scariv_pkg::GPR)) int_regwrite[scariv_pkg::INT_REGWR_PORT_NUM] ();
regwrite_if #(.REG_TYPE(scariv_pkg::FPR)) fp_regwrite [scariv_pkg::FP_REGWR_PORT_NUM ] ();

done_report_if w_done_report_if[scariv_pkg::CMT_BUS_SIZE]();

csr_info_if w_csr_info ();
interrupt_if w_int_if();
rob_info_if w_rob_info_if();
tlb_ptw_if  w_ptw_if[1 + scariv_conf_pkg::LSU_INST_NUM]();
lsu_access_if w_lsu_access();
sfence_if     w_sfence_if();
logic                          w_fence_i;

brtag_if w_brtag_if();

// ----------------------------------
// Committer Components
// ----------------------------------
/* verilator lint_off UNOPTFLAT */
commit_if     w_commit_if();
scariv_pkg::cmt_rnid_upd_t   w_commit_rnid_update;

// ----------------------------------
// ALU Components
// ----------------------------------
scariv_pkg::grp_id_t   w_disp_alu_valids [scariv_conf_pkg::ALU_INST_NUM];


// ----------------------------------
// LSU Components
// ----------------------------------
scariv_pkg::grp_id_t        w_disp_lsu_valids[scariv_conf_pkg::LSU_INST_NUM];
flush_report_if             w_flush_report_if [scariv_conf_pkg::LSU_INST_NUM]();
// ----------------------------------
// BRU Components
// ----------------------------------
scariv_pkg::grp_id_t   w_disp_bru_valids;
br_upd_if w_ex3_br_upd_if();

// ----------------------------------
// CSU Components
// ----------------------------------
scariv_pkg::grp_id_t   w_disp_csu_valids;

// ----------------------------------
// FPU Components
// ----------------------------------
scariv_pkg::grp_id_t   w_disp_fpu_valids [scariv_conf_pkg::FPU_INST_NUM];

fflags_update_if w_fflags_update_if();

// -------------------------------
// Internal Broadcast Interface
// -------------------------------
snoop_info_if  w_snoop_info_if();

l1d_snoop_if   l1d_snoop_if  ();
stq_snoop_if   stq_snoop_if  ();
mshr_snoop_if  mshr_snoop_if ();
stbuf_snoop_if stbuf_snoop_if();
streq_snoop_if streq_snoop_if();

// ----------------------------------
// Credit/Return Management
// ----------------------------------
logic                                w_resource_ok;
cre_ret_if #(.MAX_INC(scariv_conf_pkg::CMT_ENTRY_SIZE   )) rob_cre_ret_if();
cre_ret_if #(.MAX_INC(scariv_conf_pkg::RV_ALU_ENTRY_SIZE)) alu_cre_ret_if[scariv_conf_pkg::ALU_INST_NUM]();
cre_ret_if #(.MAX_INC(scariv_conf_pkg::RV_LSU_ENTRY_SIZE)) lsu_cre_ret_if[scariv_conf_pkg::LSU_INST_NUM]();
cre_ret_if #(.MAX_INC(scariv_conf_pkg::LDQ_SIZE         )) ldq_cre_ret_if();
cre_ret_if #(.MAX_INC(scariv_conf_pkg::STQ_SIZE         )) stq_cre_ret_if();
cre_ret_if #(.MAX_INC(scariv_conf_pkg::RV_BRU_ENTRY_SIZE)) bru_cre_ret_if();
cre_ret_if #(.MAX_INC(scariv_conf_pkg::RV_CSU_ENTRY_SIZE)) csu_cre_ret_if();
cre_ret_if #(.MAX_INC(scariv_conf_pkg::RV_FPU_ENTRY_SIZE)) fpu_cre_ret_if[scariv_conf_pkg::FPU_INST_NUM]();


// ----------------------------------
// Branch Tag
// ----------------------------------

scariv_pkg::brtag_t  w_iq_brtag  [scariv_conf_pkg::DISP_SIZE];

// ----------------------------------
// Merging Forwarding / Done signals
// ----------------------------------
// ALU

generate for (genvar a_idx = 0; a_idx < scariv_conf_pkg::ALU_INST_NUM; a_idx++) begin : alu_reg_wr_loop
  assign int_regwrite[a_idx].valid = w_phy_wr_if[ALU_INST_PORT_BASE + a_idx].valid;
  assign int_regwrite[a_idx].rnid  = w_phy_wr_if[ALU_INST_PORT_BASE + a_idx].rd_rnid ;
  assign int_regwrite[a_idx].data  = w_phy_wr_if[ALU_INST_PORT_BASE + a_idx].rd_data ;
end endgenerate


// LSU
generate for (genvar l_idx = 0; l_idx < scariv_conf_pkg::LSU_INST_NUM; l_idx++) begin : lsu_reg_wr_loop
  assign int_regwrite[LSU_INT_REGWR_PORT_BASE + l_idx].valid = w_phy_wr_if[LSU_INST_PORT_BASE + l_idx].valid & (w_phy_wr_if[LSU_INST_PORT_BASE + l_idx].rd_type == scariv_pkg::GPR);
  assign int_regwrite[LSU_INT_REGWR_PORT_BASE + l_idx].rnid  = w_phy_wr_if[LSU_INST_PORT_BASE + l_idx].rd_rnid;
  assign int_regwrite[LSU_INT_REGWR_PORT_BASE + l_idx].data  = w_phy_wr_if[LSU_INST_PORT_BASE + l_idx].rd_data;

  assign fp_regwrite[LSU_FP_REGWR_PORT_BASE + l_idx].valid = w_phy_wr_if[LSU_INST_PORT_BASE + l_idx].valid & (w_phy_wr_if[LSU_INST_PORT_BASE + l_idx].rd_type == scariv_pkg::FPR);
  assign fp_regwrite[LSU_FP_REGWR_PORT_BASE + l_idx].rnid  = w_phy_wr_if[LSU_INST_PORT_BASE + l_idx].rd_rnid;
  assign fp_regwrite[LSU_FP_REGWR_PORT_BASE + l_idx].data  = w_phy_wr_if[LSU_INST_PORT_BASE + l_idx].rd_data;
end
endgenerate


// BRU
assign int_regwrite[BRU_INT_REGWR_PORT_BASE].valid = w_phy_wr_if[BRU_INST_PORT_BASE].valid;
assign int_regwrite[BRU_INT_REGWR_PORT_BASE].rnid  = w_phy_wr_if[BRU_INST_PORT_BASE].rd_rnid;
assign int_regwrite[BRU_INT_REGWR_PORT_BASE].data  = w_phy_wr_if[BRU_INST_PORT_BASE].rd_data;

// CSU
assign int_regwrite[CSU_INT_REGWR_PORT_BASE].valid = w_phy_wr_if[CSU_INST_PORT_BASE].valid;
assign int_regwrite[CSU_INT_REGWR_PORT_BASE].rnid  = w_phy_wr_if[CSU_INST_PORT_BASE].rd_rnid;
assign int_regwrite[CSU_INT_REGWR_PORT_BASE].data  = w_phy_wr_if[CSU_INST_PORT_BASE].rd_data;


// FPU
generate for (genvar f_idx = 0; f_idx < scariv_conf_pkg::FPU_INST_NUM; f_idx++) begin : fpu_reg_wr_loop
  assign int_regwrite [FPU_INT_REGWR_PORT_BASE + f_idx*2+0].valid = w_phy_wr_if[FPU_INST_PORT_BASE + f_idx*2+0].valid & (w_phy_wr_if[FPU_INST_PORT_BASE + f_idx*2+0].rd_type == scariv_pkg::GPR);
  assign int_regwrite [FPU_INT_REGWR_PORT_BASE + f_idx*2+0].rnid  = w_phy_wr_if[FPU_INST_PORT_BASE + f_idx*2+0].rd_rnid ;
  assign int_regwrite [FPU_INT_REGWR_PORT_BASE + f_idx*2+0].data  = w_phy_wr_if[FPU_INST_PORT_BASE + f_idx*2+0].rd_data ;
  assign int_regwrite [FPU_INT_REGWR_PORT_BASE + f_idx*2+1].valid = w_phy_wr_if[FPU_INST_PORT_BASE + f_idx*2+1].valid & (w_phy_wr_if[FPU_INST_PORT_BASE + f_idx*2+1].rd_type == scariv_pkg::GPR);
  assign int_regwrite [FPU_INT_REGWR_PORT_BASE + f_idx*2+1].rnid  = w_phy_wr_if[FPU_INST_PORT_BASE + f_idx*2+1].rd_rnid ;
  assign int_regwrite [FPU_INT_REGWR_PORT_BASE + f_idx*2+1].data  = w_phy_wr_if[FPU_INST_PORT_BASE + f_idx*2+1].rd_data ;

  assign fp_regwrite  [FPU_FP_REGWR_PORT_BASE + f_idx*2+0].valid = w_phy_wr_if[FPU_INST_PORT_BASE+f_idx*2+0].valid & (w_phy_wr_if[FPU_INST_PORT_BASE+f_idx*2+0].rd_type == scariv_pkg::FPR);
  assign fp_regwrite  [FPU_FP_REGWR_PORT_BASE + f_idx*2+0].rnid  = w_phy_wr_if[FPU_INST_PORT_BASE+f_idx*2+0].rd_rnid ;
  assign fp_regwrite  [FPU_FP_REGWR_PORT_BASE + f_idx*2+0].data  = w_phy_wr_if[FPU_INST_PORT_BASE+f_idx*2+0].rd_data ;
  assign fp_regwrite  [FPU_FP_REGWR_PORT_BASE + f_idx*2+1].valid = w_phy_wr_if[FPU_INST_PORT_BASE+f_idx*2+1].valid & (w_phy_wr_if[FPU_INST_PORT_BASE+f_idx*2+1].rd_type == scariv_pkg::FPR);
  assign fp_regwrite  [FPU_FP_REGWR_PORT_BASE + f_idx*2+1].rnid  = w_phy_wr_if[FPU_INST_PORT_BASE+f_idx*2+1].rd_rnid ;
  assign fp_regwrite  [FPU_FP_REGWR_PORT_BASE + f_idx*2+1].data  = w_phy_wr_if[FPU_INST_PORT_BASE+f_idx*2+1].rd_data ;
end endgenerate // block: fpu_reg_wr_loop


scariv_frontend u_frontend (
  .i_clk(i_clk),
  .i_reset_n(i_reset_n),

  .sfence_if (w_sfence_if),
  .i_fence_i (w_fence_i),

  .ic_l2_req(ic_l2_req),
  .ic_l2_resp(ic_l2_resp),

  .commit_in_if (w_commit_if),
  .br_upd_if (w_ex3_br_upd_if),

  .csr_info (w_csr_info),
  .int_if   (w_int_if),

  .ibuf_front_if(w_ibuf_front_if),

  .ptw_if (w_ptw_if[0])
);


scariv_rename
  #(.REG_TYPE(scariv_pkg::GPR))
u_rename (
  .i_clk(i_clk),
  .i_reset_n(i_reset_n),

  .ibuf_front_if (w_ibuf_front_if),
  .i_sc_new_cmt_id (w_sc_new_cmt_id),

  .commit_if             (w_commit_if),
  .commit_if_rnid_update (w_commit_rnid_update),

  .i_resource_ok (w_resource_ok),

  .i_brtag  (w_iq_brtag),

  .br_upd_if (w_ex3_br_upd_if),

  .phy_wr_if (w_phy_wr_if),
  .rn_front_if  (w_rn_front_if)
);


scariv_resource_alloc u_resource_alloc
(
  .i_clk(i_clk),
  .i_reset_n(i_reset_n),

  .ibuf_front_if (w_ibuf_front_if),

  .rob_cre_ret_if (rob_cre_ret_if),
  .alu_cre_ret_if (alu_cre_ret_if),
  .lsu_cre_ret_if (lsu_cre_ret_if),
  .ldq_cre_ret_if (ldq_cre_ret_if),
  .stq_cre_ret_if (stq_cre_ret_if),
  .csu_cre_ret_if (csu_cre_ret_if),
  .bru_cre_ret_if (bru_cre_ret_if),
  .fpu_cre_ret_if (fpu_cre_ret_if),

  .br_upd_if (w_ex3_br_upd_if),

  .commit_if (w_commit_if),

  .o_brtag  (w_iq_brtag),

  .o_resource_ok (w_resource_ok),

  .brtag_if (w_brtag_if)
 );

localparam ALU_PORT_SIZE = scariv_conf_pkg::ARITH_DISP_SIZE / scariv_conf_pkg::ALU_INST_NUM;
localparam FPU_PORT_SIZE = scariv_conf_pkg::FPU_DISP_SIZE / scariv_conf_pkg::FPU_INST_NUM;

generate for (genvar d_idx = 0; d_idx < scariv_conf_pkg::DISP_SIZE; d_idx++) begin : disp_valid_loop
  for (genvar a_idx = 0; a_idx < scariv_conf_pkg::ALU_INST_NUM; a_idx++) begin: alu_disp_valid_loop
    assign w_disp_alu_valids[a_idx][d_idx] = w_rn_front_if.valid & w_rn_front_if.payload.inst[d_idx].valid & !w_rn_front_if.payload.inst[d_idx].illegal_valid &
                                             w_rn_front_if.payload.resource_cnt.alu_inst_valid[a_idx][d_idx];
  end

  for (genvar l_idx = 0; l_idx < scariv_conf_pkg::LSU_INST_NUM; l_idx++) begin: lsu_disp_valid_loop
    assign w_disp_lsu_valids[l_idx][d_idx] = w_rn_front_if.valid && w_rn_front_if.payload.inst[d_idx].valid && !w_rn_front_if.payload.inst[d_idx].illegal_valid &&
                                             w_rn_front_if.payload.resource_cnt.lsu_inst_valid[l_idx][d_idx];
  end

  assign w_disp_bru_valids[d_idx] = w_rn_front_if.valid && w_rn_front_if.payload.inst[d_idx].valid && !w_rn_front_if.payload.inst[d_idx].illegal_valid &&
                                    (w_rn_front_if.payload.inst[d_idx].cat == decoder_inst_cat_pkg::INST_CAT_BR);
  assign w_disp_csu_valids[d_idx] = w_rn_front_if.valid && w_rn_front_if.payload.inst[d_idx].valid && !w_rn_front_if.payload.inst[d_idx].illegal_valid &&
                                    (w_rn_front_if.payload.inst[d_idx].cat == decoder_inst_cat_pkg::INST_CAT_CSU);
  for (genvar f_idx = 0; f_idx < scariv_conf_pkg::FPU_INST_NUM; f_idx++) begin: fpu_disp_valid_loop
    assign w_disp_fpu_valids[f_idx][d_idx] = w_rn_front_if.valid & w_rn_front_if.payload.inst[d_idx].valid & !w_rn_front_if.payload.inst[d_idx].illegal_valid &&
                                             w_rn_front_if.payload.resource_cnt.fpu_inst_valid[f_idx][d_idx];
  end
end
endgenerate


generate for (genvar alu_idx = 0; alu_idx < scariv_conf_pkg::ALU_INST_NUM; alu_idx++) begin : alu_loop
  scariv_alu #(
      .PORT_BASE(alu_idx)
  ) u_alu (
      .i_clk(i_clk),
      .i_reset_n(i_reset_n),

      .rob_info_if   (w_rob_info_if),

      .disp_valid(w_disp_alu_valids[alu_idx]),
      .disp(w_rn_front_if),
      .cre_ret_if (alu_cre_ret_if[alu_idx]),

      .ex1_regread_rs1(int_regread[alu_idx * 2 + 0]),
      .ex1_regread_rs2(int_regread[alu_idx * 2 + 1]),

      .early_wr_in_if (w_early_wr_if),
      .phy_wr_in_if   (w_phy_wr_if  ),
      .mispred_in_if  (w_mispred_if ),

      .early_wr_out_if(w_early_wr_if[alu_idx]),
      .phy_wr_out_if  (w_phy_wr_if  [alu_idx]),

      .commit_if  (w_commit_if),
      .br_upd_if (w_ex3_br_upd_if),

      .done_report_if (w_done_report_if[alu_idx])
  );
end
endgenerate


scariv_lsu_top
u_lsu_top
  (
    .i_clk    (i_clk    ),
    .i_reset_n(i_reset_n),

    .rob_info_if   (w_rob_info_if),

    .csr_info (w_csr_info),

    .disp_valid (w_disp_lsu_valids),
    .disp (w_rn_front_if),

    .iss_cre_ret_if (lsu_cre_ret_if),
    .ldq_cre_ret_if (ldq_cre_ret_if),
    .stq_cre_ret_if (stq_cre_ret_if),

    .int_rs1_regread (int_regread[scariv_conf_pkg::ALU_INST_NUM * 2 +: scariv_conf_pkg::LSU_INST_NUM]),

    .int_rs2_regread (int_regread[(scariv_conf_pkg::ALU_INST_NUM * 2) + scariv_conf_pkg::LSU_INST_NUM +: scariv_conf_pkg::STQ_REGRD_PORT_NUM]),
    .fp_rs2_regread  (fp_regread [(scariv_conf_pkg::FPU_INST_NUM * 3) +: scariv_conf_pkg::STQ_REGRD_PORT_NUM]),

    .ptw_if       (w_ptw_if[1 +: scariv_conf_pkg::LSU_INST_NUM]),
    .lsu_access   (w_lsu_access),

    .l1d_ext_req  (l1d_ext_req ),
    .l1d_ext_resp (l1d_ext_resp),

    .early_wr_in_if(w_early_wr_if),
    .phy_wr_in_if  (w_phy_wr_if  ),

    .early_wr_out_if(w_early_wr_if[LSU_INST_PORT_BASE +: scariv_conf_pkg::LSU_INST_NUM]),
    .phy_wr_out_if  (w_phy_wr_if  [LSU_INST_PORT_BASE +: scariv_conf_pkg::LSU_INST_NUM]),
    .mispred_out_if (w_mispred_if),

    .done_report_if(w_done_report_if [LSU_DONE_PORT_BASE +: scariv_conf_pkg::LSU_INST_NUM]),
    .flush_report_if(w_flush_report_if),

    .snoop_info_if (w_snoop_info_if),

    .l1d_snoop_if   (l1d_snoop_if  ),
    .stq_snoop_if   (stq_snoop_if  ),
    .mshr_snoop_if  (mshr_snoop_if ),
    .stbuf_snoop_if (stbuf_snoop_if),
    .streq_snoop_if (streq_snoop_if),

    .sfence_if (w_sfence_if),
    .o_fence_i (w_fence_i),

    .commit_if  (w_commit_if),
    .br_upd_if (w_ex3_br_upd_if)
   );


scariv_bru
u_bru (
    .i_clk(i_clk),
    .i_reset_n(i_reset_n),

    .rob_info_if   (w_rob_info_if),

    .disp_valid(w_disp_bru_valids),
    .disp(w_rn_front_if),
    .cre_ret_if (bru_cre_ret_if),

    .ex1_regread_rs1(int_regread[scariv_conf_pkg::ALU_INST_NUM * 2 +
                                 scariv_conf_pkg::LSU_INST_NUM + scariv_conf_pkg::STQ_REGRD_PORT_NUM +
                                 0]),
    .ex1_regread_rs2(int_regread[scariv_conf_pkg::ALU_INST_NUM * 2 +
                                 scariv_conf_pkg::LSU_INST_NUM + scariv_conf_pkg::STQ_REGRD_PORT_NUM +
                                 1]),

    .early_wr_in_if(w_early_wr_if),
    .phy_wr_in_if  (w_phy_wr_if),
    .mispred_in_if (w_mispred_if),

    .early_wr_out_if(w_early_wr_if[BRU_INST_PORT_BASE]),
    .phy_wr_out_if  (w_phy_wr_if  [BRU_INST_PORT_BASE]),

    .done_report_if (w_done_report_if[BRU_DONE_PORT_BASE]),
    .commit_if      (w_commit_if),
    .ex3_br_upd_if (w_ex3_br_upd_if),
    .ex3_br_upd_slave_if (w_ex3_br_upd_if),

    .brtag_if (w_brtag_if)
);


scariv_csu
u_csu (
    .i_clk(i_clk),
    .i_reset_n(i_reset_n),

    .disp_valid(w_disp_csu_valids),
    .disp(w_rn_front_if),
    .cre_ret_if (csu_cre_ret_if),

    .ex1_regread_rs1(int_regread[scariv_conf_pkg::ALU_INST_NUM * 2 +
                                 scariv_conf_pkg::LSU_INST_NUM + scariv_conf_pkg::STQ_REGRD_PORT_NUM +
                                 2]),

    .early_wr_in_if(w_early_wr_if),
    .phy_wr_in_if  (w_phy_wr_if  ),
    .mispred_in_if (w_mispred_if ),

    .early_wr_out_if(w_early_wr_if[CSU_INST_PORT_BASE]),
    .phy_wr_out_if  (w_phy_wr_if  [CSU_INST_PORT_BASE]),

    .clint_if (clint_if),
    .plic_if  (plic_if),

    .csr_info    (w_csr_info   ),
    .int_if      (w_int_if),
    .rob_info_if (w_rob_info_if),

    .fflags_update_if (w_fflags_update_if),

    .done_report_if (w_done_report_if[CSU_DONE_PORT_BASE]),

    .commit_if (w_commit_if),
    .br_upd_if (w_ex3_br_upd_if)
);


scariv_phy_registers
  #(
    .REG_TYPE(scariv_pkg::GPR),
    .RD_PORT_SIZE(scariv_pkg::INT_REGRD_PORT_NUM),
    .WR_PORT_SIZE(scariv_pkg::INT_REGWR_PORT_NUM)
    )
u_int_phy_registers (
    .i_clk(i_clk),
    .i_reset_n(i_reset_n),

    .regwrite(int_regwrite),
    .regread(int_regread)
);


generate if (riscv_fpu_pkg::FLEN_W != 0) begin : fpu
  // =========================
  // FPU: Flaoting Point Unit
  // =========================
  for (genvar fpu_idx = 0; fpu_idx < scariv_conf_pkg::FPU_INST_NUM; fpu_idx++) begin : fpu_loop
    scariv_fpu #(
      .PORT_BASE(fpu_idx)
    ) u_fpu (
      .i_clk(i_clk),
      .i_reset_n(i_reset_n),

      .csr_info (w_csr_info),
      .rob_info_if   (w_rob_info_if),

      .disp_valid(w_disp_fpu_valids[fpu_idx]),
      .disp(w_rn_front_if),
      .cre_ret_if (fpu_cre_ret_if[fpu_idx]),

      .ex0_regread_int_rs1(int_regread[scariv_conf_pkg::ALU_INST_NUM * 2 +
                                       scariv_conf_pkg::LSU_INST_NUM + scariv_conf_pkg::STQ_REGRD_PORT_NUM +
                                       2 +   // BRU
                                       1 +   // CSU
                                       fpu_idx]),

      .ex0_regread_rs1(fp_regread[fpu_idx * 3 + 0]),
      .ex0_regread_rs2(fp_regread[fpu_idx * 3 + 1]),
      .ex0_regread_rs3(fp_regread[fpu_idx * 3 + 2]),

      .early_wr_if(w_early_wr_if),
      .phy_wr_if  (w_phy_wr_if  ),
      .mispred_if (w_mispred_if ),

      .mv_early_wr_if  (w_early_wr_if[FPU_INST_PORT_BASE + fpu_idx*2+0]),
      .mv_phy_wr_if    (w_phy_wr_if  [FPU_INST_PORT_BASE + fpu_idx*2+0]),
      .fpnew_phy_wr_if (w_phy_wr_if  [FPU_INST_PORT_BASE + fpu_idx*2+1]),

      .commit_if  (w_commit_if),
      .br_upd_if (w_ex3_br_upd_if),

      .mv_done_report_if (w_done_report_if[FPU_INST_PORT_BASE + fpu_idx*2+0]),
      .fp_done_report_if (w_done_report_if[FPU_INST_PORT_BASE + fpu_idx*2+1])
    );

    assign w_early_wr_if[FPU_INST_PORT_BASE + fpu_idx*2+1].valid = 1'b0;
  end // block: fpu_loop

  // --------------------------------------
  // FPU: Floating Point Physical Register
  // --------------------------------------
  scariv_phy_registers
    #(
      .REG_TYPE(scariv_pkg::FPR),
      .RD_PORT_SIZE(scariv_pkg::FP_REGRD_PORT_NUM),
      .WR_PORT_SIZE(scariv_pkg::FP_REGWR_PORT_NUM)
      )
  u_fp_phy_registers
    (
     .i_clk(i_clk),
     .i_reset_n(i_reset_n),

     .regwrite(fp_regwrite),
     .regread(fp_regread)
     );

end // if (riscv_fpu_pkg::FLEN_W != 0)
endgenerate


scariv_rob u_rob
  (
   .i_clk    (i_clk),
   .i_reset_n(i_reset_n),

   .rn_front_if    (w_rn_front_if     ),
   .cre_ret_if (rob_cre_ret_if),

   .int_if     (w_int_if),

   .o_sc_new_cmt_id (w_sc_new_cmt_id),

   .done_report_if  (w_done_report_if ),
   .flush_report_if (w_flush_report_if),

   .commit_if (w_commit_if),
   .fflags_update_if (w_fflags_update_if),
   .o_commit_rnid_update (w_commit_rnid_update),

   .rob_info_if   (w_rob_info_if),

   .br_upd_slave_if (w_ex3_br_upd_if)
   );


scariv_ptw u_ptw
  (
   .i_clk    (i_clk),
   .i_reset_n(i_reset_n),

   .ptw_if   (w_ptw_if),

   .lsu_access (w_lsu_access),

   .ptw_req  (ptw_req ),
   .ptw_resp (ptw_resp)
   );


// Snoop Unit
scariv_snoop_top u_snoop_top
(
 .i_clk     (i_clk    ),
 .i_reset_n (i_reset_n),

 .snoop_if       (snoop_if),

 .snoop_info_if (w_snoop_info_if),

 .l1d_snoop_if   (l1d_snoop_if  ),
 .stq_snoop_if   (stq_snoop_if  ),
 .mshr_snoop_if  (mshr_snoop_if ),
 .stbuf_snoop_if (stbuf_snoop_if),
 .streq_snoop_if (streq_snoop_if)
 );


endmodule  // scariv_tile
