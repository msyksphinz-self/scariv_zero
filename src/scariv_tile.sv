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
localparam VALU_DONE_PORT_BASE = FPU_DONE_PORT_BASE + scariv_conf_pkg::FPU_INST_NUM * 2;
localparam VLSU_DONE_PORT_BASE = VALU_DONE_PORT_BASE + 2;

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

scariv_pkg::early_wr_t w_ex1_early_wr[scariv_pkg::REL_BUS_SIZE];
scariv_pkg::phy_wr_t   w_ex3_phy_wr  [scariv_pkg::TGT_BUS_SIZE];
scariv_pkg::cmt_id_t   w_sc_new_cmt_id;

regread_if  #(.REG_TYPE(scariv_pkg::GPR)) int_regread[scariv_pkg::INT_REGRD_PORT_NUM] ();
regread_if  #(.REG_TYPE(scariv_pkg::FPR)) fp_regread [scariv_pkg::FP_REGRD_PORT_NUM ] ();
regwrite_if #(.REG_TYPE(scariv_pkg::GPR)) int_regwrite[scariv_pkg::INT_REGWR_PORT_NUM] ();
regwrite_if #(.REG_TYPE(scariv_pkg::FPR)) fp_regwrite [scariv_pkg::FP_REGWR_PORT_NUM ] ();

scariv_pkg::done_rpt_t w_done_rpt[scariv_pkg::CMT_BUS_SIZE];

csr_info_if w_csr_info ();
interrupt_if w_int_if();
rob_info_if w_rob_info_if();
tlb_ptw_if  w_ptw_if[1 +   // Frontend
                     scariv_conf_pkg::LSU_INST_NUM  // LSU
                     + 1]();  // Vector LSU
lsu_access_if w_lsu_access();
sfence_if     w_sfence_if();
logic                          w_fence_i;

logic [$clog2(scariv_conf_pkg::RAS_ENTRY_SIZE)-1: 0] w_sc_ras_index;
scariv_pkg::vaddr_t                    w_sc_ras_vaddr;

brtag_if w_brtag_if();

// ----------------------------------
// Committer Components
// ----------------------------------
/* verilator lint_off UNOPTFLAT */
scariv_pkg::commit_blk_t     w_commit;
scariv_pkg::cmt_rnid_upd_t   w_commit_rnid_update;

// ----------------------------------
// ALU Components
// ----------------------------------
scariv_pkg::grp_id_t   w_disp_alu_valids [scariv_conf_pkg::ALU_INST_NUM];
scariv_pkg::early_wr_t w_ex1_alu_early_wr[scariv_conf_pkg::ALU_INST_NUM];
scariv_pkg::phy_wr_t   w_ex3_alu_phy_wr  [scariv_conf_pkg::ALU_INST_NUM];
scariv_pkg::done_rpt_t w_alu_done_rpt    [scariv_conf_pkg::ALU_INST_NUM];


// ----------------------------------
// LSU Components
// ----------------------------------
scariv_pkg::grp_id_t        w_disp_lsu_valids;
scariv_pkg::early_wr_t      w_ex1_lsu_early_wr      [scariv_conf_pkg::LSU_INST_NUM];
scariv_pkg::phy_wr_t        w_ex3_lsu_phy_wr        [scariv_conf_pkg::LSU_INST_NUM];
scariv_pkg::done_rpt_t      w_lsu_done_rpt          [scariv_conf_pkg::LSU_INST_NUM];
scariv_pkg::mispred_t       w_ex2_mispred_lsu       [scariv_conf_pkg::LSU_INST_NUM];
scariv_pkg::another_flush_t w_lsu_another_flush_rpt [scariv_conf_pkg::LSU_INST_NUM];
// ----------------------------------
// BRU Components
// ----------------------------------
scariv_pkg::grp_id_t   w_disp_bru_valids;
scariv_pkg::early_wr_t w_ex1_bru_early_wr;
scariv_pkg::phy_wr_t   w_ex3_bru_phy_wr  ;
scariv_pkg::done_rpt_t w_bru_done_rpt;
br_upd_if w_ex3_br_upd_if();

// ----------------------------------
// CSU Components
// ----------------------------------
scariv_pkg::grp_id_t   w_disp_csu_valids;
scariv_pkg::early_wr_t w_ex1_csu_early_wr;
scariv_pkg::phy_wr_t   w_ex3_csu_phy_wr  ;
scariv_pkg::done_rpt_t w_csu_done_rpt;

// ----------------------------------
// FPU Components
// ----------------------------------
scariv_pkg::grp_id_t   w_disp_fpu_valids [scariv_conf_pkg::FPU_INST_NUM];
scariv_pkg::early_wr_t w_ex1_fpu_early_wr[scariv_conf_pkg::FPU_INST_NUM];
scariv_pkg::phy_wr_t   w_ex3_fpumv_phy_wr[scariv_conf_pkg::FPU_INST_NUM];
scariv_pkg::phy_wr_t   w_fpnew_phy_wr    [scariv_conf_pkg::FPU_INST_NUM];
scariv_pkg::done_rpt_t w_fpu_mv_done_rpt [scariv_conf_pkg::FPU_INST_NUM];
scariv_pkg::done_rpt_t w_fpu_fp_done_rpt [scariv_conf_pkg::FPU_INST_NUM];

fflags_update_if w_fflags_update_if();

// ----------------------------------
// VEC Components
// ----------------------------------
scariv_pkg::grp_id_t   w_disp_valu_valids ;
scariv_pkg::early_wr_t w_ex1_valu_early_wr;
vec_regread_if         w_vec_phy_rd_if[7]()  ;
vec_regwrite_if        w_vec_phy_wr_if[3]()  ;
scariv_pkg::done_rpt_t w_valu_done_rpt[2]    ;

scariv_pkg::grp_id_t   w_disp_vlsu_valids ;
scariv_pkg::early_wr_t w_ex1_vlsu_early_wr;
scariv_pkg::phy_wr_t   w_ex3_vlsu_phy_wr  ;
scariv_pkg::done_rpt_t w_vlsu_done_rpt    ;

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
cre_ret_if #(.MAX_INC(scariv_conf_pkg::RV_VALU_ENTRY_SIZE)) valu_cre_ret_if();
cre_ret_if #(.MAX_INC(scariv_conf_pkg::RV_VLSU_ENTRY_SIZE)) vlsu_cre_ret_if();


// ----------------------------------
// Branch Tag
// ----------------------------------

scariv_pkg::brtag_t  w_iq_brtag  [scariv_conf_pkg::DISP_SIZE];

// ----------------------------------
// L1D VLSU to Scalar Interface
// ----------------------------------
l1d_rd_if            vlsu_l1d_rd_if   ();
l1d_missu_if         vlsu_l1d_missu_if();

// ----------------------------------
// Merging Forwarding / Done signals
// ----------------------------------
// ALU
generate for (genvar a_idx = 0; a_idx < scariv_conf_pkg::ALU_INST_NUM; a_idx++) begin : alu_reg_loop
  assign w_ex1_early_wr[a_idx] = w_ex1_alu_early_wr[a_idx];
  assign w_ex3_phy_wr  [a_idx] = w_ex3_alu_phy_wr  [a_idx];
  assign w_done_rpt    [a_idx] = w_alu_done_rpt    [a_idx];
end
endgenerate

generate for (genvar a_idx = 0; a_idx < scariv_conf_pkg::ALU_INST_NUM; a_idx++) begin : alu_reg_wr_loop
  assign int_regwrite[a_idx].valid = w_ex3_alu_phy_wr[a_idx].valid;
  assign int_regwrite[a_idx].rnid  = w_ex3_alu_phy_wr[a_idx].rd_rnid ;
  assign int_regwrite[a_idx].data  = w_ex3_alu_phy_wr[a_idx].rd_data ;
end endgenerate


// LSU
generate for (genvar l_idx = 0; l_idx < scariv_conf_pkg::LSU_INST_NUM; l_idx++) begin : lsu_reg_loop
  assign w_ex1_early_wr[LSU_INST_PORT_BASE + l_idx] = w_ex1_lsu_early_wr[l_idx];
  assign w_ex3_phy_wr  [LSU_INST_PORT_BASE + l_idx] = w_ex3_lsu_phy_wr  [l_idx];
  assign w_done_rpt    [LSU_DONE_PORT_BASE + l_idx] = w_lsu_done_rpt    [l_idx];
end
endgenerate

generate for (genvar l_idx = 0; l_idx < scariv_conf_pkg::LSU_INST_NUM; l_idx++) begin : lsu_reg_wr_loop
  assign int_regwrite[LSU_INT_REGWR_PORT_BASE + l_idx].valid = w_ex3_lsu_phy_wr[l_idx].valid & (w_ex3_lsu_phy_wr[l_idx].rd_type == scariv_pkg::GPR);
  assign int_regwrite[LSU_INT_REGWR_PORT_BASE + l_idx].rnid  = w_ex3_lsu_phy_wr[l_idx].rd_rnid;
  assign int_regwrite[LSU_INT_REGWR_PORT_BASE + l_idx].data  = w_ex3_lsu_phy_wr[l_idx].rd_data;

  assign fp_regwrite[LSU_FP_REGWR_PORT_BASE + l_idx].valid = w_ex3_lsu_phy_wr[l_idx].valid & (w_ex3_lsu_phy_wr[l_idx].rd_type == scariv_pkg::FPR);
  assign fp_regwrite[LSU_FP_REGWR_PORT_BASE + l_idx].rnid  = w_ex3_lsu_phy_wr[l_idx].rd_rnid;
  assign fp_regwrite[LSU_FP_REGWR_PORT_BASE + l_idx].data  = w_ex3_lsu_phy_wr[l_idx].rd_data;
end
endgenerate


// BRU
assign w_ex1_early_wr[BRU_INST_PORT_BASE] = w_ex1_bru_early_wr;
assign w_ex3_phy_wr  [BRU_INST_PORT_BASE] = w_ex3_bru_phy_wr  ;
assign w_done_rpt    [BRU_DONE_PORT_BASE] = w_bru_done_rpt;

assign int_regwrite[BRU_INT_REGWR_PORT_BASE].valid = w_ex3_bru_phy_wr.valid;
assign int_regwrite[BRU_INT_REGWR_PORT_BASE].rnid  = w_ex3_bru_phy_wr.rd_rnid;
assign int_regwrite[BRU_INT_REGWR_PORT_BASE].data  = w_ex3_bru_phy_wr.rd_data;

// CSU
// assign w_ex1_early_wr[CSU_INST_PORT_BASE] = w_ex1_csu_early_wr;
assign w_ex1_early_wr[CSU_INST_PORT_BASE] = 'h0;
assign w_ex3_phy_wr  [CSU_INST_PORT_BASE] = w_ex3_csu_phy_wr  ;
assign w_done_rpt    [CSU_DONE_PORT_BASE] = w_csu_done_rpt;

assign int_regwrite[CSU_INT_REGWR_PORT_BASE].valid = w_ex3_csu_phy_wr.valid;
assign int_regwrite[CSU_INT_REGWR_PORT_BASE].rnid  = w_ex3_csu_phy_wr.rd_rnid;
assign int_regwrite[CSU_INT_REGWR_PORT_BASE].data  = w_ex3_csu_phy_wr.rd_data;


// FPU
generate for (genvar f_idx = 0; f_idx < scariv_conf_pkg::FPU_INST_NUM; f_idx++) begin : fpu_reg_loop
  assign w_ex1_early_wr[FPU_INST_PORT_BASE + f_idx*2+0] = w_ex1_fpu_early_wr[f_idx];
  assign w_ex1_early_wr[FPU_INST_PORT_BASE + f_idx*2+1] = 'h0;   // Now, FPNew early wakeup is not used.
  assign w_ex3_phy_wr  [FPU_INST_PORT_BASE + f_idx*2+0] = w_ex3_fpumv_phy_wr[f_idx];
  assign w_ex3_phy_wr  [FPU_INST_PORT_BASE + f_idx*2+1] = w_fpnew_phy_wr    [f_idx];
  assign w_done_rpt    [FPU_DONE_PORT_BASE + f_idx*2+0] = w_fpu_mv_done_rpt [f_idx];
  assign w_done_rpt    [FPU_DONE_PORT_BASE + f_idx*2+1] = w_fpu_fp_done_rpt [f_idx];
end
endgenerate

assign w_done_rpt[VALU_DONE_PORT_BASE+0] = w_valu_done_rpt[0];
assign w_done_rpt[VALU_DONE_PORT_BASE+1] = w_valu_done_rpt[1];
assign w_done_rpt[VLSU_DONE_PORT_BASE  ] = w_vlsu_done_rpt;

generate for (genvar f_idx = 0; f_idx < scariv_conf_pkg::FPU_INST_NUM; f_idx++) begin : fpu_reg_wr_loop
  assign int_regwrite [FPU_INT_REGWR_PORT_BASE + f_idx*2+0].valid = w_ex3_fpumv_phy_wr[f_idx].valid & (w_ex3_fpumv_phy_wr[f_idx].rd_type == scariv_pkg::GPR);
  assign int_regwrite [FPU_INT_REGWR_PORT_BASE + f_idx*2+0].rnid  = w_ex3_fpumv_phy_wr[f_idx].rd_rnid ;
  assign int_regwrite [FPU_INT_REGWR_PORT_BASE + f_idx*2+0].data  = w_ex3_fpumv_phy_wr[f_idx].rd_data ;
  assign int_regwrite [FPU_INT_REGWR_PORT_BASE + f_idx*2+1].valid = w_fpnew_phy_wr    [f_idx].valid & (w_fpnew_phy_wr[f_idx].rd_type == scariv_pkg::GPR);
  assign int_regwrite [FPU_INT_REGWR_PORT_BASE + f_idx*2+1].rnid  = w_fpnew_phy_wr    [f_idx].rd_rnid ;
  assign int_regwrite [FPU_INT_REGWR_PORT_BASE + f_idx*2+1].data  = w_fpnew_phy_wr    [f_idx].rd_data ;

  assign fp_regwrite  [FPU_FP_REGWR_PORT_BASE + f_idx*2+0].valid = w_ex3_fpumv_phy_wr[f_idx].valid & (w_ex3_fpumv_phy_wr[f_idx].rd_type == scariv_pkg::FPR);
  assign fp_regwrite  [FPU_FP_REGWR_PORT_BASE + f_idx*2+0].rnid  = w_ex3_fpumv_phy_wr[f_idx].rd_rnid ;
  assign fp_regwrite  [FPU_FP_REGWR_PORT_BASE + f_idx*2+0].data  = w_ex3_fpumv_phy_wr[f_idx].rd_data ;
  assign fp_regwrite  [FPU_FP_REGWR_PORT_BASE + f_idx*2+1].valid = w_fpnew_phy_wr    [f_idx].valid & (w_fpnew_phy_wr[f_idx].rd_type == scariv_pkg::FPR);
  assign fp_regwrite  [FPU_FP_REGWR_PORT_BASE + f_idx*2+1].rnid  = w_fpnew_phy_wr    [f_idx].rd_rnid ;
  assign fp_regwrite  [FPU_FP_REGWR_PORT_BASE + f_idx*2+1].data  = w_fpnew_phy_wr    [f_idx].rd_data ;
end endgenerate

scariv_frontend u_frontend (
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

  .ibuf_front_if(w_ibuf_front_if),
  .rn_front_if (w_rn_front_if),
  .o_sc_ras_index  (w_sc_ras_index),
  .o_sc_ras_vaddr (w_sc_ras_vaddr),

  .ptw_if (w_ptw_if[0])
);


scariv_rename
  #(.REG_TYPE(scariv_pkg::GPR))
u_rename (
  .i_clk(i_clk),
  .i_reset_n(i_reset_n),

  .ibuf_front_if (w_ibuf_front_if),
  .i_sc_new_cmt_id (w_sc_new_cmt_id),

  .i_commit             (w_commit),
  .i_commit_rnid_update (w_commit_rnid_update),

  .i_resource_ok (w_resource_ok),

  .i_brtag  (w_iq_brtag),

  .br_upd_if (w_ex3_br_upd_if),

  .i_phy_wr (w_ex3_phy_wr),
  .valu_vec_phy_wr_if (w_vec_phy_wr_if),

  .rn_front_if  (w_rn_front_if),
  .i_sc_ras_index (w_sc_ras_index),
  .i_sc_ras_vaddr (w_sc_ras_vaddr)
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
  .valu_cre_ret_if(valu_cre_ret_if),
  .vlsu_cre_ret_if(vlsu_cre_ret_if),

  .br_upd_if (w_ex3_br_upd_if),

  .i_commit (w_commit),

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

  assign w_disp_lsu_valids[d_idx] = w_rn_front_if.valid && w_rn_front_if.payload.inst[d_idx].valid && !w_rn_front_if.payload.inst[d_idx].illegal_valid &&
                                    (w_rn_front_if.payload.inst[d_idx].cat == decoder_inst_cat_pkg::INST_CAT_LD ||
                                     w_rn_front_if.payload.inst[d_idx].cat == decoder_inst_cat_pkg::INST_CAT_ST);
  assign w_disp_bru_valids[d_idx] = w_rn_front_if.valid && w_rn_front_if.payload.inst[d_idx].valid && !w_rn_front_if.payload.inst[d_idx].illegal_valid &&
                                    (w_rn_front_if.payload.inst[d_idx].cat == decoder_inst_cat_pkg::INST_CAT_BR);
  assign w_disp_csu_valids[d_idx] = w_rn_front_if.valid && w_rn_front_if.payload.inst[d_idx].valid && !w_rn_front_if.payload.inst[d_idx].illegal_valid &&
                                    (w_rn_front_if.payload.inst[d_idx].cat == decoder_inst_cat_pkg::INST_CAT_CSU);
  for (genvar f_idx = 0; f_idx < scariv_conf_pkg::FPU_INST_NUM; f_idx++) begin: fpu_disp_valid_loop
    assign w_disp_fpu_valids[f_idx][d_idx] = w_rn_front_if.valid & w_rn_front_if.payload.inst[d_idx].valid & !w_rn_front_if.payload.inst[d_idx].illegal_valid &&
                                             w_rn_front_if.payload.resource_cnt.fpu_inst_valid[f_idx][d_idx];
  end

  assign w_disp_valu_valids[d_idx] = w_rn_front_if.valid && w_rn_front_if.payload.inst[d_idx].valid && !w_rn_front_if.payload.inst[d_idx].illegal_valid &&
                                     (w_rn_front_if.payload.inst[d_idx].cat == decoder_inst_cat_pkg::INST_CAT_VALU);
  assign w_disp_vlsu_valids[d_idx] = w_rn_front_if.valid && w_rn_front_if.payload.inst[d_idx].valid && !w_rn_front_if.payload.inst[d_idx].illegal_valid &&
                                     (w_rn_front_if.payload.inst[d_idx].cat == decoder_inst_cat_pkg::INST_CAT_VLSU);

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

      .i_early_wr(w_ex1_early_wr),
      .i_phy_wr  (w_ex3_phy_wr),
      .i_mispred_lsu (w_ex2_mispred_lsu),

      .o_ex1_early_wr(w_ex1_alu_early_wr[alu_idx]),
      .o_ex3_phy_wr  (w_ex3_alu_phy_wr  [alu_idx]),

      .i_commit  (w_commit),
      .br_upd_if (w_ex3_br_upd_if),

      .o_done_report (w_alu_done_rpt[alu_idx])
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

    .ex1_int_regread (int_regread[scariv_conf_pkg::ALU_INST_NUM * 2 +: scariv_conf_pkg::LSU_INST_NUM]),

    .int_rs2_regread (int_regread[(scariv_conf_pkg::ALU_INST_NUM * 2) +  scariv_conf_pkg::LSU_INST_NUM]),
    .fp_rs2_regread  (fp_regread [(scariv_conf_pkg::FPU_INST_NUM * 3)]),

    .ptw_if       (w_ptw_if[1 +: scariv_conf_pkg::LSU_INST_NUM]),
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

    .snoop_info_if (w_snoop_info_if),

    .l1d_snoop_if   (l1d_snoop_if  ),
    .stq_snoop_if   (stq_snoop_if  ),
    .mshr_snoop_if  (mshr_snoop_if ),
    .stbuf_snoop_if (stbuf_snoop_if),
    .streq_snoop_if (streq_snoop_if),

    .sfence_if (w_sfence_if),
    .o_fence_i (w_fence_i),

    .vlsu_l1d_rd_if    (vlsu_l1d_rd_if   ),
    .vlsu_l1d_missu_if (vlsu_l1d_missu_if),

    .i_commit  (w_commit),
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
                                 scariv_conf_pkg::LSU_INST_NUM + 1 +
                                 0]),
    .ex1_regread_rs2(int_regread[scariv_conf_pkg::ALU_INST_NUM * 2 +
                                 scariv_conf_pkg::LSU_INST_NUM + 1 +
                                 1]),

    .i_early_wr(w_ex1_early_wr),
    .i_phy_wr  (w_ex3_phy_wr),
    .i_mispred_lsu (w_ex2_mispred_lsu),

    .o_ex1_early_wr(w_ex1_bru_early_wr),
    .o_ex3_phy_wr  (w_ex3_bru_phy_wr  ),

    .o_done_report (w_bru_done_rpt),
    .i_commit      (w_commit),
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
    .i_vlvtype_ren_idx (r_rn_vlvtype_info_if.vsetvl_index),
    .cre_ret_if (csu_cre_ret_if),

    .ex1_regread_rs1(int_regread[scariv_conf_pkg::ALU_INST_NUM * 2 +
                                 scariv_conf_pkg::LSU_INST_NUM + 1 +
                                 2]),

    .i_early_wr(w_ex1_early_wr),
    .i_phy_wr  (w_ex3_phy_wr),

    .o_ex1_early_wr(w_ex1_csu_early_wr),
    .o_ex3_phy_wr  (w_ex3_csu_phy_wr  ),
    .i_mispred_lsu (w_ex2_mispred_lsu),

    .clint_if (clint_if),
    .plic_if  (plic_if),

    .csr_info    (w_csr_info   ),
    .int_if      (w_int_if),
    .rob_info_if (w_rob_info_if),

    .fflags_update_if (w_fflags_update_if),

    .vlvtype_upd_if (w_vlvtype_upd_if),

    .o_done_report (w_csu_done_rpt),

    .i_commit (w_commit),
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

      .ex1_regread_int_rs1(int_regread[scariv_conf_pkg::ALU_INST_NUM * 2 +
                                       scariv_conf_pkg::LSU_INST_NUM + 1 +
                                       2 +   // BRU
                                       1 +   // CSU
                                       fpu_idx]),

      .ex1_regread_rs1(fp_regread[fpu_idx * 3 + 0]),
      .ex1_regread_rs2(fp_regread[fpu_idx * 3 + 1]),
      .ex1_regread_rs3(fp_regread[fpu_idx * 3 + 2]),

      .i_early_wr(w_ex1_early_wr),
      .i_phy_wr  (w_ex3_phy_wr),
      .i_mispred_lsu (w_ex2_mispred_lsu),

      .o_ex1_mv_early_wr(w_ex1_fpu_early_wr[fpu_idx]),
      .o_ex3_mv_phy_wr  (w_ex3_fpumv_phy_wr[fpu_idx]),
      .o_fpnew_phy_wr   (w_fpnew_phy_wr    [fpu_idx]),

      .i_commit  (w_commit),
      .br_upd_if (w_ex3_br_upd_if),

      .o_mv_done_report (w_fpu_mv_done_rpt[fpu_idx]),
      .o_fp_done_report (w_fpu_fp_done_rpt[fpu_idx])
    );
  end

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

vlvtype_commit_if w_vlvtype_commit();
vlvtype_upd_if    w_vlvtype_upd_if();
vlvtype_info_if   r_rn_vlvtype_info_if();

generate if (scariv_vec_pkg::VLEN_W != 0) begin : vpu
  scariv_vec_pkg::vlvtype_ren_idx_t  w_ibuf_vlvtype_index;
  vlvtype_req_if                     w_vlvtype_req_if();

  scariv_vec_pkg::vlvtype_t r_rn_vlvtype;

  scariv_pkg::grp_id_t w_rn_is_subcat_vset;

  for (genvar d_idx = 0; d_idx < scariv_conf_pkg::DISP_SIZE; d_idx++) begin : csu_vset_loop
    assign w_rn_is_subcat_vset[d_idx] = (w_rn_front_if.payload.inst[d_idx].cat == decoder_inst_cat_pkg::INST_CAT_CSU) &
                                        (w_rn_front_if.payload.inst[d_idx].subcat == decoder_inst_cat_pkg::INST_SUBCAT_VSET);
  end

  assign w_vlvtype_req_if.valid              = |w_rn_is_subcat_vset;
  assign w_vlvtype_req_if.checkpt_push_valid = |w_rn_front_if.payload.is_br_included;

  assign r_rn_vlvtype_info_if.vlvtype      = w_vlvtype_req_if.vlvtype;
  assign r_rn_vlvtype_info_if.index        = w_vlvtype_req_if.index;
  assign r_rn_vlvtype_info_if.vsetvl_index = w_vlvtype_req_if.vsetvl_index;
  assign r_rn_vlvtype_info_if.ready        = w_vlvtype_req_if.ready;

  scariv_vec_vlvtype_rename
  u_vec_vlvtype_rename
    (
     .i_clk     (i_clk    ),
     .i_reset_n (i_reset_n),

     .vlvtype_req_if    (w_vlvtype_req_if   ),
     .vlvtype_commit_if (w_vlvtype_commit),
     .i_brtag           (w_rn_front_if.payload.inst[0].brtag),

     .i_commit  (w_commit),
     .br_upd_if (w_ex3_br_upd_if),

     .vlvtype_upd_if (w_vlvtype_upd_if)
   );


  localparam VALU_READ_PORT_IDX = scariv_conf_pkg::ALU_INST_NUM * 2 +
                                  scariv_conf_pkg::LSU_INST_NUM + 1 +
                                  2 +   // BRU
                                  1 +   // CSU
                                  scariv_conf_pkg::FPU_INST_NUM;
  localparam VALU_VPR_READ_PORT_IDX = 0;

  scariv_vec_alu
    #(.PORT_BASE(0))
  u_vec_alu
    (
     .i_clk    (i_clk),
     .i_reset_n(i_reset_n),

     .csr_info (w_csr_info),
     .rob_info_if(w_rob_info_if),

     .disp_valid(w_disp_valu_valids),
     .disp(w_rn_front_if),
     .vlvtype_info_if (r_rn_vlvtype_info_if),
     .vlvtype_upd_if  (w_vlvtype_upd_if),

     .cre_ret_if(valu_cre_ret_if),

     .ex1_xpr_regread_rs1(int_regread[VALU_READ_PORT_IDX]),

     .ex1_fpr_regread_rs1(fp_regread[scariv_conf_pkg::FPU_INST_NUM * 3 +     // FPU port
                                     1]),                                    // LSU port

     .i_phy_wr(w_ex3_phy_wr),

     .vec_phy_rd_if     (w_vec_phy_rd_if[VALU_VPR_READ_PORT_IDX +: 3]),
     .vec_phy_old_wr_if (w_vec_phy_rd_if[VALU_VPR_READ_PORT_IDX +  3]),
     .vec_phy_wr_if     (w_vec_phy_wr_if[0:1]),

     .o_done_report(w_valu_done_rpt),

     .i_commit (w_commit),
     .br_upd_if(w_ex3_br_upd_if)
     );


  localparam VLSU_XPR_READ_PORT_IDX = VALU_READ_PORT_IDX + 1;
  localparam VLSU_VPR_READ_PORT_IDX = VALU_VPR_READ_PORT_IDX + 4;

  scariv_vec_lsu
    #(.PORT_BASE(0))
  u_vec_lsu
    (
     .i_clk    (i_clk),
     .i_reset_n(i_reset_n),

     .csr_info   (w_csr_info   ),
     .sfence_if  (w_sfence_if  ),
     .rob_info_if(w_rob_info_if),
     .ptw_if     (w_ptw_if[1 + scariv_conf_pkg::LSU_INST_NUM]),

     .disp_valid      (w_disp_vlsu_valids),
     .disp            (w_rn_front_if),
     .vlvtype_info_if (r_rn_vlvtype_info_if),
     .vlvtype_upd_if  (w_vlvtype_upd_if),

     .cre_ret_if(vlsu_cre_ret_if),

     .ex1_xpr_regread_rs1(int_regread[VLSU_XPR_READ_PORT_IDX]),

     .i_phy_wr(w_ex3_phy_wr),

     .vec_phy_rd_if     (w_vec_phy_rd_if[VLSU_VPR_READ_PORT_IDX +: 2]),
     .vec_phy_old_wr_if (w_vec_phy_rd_if[VLSU_VPR_READ_PORT_IDX +  2]),
     .vec_phy_wr_if     (w_vec_phy_wr_if[2]),

     .l1d_rd_if    (vlsu_l1d_rd_if   ),
     .l1d_missu_if (vlsu_l1d_missu_if),

     .o_done_report(w_vlsu_done_rpt),

     .i_commit (w_commit),
     .br_upd_if(w_ex3_br_upd_if)
     );


  scariv_vec_registers
    #(
      .RD_PORT_SIZE(VLSU_VPR_READ_PORT_IDX + 3),
      .WR_PORT_SIZE(3)
      )
  u_vec_registers
    (
     .i_clk     (i_clk    ),
     .i_reset_n (i_reset_n),

     .regread (w_vec_phy_rd_if),
     .regwrite(w_vec_phy_wr_if)
     );


end endgenerate

scariv_rob u_rob
  (
   .i_clk    (i_clk),
   .i_reset_n(i_reset_n),

   .rn_front_if    (w_rn_front_if     ),
   .cre_ret_if (rob_cre_ret_if),

   .int_if     (w_int_if),

   .o_sc_new_cmt_id (w_sc_new_cmt_id),

   .i_done_rpt (w_done_rpt),
   .i_another_flush_report(w_lsu_another_flush_rpt),

   .o_commit (w_commit),
   .fflags_update_if (w_fflags_update_if),
   .o_commit_rnid_update (w_commit_rnid_update),

   .rob_info_if   (w_rob_info_if),
   .vlvtype_commit_if (w_vlvtype_commit),

   .ex3_br_upd_if (w_ex3_br_upd_if)
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
