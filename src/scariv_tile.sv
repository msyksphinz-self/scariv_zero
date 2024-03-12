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
tlb_ptw_if  w_ptw_if[1 +   // Frontend
                     scariv_conf_pkg::LSU_INST_NUM  // LSU
                     + 1]();  // Vector LSU
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
flush_report_if             w_flush_report_if[scariv_pkg::ANOTHER_FLUSH_SIZE]();

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

// ----------------------------------
// VEC Components
// ----------------------------------
localparam VPR_READ_PORT_NUM = 5 +  // from VALU
                               4 +  // from VLSU
                               0;
scariv_pkg::grp_id_t   w_disp_valu_valids ;
scariv_pkg::early_wr_t w_ex1_valu_early_wr;
vec_regread_if         w_vec_phy_rd_if[VPR_READ_PORT_NUM]()  ;
vec_regwrite_if        w_vec_phy_wr_if[3]()  ;
scariv_pkg::done_rpt_t w_valu_done_rpt[2]    ;
vec_phy_fwd_if         w_vec_phy_fwd_if[3]();
st_buffer_if           w_vlsu_st_buffer_if();
vstq_haz_check_if      w_vstq_haz_check_if[scariv_conf_pkg::LSU_INST_NUM]();
scalar_ldq_haz_check_if w_scalar_ldq_haz_check_if();
logic                   w_lmul_exception_mode;

scariv_pkg::grp_id_t   w_disp_vlsu_valids ;
scariv_pkg::early_wr_t w_ex1_vlsu_early_wr;
scariv_pkg::phy_wr_t   w_ex3_vlsu_phy_wr  ;
scariv_pkg::done_rpt_t w_vlsu_done_rpt    ;

vlmul_upd_if           w_vlmul_upd_if();

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
l1d_rd_if                       vlsu_l1d_rd_if   ();
l1d_missu_if                    vlsu_l1d_missu_if();
scariv_lsu_pkg::missu_resolve_t w_missu_resolve;
vlvtype_req_if                  w_vlvtype_req_if();

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

  .vlmul_upd_if   (w_vlmul_upd_if),

  .i_resource_ok (w_resource_ok),

  .i_brtag  (w_iq_brtag),

  .br_upd_if (w_ex3_br_upd_if),

  .vec_phy_fwd_if (w_vec_phy_fwd_if),
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
  .valu_cre_ret_if(valu_cre_ret_if),
  .vlsu_cre_ret_if(vlsu_cre_ret_if),

  .vlvtype_req_if (w_vlvtype_req_if),

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
    .flush_report_if(w_flush_report_if[0 +: scariv_conf_pkg::LSU_INST_NUM]),

    .snoop_info_if (w_snoop_info_if),

    .l1d_snoop_if   (l1d_snoop_if  ),
    .stq_snoop_if   (stq_snoop_if  ),
    .mshr_snoop_if  (mshr_snoop_if ),
    .stbuf_snoop_if (stbuf_snoop_if),
    .streq_snoop_if (streq_snoop_if),

    .sfence_if (w_sfence_if),
    .o_fence_i (w_fence_i),

    .vlsu_l1d_rd_if          (vlsu_l1d_rd_if           ),
    .vlsu_l1d_missu_if       (vlsu_l1d_missu_if        ),
    .o_missu_resolve         (w_missu_resolve          ),
    .vlsu_st_buffer_if       (w_vlsu_st_buffer_if      ),
    .vstq_haz_check_if       (w_vstq_haz_check_if      ),
    .scalar_ldq_haz_check_if (w_scalar_ldq_haz_check_if),

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
    .i_vlvtype_ren_idx (r_rn_vlvtype_info_if.vsetvl_index),
    .cre_ret_if (csu_cre_ret_if),

    .ex1_regread_rs1(int_regread[scariv_conf_pkg::ALU_INST_NUM * 2 +
                                 scariv_conf_pkg::LSU_INST_NUM + scariv_conf_pkg::STQ_REGRD_PORT_NUM +
                                 2]),
    .ex1_regread_rs2(int_regread[scariv_conf_pkg::ALU_INST_NUM * 2 +
                                 scariv_conf_pkg::LSU_INST_NUM + 1 +
                                 3]),

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

    .o_lmul_exception_mode (w_lmul_exception_mode),
    .vec_csr_if     (w_vec_csr_if),
    .vlvtype_upd_if (w_vlvtype_upd_if),
    .vlmul_upd_if   (w_vlmul_upd_if),

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
                                       2 +   // CSU
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

vlvtype_commit_if w_vlvtype_commit();
vlvtype_upd_if    w_vlvtype_upd_if();
vec_csr_if        w_vec_csr_if();
vlvtype_info_if   r_rn_vlvtype_info_if();

generate if (scariv_vec_pkg::VLEN_W != 0) begin : vpu
  scariv_vec_pkg::vlvtype_ren_idx_t  w_ibuf_vlvtype_index;

  scariv_vec_pkg::vlvtype_t r_rn_vlvtype;

  scariv_pkg::grp_id_t w_rn_is_subcat_vset;

  for (genvar d_idx = 0; d_idx < scariv_conf_pkg::DISP_SIZE; d_idx++) begin : csu_vset_loop
    assign w_rn_is_subcat_vset[d_idx] = (w_rn_front_if.payload.inst[d_idx].cat == decoder_inst_cat_pkg::INST_CAT_CSU) &
                                        (w_rn_front_if.payload.inst[d_idx].subcat == decoder_inst_cat_pkg::INST_SUBCAT_VSET);
  end

  assign w_vlvtype_req_if.valid              = w_rn_front_if.valid & w_rn_front_if.ready & (|w_rn_is_subcat_vset);
  assign w_vlvtype_req_if.checkpt_push_valid = |w_rn_front_if.payload.is_br_included;
`ifdef SIMULATION
  assign w_vlvtype_req_if.sim_cmt_id   = w_rn_front_if.payload.cmt_id;
  assign w_vlvtype_req_if.sim_grp_id   = w_rn_is_subcat_vset;
`endif // SIMULATION

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

     .vec_csr_if     (w_vec_csr_if),
     .vlvtype_upd_if (w_vlvtype_upd_if)
   );


  localparam VALU_READ_PORT_IDX = scariv_conf_pkg::ALU_INST_NUM * 2 +
                                  scariv_conf_pkg::LSU_INST_NUM + 1 +
                                  2 +   // BRU
                                  2 +   // CSU
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

     .phy_wr_if (w_phy_wr_if),

     .vec_phy_rd_if     (w_vec_phy_rd_if[VALU_VPR_READ_PORT_IDX +: 3]),
     .vec_phy_v0_if     (w_vec_phy_rd_if[VALU_VPR_READ_PORT_IDX +  4]),
     .vec_phy_old_wr_if (w_vec_phy_rd_if[VALU_VPR_READ_PORT_IDX +  3]),
     .vec_phy_wr_if     (w_vec_phy_wr_if[0:1]),
     .vec_valu_phy_fwd_if (w_vec_phy_fwd_if[0:1]),
     .vec_vlsu_phy_fwd_if (w_vec_phy_fwd_if[2]),

     .done_report_if (w_done_report_if [VALU_DONE_PORT_BASE +: 2]),

     .commit_if(w_commit_if),
     .br_upd_if(w_ex3_br_upd_if)
     );


  localparam VLSU_XPR_READ_PORT_IDX = VALU_READ_PORT_IDX + 1;
  localparam VLSU_VPR_READ_PORT_IDX = VALU_VPR_READ_PORT_IDX + 5;

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

     .i_lmul_exception_mode (w_lmul_exception_mode),

     .disp_valid      (w_disp_vlsu_valids),
     .disp            (w_rn_front_if),
     .vlvtype_info_if (r_rn_vlvtype_info_if),
     .vlvtype_upd_if  (w_vlvtype_upd_if),

     .cre_ret_if(vlsu_cre_ret_if),

     .ex1_xpr_regread_rs1(int_regread[VLSU_XPR_READ_PORT_IDX]),

     .phy_wr_if (w_phy_wr_if),

     .vec_phy_rd_if     (w_vec_phy_rd_if[VLSU_VPR_READ_PORT_IDX +: 3]),
     .vec_phy_old_wr_if (w_vec_phy_rd_if[VLSU_VPR_READ_PORT_IDX +  3]),
     .vec_phy_wr_if     (w_vec_phy_wr_if[2]),

     .vec_valu_phy_fwd_if (w_vec_phy_fwd_if[0:1]),
     .vec_vlsu_phy_fwd_if (w_vec_phy_fwd_if[2]),

     .scalar_ldq_haz_check_if (w_scalar_ldq_haz_check_if),

     .l1d_rd_if       (vlsu_l1d_rd_if   ),
     .l1d_missu_if    (vlsu_l1d_missu_if),
     .i_missu_resolve (w_missu_resolve  ),

     .done_report_if (w_done_report_if [VLSU_DONE_PORT_BASE]),
     .flush_report_if(w_flush_report_if[scariv_conf_pkg::LSU_INST_NUM]),

     .commit_if(w_commit_if),
     .br_upd_if(w_ex3_br_upd_if),

     .st_buffer_if      (w_vlsu_st_buffer_if),
     .vstq_haz_check_if (w_vstq_haz_check_if)
     );


  scariv_vec_registers
    #(
      .RD_PORT_SIZE(VPR_READ_PORT_NUM),
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

   .done_report_if  (w_done_report_if ),
   .flush_report_if (w_flush_report_if),

   .commit_if (w_commit_if),
   .fflags_update_if (w_fflags_update_if),
   .o_commit_rnid_update (w_commit_rnid_update),

   .rob_info_if   (w_rob_info_if),
   .vlvtype_commit_if (w_vlvtype_commit),

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
