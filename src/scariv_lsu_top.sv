// ------------------------------------------------------------------------
// NAME : scariv_lsu_top
// TYPE : package
// ------------------------------------------------------------------------
// LSU Top
// ------------------------------------------------------------------------
// SubUnit
//  LSU SubUnit
//  LDQ
//  STQ
//  MSHR
//  Store Requseter for L2
//  ST-Buffer for Store Merge
//  LR/SC Unit
//  DCache
// ------------------------------------------------------------------------

module scariv_lsu_top
  import scariv_lsu_pkg::*;
(
    input logic i_clk,
    input logic i_reset_n,

    /* CSR information */
    csr_info_if.slave                     csr_info,

    /* ROB notification interface */
    rob_info_if.slave           rob_info_if,

    input logic         [scariv_conf_pkg::DISP_SIZE-1:0] disp_valid,
    scariv_front_if.watch                                      disp,
    cre_ret_if.slave    iss_cre_ret_if[scariv_conf_pkg::LSU_INST_NUM],
    cre_ret_if.slave    ldq_cre_ret_if,
    cre_ret_if.slave    stq_cre_ret_if,

    regread_if.master   ex1_int_regread[scariv_conf_pkg::LSU_INST_NUM-1: 0],

    regread_if.master   int_rs2_regread,
    regread_if.master   fp_rs2_regread ,

    // Page Table Walk I/O
    tlb_ptw_if.master ptw_if[scariv_conf_pkg::LSU_INST_NUM],

    // (Now) Use for PTW access L1D
    lsu_access_if.slave   lsu_access,

    l2_req_if.master  l1d_ext_req,
    l2_resp_if.slave  l1d_ext_resp,

    /* Forwarding path */
    input scariv_pkg::early_wr_t i_early_wr[scariv_pkg::REL_BUS_SIZE],
    input scariv_pkg::phy_wr_t   i_phy_wr [scariv_pkg::TGT_BUS_SIZE],

    /* write output */
    output scariv_pkg::early_wr_t o_ex1_early_wr[scariv_conf_pkg::LSU_INST_NUM],
    output scariv_pkg::phy_wr_t   o_ex3_phy_wr  [scariv_conf_pkg::LSU_INST_NUM],

    output scariv_pkg::done_rpt_t      o_done_report          [scariv_conf_pkg::LSU_INST_NUM],  // LDQ done report, STQ done report
    output scariv_pkg::another_flush_t o_another_flush_report [scariv_conf_pkg::LSU_INST_NUM],

    output scariv_pkg::mispred_t  o_ex2_mispred[scariv_conf_pkg::LSU_INST_NUM],

    // Internal Broadcast Interface
    snoop_info_if.monitor snoop_info_if,
    l1d_snoop_if.slave   l1d_snoop_if,
    stq_snoop_if.slave   stq_snoop_if,
    mshr_snoop_if.slave  mshr_snoop_if,
    stbuf_snoop_if.slave stbuf_snoop_if,
    streq_snoop_if.slave streq_snoop_if,

    /* SFENCE update information */
    sfence_if.master            sfence_if,
    /* FENCE.I update */
    output logic                o_fence_i,

    // ----------------------
    // Vector LSU interface
    // ----------------------
    l1d_rd_if.slave             vlsu_l1d_rd_if,
    l1d_missu_if.slave          vlsu_l1d_missu_if,
    output missu_resolve_t      o_missu_resolve,

    // Commit notification
    input scariv_pkg::commit_blk_t i_commit,
    br_upd_if.slave              br_upd_if
   );

// LSU Pipeline + STQ Interface + PTW + Snoop
localparam L1D_SNOOP_PORT    = 0;
localparam L1D_PTW_PORT      = L1D_SNOOP_PORT   + 1;
localparam L1D_LS_PORT_BASE  = L1D_PTW_PORT     + 1;
localparam L1D_MISSU_PORT    = L1D_LS_PORT_BASE + scariv_conf_pkg::LSU_INST_NUM;
localparam L1D_ST_RD_PORT    = L1D_MISSU_PORT   + 1;
localparam L1D_VLSU_RD_PORT  = L1D_ST_RD_PORT   + 1;
localparam L1D_RD_PORT_NUM   = L1D_VLSU_RD_PORT + 1;

l1d_rd_if  w_l1d_rd_if [L1D_RD_PORT_NUM] ();
l1d_wr_if  w_l1d_stbuf_wr_if();
l1d_wr_if  w_l1d_merge_if();
l1d_wr_if  w_miss_l1d_wr_if();
l1d_wr_if  w_snoop_wr_if();
// LSU Pipeline + ST-Buffer
l1d_missu_if w_l1d_missu_if   [scariv_lsu_pkg::MSHR_REQ_PORT_NUM] ();
fwd_check_if w_ex2_fwd_check  [scariv_conf_pkg::LSU_INST_NUM] ();
fwd_check_if w_stbuf_fwd_check[scariv_conf_pkg::LSU_INST_NUM] ();
fwd_check_if w_streq_fwd_check[scariv_conf_pkg::LSU_INST_NUM] ();

missu_dc_search_if w_missu_dc_search_if ();
missu_resolve_t w_missu_resolve;
logic     w_missu_is_full;
logic     w_missu_is_empty;
logic     w_stq_rmw_existed;

stq_resolve_t w_stq_rs2_resolve;

l2_req_if    w_l1d_ext_req[2]();
l1d_evict_if w_l1d_evict_if();

// Feedbacks to LDQ / STQ
ex1_q_update_t        w_ex1_q_updates[scariv_conf_pkg::LSU_INST_NUM];
logic [scariv_conf_pkg::LSU_INST_NUM-1: 0] w_tlb_resolve;
ex2_q_update_t        w_ex2_q_updates[scariv_conf_pkg::LSU_INST_NUM];

done_if w_ex3_done_if[scariv_conf_pkg::LSU_INST_NUM]();

scariv_pkg::grp_id_t      w_ldq_disp_valid;
scariv_pkg::grp_id_t      w_stq_disp_valid;

scariv_pkg::done_rpt_t w_done_report[scariv_conf_pkg::LSU_INST_NUM];

missu_fwd_if w_missu_fwd_if [scariv_conf_pkg::LSU_INST_NUM]();
ldq_haz_check_if w_ldq_haz_check_if [scariv_conf_pkg::LSU_INST_NUM]();
stq_haz_check_if w_stq_haz_check_if [scariv_conf_pkg::LSU_INST_NUM]();

rmw_order_check_if w_rmw_order_check_if[scariv_conf_pkg::LSU_INST_NUM]();

lrsc_if  w_lrsc_if[scariv_conf_pkg::LSU_INST_NUM]();

st_buffer_if            w_st_buffer_if();
missu_pa_search_if      w_missu_pa_search_if();
mshr_stbuf_search_if    w_mshr_stbuf_search_if();
uc_write_if             w_uc_write_if();

st_req_info_if          w_st_req_info_if();

sfence_if                                  w_sfence_if_inst[scariv_conf_pkg::LSU_INST_NUM]();
logic [scariv_conf_pkg::LSU_INST_NUM-1: 0] w_fence_i;
logic [scariv_conf_pkg::LSU_INST_NUM-1: 0] w_sfence_if_valid;
logic [scariv_conf_pkg::LSU_INST_NUM-1: 0] w_sfence_if_is_rs1_x0;
logic [scariv_conf_pkg::LSU_INST_NUM-1: 0] w_sfence_if_is_rs2_x0;
scariv_pkg::vaddr_t w_sfence_if_vaddr[scariv_conf_pkg::LSU_INST_NUM];

assign o_fence_i = |w_fence_i;

assign sfence_if.valid     = |w_sfence_if_valid;
assign sfence_if.is_rs1_x0 = |w_sfence_if_is_rs1_x0;
assign sfence_if.is_rs2_x0 = |w_sfence_if_is_rs2_x0;
bit_oh_or #(.T(scariv_pkg::vaddr_t), .WORDS(scariv_conf_pkg::LSU_INST_NUM)) u_sfence_vaddr_merge (.i_oh(w_sfence_if_valid), .i_data(w_sfence_if_vaddr), .o_selected(sfence_if.vaddr));


generate for (genvar lsu_idx = 0; lsu_idx < scariv_conf_pkg::LSU_INST_NUM; lsu_idx++) begin : lsu_loop

  scariv_lsu
  #(
    .LSU_PIPE_IDX(lsu_idx),
    .PORT_BASE(lsu_idx * (scariv_conf_pkg::MEM_DISP_SIZE / scariv_conf_pkg::LSU_INST_NUM))
    )
  u_scariv_lsu
  (
    .i_clk    (i_clk    ),
    .i_reset_n(i_reset_n),

    .csr_info (csr_info),
    .rob_info_if (rob_info_if),
    .sfence_if_slave (sfence_if),

    .disp_valid (disp_valid             ),
    .disp       (disp                   ),
    .cre_ret_if (iss_cre_ret_if[lsu_idx]),

    .ex1_regread_rs1     (ex1_int_regread[lsu_idx]),

    .i_early_wr(i_early_wr),
    .i_phy_wr  (i_phy_wr),
    .i_mispred_lsu (o_ex2_mispred),

    .ex2_fwd_check_if (w_ex2_fwd_check[lsu_idx]),
    .stbuf_fwd_check_if (w_stbuf_fwd_check[lsu_idx]),
    .streq_fwd_check_if (w_streq_fwd_check[lsu_idx]),

    .ptw_if(ptw_if[lsu_idx]),
    .l1d_rd_if (w_l1d_rd_if[L1D_LS_PORT_BASE + lsu_idx]),
    .l1d_missu_if (w_l1d_missu_if[lsu_idx]),
    .ldq_haz_check_if (w_ldq_haz_check_if[lsu_idx]),
    .stq_haz_check_if (w_stq_haz_check_if[lsu_idx]),
    .missu_fwd_if (w_missu_fwd_if[lsu_idx]),

    .rmw_order_check_if (w_rmw_order_check_if[lsu_idx]),
    .lrsc_if            (w_lrsc_if[lsu_idx]),

    .o_ex1_q_updates (w_ex1_q_updates [lsu_idx]),
    .o_tlb_resolve   (w_tlb_resolve   [lsu_idx]),
    .o_ex2_q_updates (w_ex2_q_updates [lsu_idx]),

    .i_st_buffer_empty    (w_st_buffer_if.is_empty),
    .i_st_requester_empty (w_uc_write_if.is_empty ),

    .i_stq_rmw_existed (w_stq_rmw_existed),
    .i_stq_rs2_resolve (w_stq_rs2_resolve),

    .i_missu_resolve (w_missu_resolve),
    .i_missu_is_full (w_missu_is_full),
    .i_missu_is_empty (w_missu_is_empty),

    .o_ex1_early_wr(o_ex1_early_wr[lsu_idx]),
    .o_ex3_phy_wr  (o_ex3_phy_wr  [lsu_idx]),

    .sfence_if_master (w_sfence_if_inst[lsu_idx]),
    .o_fence_i (w_fence_i[lsu_idx]),

    .i_commit (i_commit),

    .o_ex2_mispred          (o_ex2_mispred         [lsu_idx]),
    .o_done_report          (o_done_report         [lsu_idx]),
    .o_another_flush_report (o_another_flush_report[lsu_idx]),
    .br_upd_if              (br_upd_if             )
   );

  assign w_sfence_if_valid    [lsu_idx] = w_sfence_if_inst[lsu_idx].valid;
  assign w_sfence_if_is_rs1_x0[lsu_idx] = w_sfence_if_inst[lsu_idx].is_rs1_x0;
  assign w_sfence_if_is_rs2_x0[lsu_idx] = w_sfence_if_inst[lsu_idx].is_rs2_x0;
  assign w_sfence_if_vaddr    [lsu_idx] = w_sfence_if_inst[lsu_idx].vaddr;

end // block: lsu_loop
endgenerate

generate for (genvar d_idx = 0; d_idx < scariv_conf_pkg::DISP_SIZE; d_idx++) begin : disp_loop
  assign w_ldq_disp_valid[d_idx] = disp_valid[d_idx] & disp.payload.inst[d_idx].cat == decoder_inst_cat_pkg::INST_CAT_LD;
  assign w_stq_disp_valid[d_idx] = disp_valid[d_idx] & disp.payload.inst[d_idx].cat == decoder_inst_cat_pkg::INST_CAT_ST;
end
endgenerate

// -----------------------------------
// Ldq
// -----------------------------------
scariv_ldq
u_ldq
(
 .i_clk    (i_clk    ),
 .i_reset_n(i_reset_n),

 .rob_info_if (rob_info_if),

 .i_disp_valid (w_ldq_disp_valid),
 .disp         (disp            ),
 .cre_ret_if   (ldq_cre_ret_if  ),

 .ldq_haz_check_if (w_ldq_haz_check_if),

 .i_ex1_q_updates(w_ex1_q_updates),
 .i_ex2_q_updates(w_ex2_q_updates),

 .i_missu_resolve (w_missu_resolve),
 .i_missu_is_full (w_missu_is_full),

 .i_stq_rs2_resolve (w_stq_rs2_resolve),

 .ex3_done_if (w_ex3_done_if),

 .st_buffer_if (w_st_buffer_if),
 .uc_write_if  (w_uc_write_if),

 .i_commit (i_commit),
 .br_upd_if (br_upd_if),
 .o_done_report()
 );


// -----------------------------------
// STQ
// -----------------------------------
scariv_stq
  u_stq
(
 .i_clk    (i_clk    ),
 .i_reset_n(i_reset_n),

 .rob_info_if (rob_info_if),

 .i_disp_valid (w_stq_disp_valid),
 .disp         (disp            ),
 .cre_ret_if   (stq_cre_ret_if  ),

 .i_early_wr    (i_early_wr),
 .i_phy_wr      (i_phy_wr  ),
 .i_mispred_lsu (o_ex2_mispred),

 .i_tlb_resolve  (w_tlb_resolve  ),
 .i_ex1_q_updates(w_ex1_q_updates),
 .i_ex2_q_updates(w_ex2_q_updates),

  .int_rs2_regread (int_rs2_regread),
  .fp_rs2_regread  (fp_rs2_regread ),

 .ex2_fwd_check_if(w_ex2_fwd_check),
 .stq_haz_check_if (w_stq_haz_check_if),
 .rmw_order_check_if (w_rmw_order_check_if),

 .ex3_done_if (w_ex3_done_if),

 .i_missu_is_empty (w_missu_is_empty),

  .o_stq_rmw_existed (w_stq_rmw_existed),

 .i_commit (i_commit),
 .br_upd_if (br_upd_if),

 .st_buffer_if (w_st_buffer_if),
 .uc_write_if  (w_uc_write_if),

 .stq_snoop_if(stq_snoop_if),

 .o_stq_rs2_resolve (w_stq_rs2_resolve)
);

assign w_l1d_rd_if [L1D_MISSU_PORT].s0_valid = 'h0;

assign w_l1d_missu_if[scariv_conf_pkg::LSU_INST_NUM + 1].load = vlsu_l1d_missu_if.load;
assign w_l1d_missu_if[scariv_conf_pkg::LSU_INST_NUM + 1].req_payload = vlsu_l1d_missu_if.req_payload;
assign vlsu_l1d_missu_if.resp_payload = w_l1d_missu_if[scariv_conf_pkg::LSU_INST_NUM + 1].resp_payload;

assign o_missu_resolve = w_missu_resolve;

scariv_l1d_mshr
u_l1d_mshr
(
 .i_clk    (i_clk    ),
 .i_reset_n(i_reset_n),

 .l1d_missu  (w_l1d_missu_if),
 .missu_fwd_if (w_missu_fwd_if),

 .o_missu_is_full  (w_missu_is_full ),
 .o_missu_resolve  (w_missu_resolve ),
 .o_missu_is_empty (w_missu_is_empty),

 .l1d_ext_rd_req  (w_l1d_ext_req[0]),
 .l1d_ext_rd_resp (l1d_ext_resp  ),

 .l1d_wr_if (w_miss_l1d_wr_if),

 .l1d_evict_if  (w_l1d_evict_if),

 .snoop_info_if (snoop_info_if),
 .mshr_snoop_if (mshr_snoop_if),

 .st_req_info_if (w_st_req_info_if),

 .mshr_stbuf_search_if (w_mshr_stbuf_search_if),

 .missu_pa_search_if (w_missu_pa_search_if),
 .missu_dc_search_if (w_missu_dc_search_if)
 );


scariv_store_requestor
u_scariv_store_requester
  (
   .i_clk (i_clk),
   .i_reset_n (i_reset_n),

   .fwd_check_if  (w_streq_fwd_check),

   .st_req_info_if (w_st_req_info_if),

   .l1d_evict_if  (w_l1d_evict_if),
   .uc_write_if   (w_uc_write_if),

   .streq_snoop_if(streq_snoop_if),

   .l1d_ext_wr_req(w_l1d_ext_req[1])
   );

scariv_st_buffer
u_st_buffer
  (
   .i_clk (i_clk),
   .i_reset_n (i_reset_n),

   .st_buffer_if        (w_st_buffer_if),
   .l1d_rd_if           (w_l1d_rd_if[L1D_ST_RD_PORT]),
   .l1d_missu_stq_miss_if (w_l1d_missu_if[scariv_conf_pkg::LSU_INST_NUM]),
   .l1d_stbuf_wr_if       (w_l1d_stbuf_wr_if),
   .l1d_mshr_wr_if        (w_miss_l1d_wr_if),

   .snoop_info_if  (snoop_info_if),
   .stbuf_snoop_if (stbuf_snoop_if),

   .rmw_order_check_if  (w_rmw_order_check_if),

   .stbuf_fwd_check_if  (w_stbuf_fwd_check),
   .missu_pa_search_if  (w_missu_pa_search_if),

   .mshr_stbuf_search_if (w_mshr_stbuf_search_if),
   .i_missu_resolve      (w_missu_resolve)
   );


l2_if_arbiter
  #(.ARB_NUM(2))
u_scariv_l2_req_arbiter
(
 .l2_req_slave_if  (w_l1d_ext_req),
 .l2_req_master_if (l1d_ext_req  )
 );


scariv_lsu_lrsc
u_lrsc
  (
   .i_clk     (i_clk    ),
   .i_reset_n (i_reset_n),

   .lrsc_if (w_lrsc_if)
   );


// --------------------------
// PTW L1D Access Interface
// --------------------------
logic                                 r_ptw_resp_valid;
logic [$clog2(scariv_conf_pkg::DCACHE_DATA_W / riscv_pkg::XLEN_W)-1:0] r_ptw_paddr_sel;
// logic                                 r_ptw_missu_resp_full;
// logic                                 r_ptw_missu_resp_conflict;
// logic [scariv_conf_pkg::MISSU_ENTRY_SIZE-1: 0] r_ptw_missu_resp_missu_index_oh;

assign w_l1d_rd_if [L1D_PTW_PORT].s0_valid = lsu_access.req_valid;
assign w_l1d_rd_if [L1D_PTW_PORT].s0_high_priority = 1'b0;
assign w_l1d_rd_if [L1D_PTW_PORT].s0_paddr = lsu_access.paddr;
assign lsu_access.resp_valid = r_ptw_resp_valid;
assign lsu_access.status = w_l1d_rd_if[L1D_PTW_PORT].s1_conflict ? STATUS_L1D_CONFLICT :
                           w_l1d_rd_if[L1D_PTW_PORT].s1_hit      ? STATUS_HIT :
                           w_l1d_rd_if[L1D_PTW_PORT].s1_miss     ? STATUS_MISS :
                           STATUS_NONE;
// assign lsu_access.missu_conflicted_idx_oh   = r_ptw_missu_resp_missu_index_oh;
assign lsu_access.missu_conflicted_idx_oh = 'h0;
assign lsu_access.data                    = w_l1d_rd_if[L1D_PTW_PORT].s1_data[{r_ptw_paddr_sel, {$clog2(riscv_pkg::XLEN_W){1'b0}}} +: riscv_pkg::XLEN_W];
assign lsu_access.conflict_resolve_vld    = w_missu_resolve.valid;
assign lsu_access.conflict_resolve_idx_oh = w_missu_resolve.resolve_index_oh;

always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_ptw_resp_valid    <= 1'b0;
    r_ptw_paddr_sel     <= 'h0;
  end else begin
    r_ptw_paddr_sel             <= lsu_access.paddr[$clog2(riscv_pkg::XLEN_W / 8) +: $clog2(scariv_conf_pkg::DCACHE_DATA_W / riscv_pkg::XLEN_W)];
    r_ptw_resp_valid            <= lsu_access.req_valid;
  end
end

// ---------------------------
//  L1D Snoop Interface
// ---------------------------
logic r_snoop_resp_valid;

assign w_l1d_rd_if [L1D_SNOOP_PORT].s0_valid = l1d_snoop_if.req_s0_valid & (l1d_snoop_if.req_s0_cmd == SNOOP_READ);
assign w_l1d_rd_if [L1D_SNOOP_PORT].s0_paddr = l1d_snoop_if.req_s0_paddr;
assign w_l1d_rd_if [L1D_SNOOP_PORT].s0_high_priority = 1'b0;

assign l1d_snoop_if.resp_s1_valid  = r_snoop_resp_valid;
assign l1d_snoop_if.resp_s1_status = w_l1d_rd_if[L1D_SNOOP_PORT].s1_conflict ? STATUS_L1D_CONFLICT :
                                     w_l1d_rd_if[L1D_SNOOP_PORT].s1_hit      ? STATUS_HIT :
                                     w_l1d_rd_if[L1D_SNOOP_PORT].s1_miss     ? STATUS_MISS :
                                     STATUS_NONE;
assign l1d_snoop_if.resp_s1_ways   = w_l1d_rd_if[L1D_SNOOP_PORT].s1_hit_way;
assign l1d_snoop_if.resp_s1_be     = w_l1d_rd_if[L1D_SNOOP_PORT].s1_hit ? {DCACHE_DATA_B_W{1'b1}} : {DCACHE_DATA_B_W{1'b0}};
assign l1d_snoop_if.resp_s1_data   = w_l1d_rd_if[L1D_SNOOP_PORT].s1_data;

assign w_snoop_wr_if.s0_valid           = l1d_snoop_if.req_s0_valid & (l1d_snoop_if.req_s0_cmd == SNOOP_INVALID);
assign w_snoop_wr_if.s0_wr_req.s0_way   = l1d_snoop_if.req_s0_ways;
assign w_snoop_wr_if.s0_wr_req.s0_paddr = l1d_snoop_if.req_s0_paddr;
assign w_snoop_wr_if.s0_wr_req.s0_data  = 'h0;
assign w_snoop_wr_if.s0_wr_req.s0_mesi  = scariv_lsu_pkg::MESI_INVALID;

always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_snoop_resp_valid <= 1'b0;
  end else begin
    r_snoop_resp_valid <= l1d_snoop_if.req_s0_valid;
  end
end


// ----------------------
// Vector LSU interface
// ----------------------
assign w_l1d_rd_if [L1D_VLSU_RD_PORT].s0_valid = vlsu_l1d_rd_if.s0_valid;
assign w_l1d_rd_if [L1D_VLSU_RD_PORT].s0_paddr = vlsu_l1d_rd_if.s0_paddr;
assign w_l1d_rd_if [L1D_VLSU_RD_PORT].s0_high_priority = 1'b0;

assign vlsu_l1d_rd_if.s1_conflict = w_l1d_rd_if[L1D_VLSU_RD_PORT].s1_conflict;
assign vlsu_l1d_rd_if.s1_miss     = w_l1d_rd_if[L1D_VLSU_RD_PORT].s1_miss;
assign vlsu_l1d_rd_if.s1_hit      = w_l1d_rd_if[L1D_VLSU_RD_PORT].s1_hit;
assign vlsu_l1d_rd_if.s1_hit_way  = w_l1d_rd_if[L1D_VLSU_RD_PORT].s1_hit_way;
assign vlsu_l1d_rd_if.s1_data     = w_l1d_rd_if[L1D_VLSU_RD_PORT].s1_data;


scariv_dcache
  #(.RD_PORT_NUM (L1D_RD_PORT_NUM))
u_scariv_dcache
  (
   .i_clk(i_clk),
   .i_reset_n(i_reset_n),

   .l1d_rd_if       (w_l1d_rd_if),
   .stbuf_l1d_wr_if (w_l1d_stbuf_wr_if),

   .stbuf_l1d_merge_if (w_l1d_merge_if  ),
   .missu_l1d_wr_if    (w_miss_l1d_wr_if),

   .snoop_wr_if        (w_snoop_wr_if),

   .missu_dc_search_if (w_missu_dc_search_if)
   );

endmodule // mrsh_lsu_top
