module msrh_lsu_top
  import msrh_lsu_pkg::*;
(
    input logic i_clk,
    input logic i_reset_n,

    /* CSR information */
    csr_info_if.slave                     csr_info,

    input logic         [msrh_conf_pkg::DISP_SIZE-1:0] disp_valid,
    disp_if.watch                                      disp,
    cre_ret_if.slave    sch_cre_ret_if[msrh_conf_pkg::LSU_INST_NUM],
    cre_ret_if.slave    ldq_cre_ret_if,
    cre_ret_if.slave    stq_cre_ret_if,

    regread_if.master   ex1_regread[msrh_conf_pkg::LSU_INST_NUM * 2-1:0],

    // Page Table Walk I/O
    tlb_ptw_if.master ptw_if[msrh_conf_pkg::LSU_INST_NUM],

    // (Now) Use for PTW access L1D
    lsu_access_if.slave   lsu_access,

    l2_req_if.master  l1d_ext_req,
    l2_resp_if.slave  l1d_ext_resp,

    /* Forwarding path */
    input msrh_pkg::early_wr_t i_early_wr[msrh_pkg::REL_BUS_SIZE],
    input msrh_pkg::phy_wr_t   i_phy_wr [msrh_pkg::TGT_BUS_SIZE],

    /* write output */
    output msrh_pkg::early_wr_t o_ex1_early_wr[msrh_conf_pkg::LSU_INST_NUM],
    output msrh_pkg::phy_wr_t   o_ex3_phy_wr  [msrh_conf_pkg::LSU_INST_NUM],

    output msrh_pkg::done_rpt_t o_done_report[msrh_conf_pkg::LSU_INST_NUM],  // LDQ done report, STQ done report
    output msrh_pkg::mispred_t  o_ex3_mispred[msrh_conf_pkg::LSU_INST_NUM],

    // Commit notification
    input msrh_pkg::commit_blk_t i_commit
   );

// LSU Pipeline + STQ Interface + PTW
l1d_rd_if  w_l1d_rd_if [msrh_conf_pkg::LSU_INST_NUM + 1 + 1] ();
l1d_wr_if  w_l1d_wr_if();
// LSU Pipeline + PTW
l1d_lrq_if w_l1d_lrq_if[msrh_conf_pkg::LSU_INST_NUM] ();
l1d_lrq_if w_l1d_lrq_from_stq_miss ();
fwd_check_if w_ex2_fwd_check[msrh_conf_pkg::LSU_INST_NUM] ();

lrq_search_if w_lrq_search_if ();
lrq_resolve_t w_lrq_resolve;

// Feedbacks to LDQ / STQ
ex1_q_update_t        w_ex1_q_updates[msrh_conf_pkg::LSU_INST_NUM];
logic [msrh_conf_pkg::LSU_INST_NUM-1: 0] w_tlb_resolve;
ex2_q_update_t        w_ex2_q_updates[msrh_conf_pkg::LSU_INST_NUM];
ex2_addr_check_t      w_ex2_addr_check[msrh_conf_pkg::LSU_INST_NUM];

stq_resolve_t w_stq_resolve;

lsu_replay_if w_ldq_replay[msrh_conf_pkg::LSU_INST_NUM]();
lsu_replay_if w_stq_replay[msrh_conf_pkg::LSU_INST_NUM]();

logic [msrh_conf_pkg::LSU_INST_NUM-1: 0]   w_ex3_done;

logic [msrh_conf_pkg::DISP_SIZE-1: 0]      w_ldq_disp_valid;
logic [msrh_conf_pkg::DISP_SIZE-1: 0]      w_stq_disp_valid;

msrh_pkg::done_rpt_t w_ld_done_report[msrh_conf_pkg::LSU_INST_NUM];
msrh_pkg::done_rpt_t w_st_done_report[msrh_conf_pkg::LSU_INST_NUM];

generate for (genvar lsu_idx = 0; lsu_idx < msrh_conf_pkg::LSU_INST_NUM; lsu_idx++) begin : lsu_loop

  msrh_lsu
  #(
    .LSU_PIPE_IDX(lsu_idx),
    .PORT_BASE(lsu_idx * 2)
    )
  u_msrh_lsu
  (
    .i_clk    (i_clk    ),
    .i_reset_n(i_reset_n),

    .csr_info (csr_info),

    .disp_valid (disp_valid),
    .disp (disp),
    .cre_ret_if  (sch_cre_ret_if[lsu_idx]),

    .ex1_regread_rs1 (ex1_regread[lsu_idx * 2 + 0]),
    .ex1_regread_rs2 (ex1_regread[lsu_idx * 2 + 1]),

    .i_early_wr(i_early_wr),
    .i_phy_wr  (i_phy_wr),
    .i_mispred_lsu (o_ex3_mispred),

    .ex2_fwd_check_if (w_ex2_fwd_check[lsu_idx]),

    .ptw_if(ptw_if[lsu_idx]),
    .l1d_rd_if (w_l1d_rd_if[lsu_idx]),
    .l1d_lrq_if (w_l1d_lrq_if[lsu_idx]),

    .ldq_replay_if (w_ldq_replay[lsu_idx]),
    .stq_replay_if (w_stq_replay[lsu_idx]),

    .o_ex1_q_updates (w_ex1_q_updates [lsu_idx]),
    .o_tlb_resolve   (w_tlb_resolve   [lsu_idx]),
    .o_ex2_q_updates (w_ex2_q_updates [lsu_idx]),
    .o_ex2_addr_check(w_ex2_addr_check[lsu_idx]),

    .o_ex1_early_wr(o_ex1_early_wr[lsu_idx]),
    .o_ex3_phy_wr  (o_ex3_phy_wr  [lsu_idx]),

    .i_commit (i_commit),

    .o_ex3_mispred (o_ex3_mispred[lsu_idx]),
    .o_ex3_done (w_ex3_done [lsu_idx])
   );

  // Done Report Generate
  assign o_done_report[lsu_idx] = w_ld_done_report[lsu_idx].valid ? w_ld_done_report[lsu_idx] : w_st_done_report[lsu_idx];
`ifdef SIMULATION
  always_ff @ (negedge i_clk, negedge i_reset_n) begin
    if (!i_reset_n) begin
    end else begin
      if (w_ld_done_report[lsu_idx].valid & w_st_done_report[lsu_idx].valid) begin
        $fatal(0, "ld / st done report asserted in same time");
      end
    end
  end
`endif // SIMULATION
end // block: lsu_loop
endgenerate

generate for (genvar d_idx = 0; d_idx < msrh_conf_pkg::DISP_SIZE; d_idx++) begin : disp_loop
  assign w_ldq_disp_valid[d_idx] = disp_valid[d_idx] & disp.inst[d_idx].cat == decoder_inst_cat_pkg::INST_CAT_LD;
  assign w_stq_disp_valid[d_idx] = disp_valid[d_idx] & disp.inst[d_idx].cat == decoder_inst_cat_pkg::INST_CAT_ST;
end
endgenerate

// -----------------------------------
// Ldq
// -----------------------------------
msrh_ldq
  u_ldq
(
 .i_clk    (i_clk    ),
 .i_reset_n(i_reset_n),

 .i_disp_valid (w_ldq_disp_valid),
 .disp         (disp            ),
 .cre_ret_if   (ldq_cre_ret_if  ),

 .i_tlb_resolve   (w_tlb_resolve   ),
 .i_ex1_q_updates (w_ex1_q_updates ),
 .i_ex2_q_updates (w_ex2_q_updates ),
 .i_ex2_addr_check(w_ex2_addr_check),

 .i_lrq_resolve (w_lrq_resolve),
 .i_stq_resolve (w_stq_resolve),

 .ldq_replay_if (w_ldq_replay),

 .i_ex3_done (w_ex3_done),

 .i_commit (i_commit),
 .o_done_report(w_ld_done_report)
 );


// -----------------------------------
// STQ
// -----------------------------------
msrh_stq
  u_stq
(
 .i_clk    (i_clk    ),
 .i_reset_n(i_reset_n),

 .i_disp_valid (w_stq_disp_valid),
 .disp         (disp            ),
 .cre_ret_if   (stq_cre_ret_if  ),

 .i_early_wr (i_early_wr),

 .i_tlb_resolve  (w_tlb_resolve  ),
 .i_ex1_q_updates(w_ex1_q_updates),
 .i_ex2_q_updates(w_ex2_q_updates),

 .ex2_fwd_check_if(w_ex2_fwd_check),

 .stq_replay_if (w_stq_replay),

 .i_ex3_done (w_ex3_done),

 .i_commit (i_commit),
 .l1d_rd_if (w_l1d_rd_if[msrh_conf_pkg::LSU_INST_NUM]),
 .l1d_lrq_stq_miss_if (w_l1d_lrq_from_stq_miss),

 .i_lrq_resolve (w_lrq_resolve),
 .o_stq_resolve (w_stq_resolve),

 .l1d_wr_if (w_l1d_wr_if),

 .o_done_report(w_st_done_report)
 );


msrh_l1d_load_requester
  u_msrh_l1d_load_requester
(
 .i_clk    (i_clk    ),
 .i_reset_n(i_reset_n),
 .l1d_lrq  (w_l1d_lrq_if),

 .l1d_ext_req  (l1d_ext_req ),
 .l1d_ext_resp (l1d_ext_resp),

 .l1d_lrq_stq_miss_if (w_l1d_lrq_from_stq_miss),

 .lrq_search_if (w_lrq_search_if),
 .o_lrq_resolve (w_lrq_resolve)
 );

// --------------------------
// PTW L1D Access Interface
// --------------------------
logic                                 r_ptw_resp_valid;
logic [$clog2(msrh_conf_pkg::DCACHE_DATA_W / riscv_pkg::XLEN_W)-1:0] r_ptw_paddr_sel;
// logic                                 r_ptw_lrq_resp_full;
// logic                                 r_ptw_lrq_resp_conflict;
// logic [msrh_pkg::LRQ_ENTRY_SIZE-1: 0] r_ptw_lrq_resp_lrq_index_oh;

localparam L1D_PTW_PORT = msrh_conf_pkg::LSU_INST_NUM + 1;
assign w_l1d_rd_if [L1D_PTW_PORT].valid = lsu_access.req_valid;
assign w_l1d_rd_if [L1D_PTW_PORT].paddr = lsu_access.paddr;
assign lsu_access.resp_valid = r_ptw_resp_valid;
assign lsu_access.status = w_l1d_rd_if[L1D_PTW_PORT].hit      ? STATUS_HIT :
                           w_l1d_rd_if[L1D_PTW_PORT].conflict ? STATUS_L1D_CONFLICT :
                           // r_ptw_lrq_resp_conflict            ? STATUS_LRQ_CONFLICT :
                           w_l1d_rd_if[L1D_PTW_PORT].miss     ? STATUS_MISS :
                           STATUS_NONE;
// assign lsu_access.lrq_conflicted_idx_oh   = r_ptw_lrq_resp_lrq_index_oh;
assign lsu_access.lrq_conflicted_idx_oh = 'h0;
assign lsu_access.data                    = w_l1d_rd_if[L1D_PTW_PORT].data[{r_ptw_paddr_sel, {$clog2(riscv_pkg::XLEN_W){1'b0}}} +: riscv_pkg::XLEN_W];
assign lsu_access.conflict_resolve_vld    = w_lrq_resolve.valid;
assign lsu_access.conflict_resolve_idx_oh = w_lrq_resolve.resolve_index_oh;

// // ---------------------------
// // LRQ Access Check Interface
// // ---------------------------
// localparam LRQ_PTW_PORT = msrh_conf_pkg::LSU_INST_NUM;
// assign w_l1d_lrq_if[LRQ_PTW_PORT].load = lsu_access.req_valid;
// assign w_l1d_lrq_if[LRQ_PTW_PORT].req_payload.paddr = lsu_access.paddr;
always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_ptw_resp_valid    <= 1'b0;
    r_ptw_paddr_sel     <= 'h0;
    // r_ptw_lrq_resp_full <= 1'b0;
    // r_ptw_lrq_resp_conflict <= 1'b0;
    // r_ptw_lrq_resp_lrq_index_oh <= 'h0;
  end else begin
    r_ptw_paddr_sel             <= lsu_access.paddr[$clog2(riscv_pkg::XLEN_W / 8) +: $clog2(msrh_conf_pkg::DCACHE_DATA_W / riscv_pkg::XLEN_W)];
    r_ptw_resp_valid            <= lsu_access.req_valid;
    // r_ptw_lrq_resp_full         <= w_l1d_lrq_if[LRQ_PTW_PORT].resp_payload.full;
    // r_ptw_lrq_resp_conflict     <= w_l1d_lrq_if[LRQ_PTW_PORT].resp_payload.conflict;
    // r_ptw_lrq_resp_lrq_index_oh <= w_l1d_lrq_if[LRQ_PTW_PORT].resp_payload.lrq_index_oh;
  end
end

msrh_dcache
u_msrh_dcache
  (
   .i_clk(i_clk),
   .i_reset_n(i_reset_n),
   .l1d_rd_if (w_l1d_rd_if),
   .l1d_wr_if (w_l1d_wr_if),

   .l1d_ext_resp (l1d_ext_resp),

   .lrq_search_if (w_lrq_search_if)
   );

endmodule // mrsh_lsu_top
