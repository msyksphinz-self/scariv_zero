// ------------------------------------------------------------------------
// NAME : scariv_vec_lsu_pipe
// TYPE : module
// ------------------------------------------------------------------------
// LSU Pipeline
// ------------------------------------------------------------------------
//
// ------------------------------------------------------------------------

module scariv_vec_lsu_pipe
  import decoder_vlsu_ctrl_pkg::*;
  import scariv_lsu_pkg::*;
(
 input logic i_clk,
 input logic i_reset_n,

 /* SFENCE update information */
 sfence_if.slave    sfence_if,
 /* CSR information */
 csr_info_if.slave  csr_info,
 /* Page Table Walk I/O */
 tlb_ptw_if.master ptw_if,

 // Commit notification
 commit_if.monitor              commit_if,
 br_upd_if.slave                br_upd_if,

 input scariv_vec_pkg::issue_t  i_ex0_issue,
 input logic                    i_ex0_replay_selected,
 input scariv_vec_pkg::vlsu_replay_info_t i_ex0_replay_info,

 input scariv_pkg::phy_wr_t     ex1_i_phy_wr[scariv_pkg::TGT_BUS_SIZE],

 output logic                   o_pipe_stall,

 regread_if.master      ex0_xpr_regread_rs1,

 vec_regread_if.master  vec_phy_rd_if[2],
 vec_regread_if.master  vec_phy_old_wr_if,
 vec_regwrite_if.master vec_phy_wr_if ,
 vec_phy_fwd_if.master  vec_phy_fwd_if[1],

 output logic           o_tlb_resolve,

 input logic            i_replay_queue_full,

 /* EX1 L1D read stage */
 l1d_rd_if.master       l1d_rd_if,
 /* EX2 L1D MSHR control */
 l1d_missu_if.master    l1d_missu_if,

 /* Interface for Replay Queue */
 lsu_pipe_haz_if.master lsu_pipe_haz_if,

 vlsu_lsq_req_if.master vlsu_ldq_req_if,
 vlsu_lsq_req_if.master vlsu_stq_req_if,

 scalar_ldq_haz_check_if.master scalar_ldq_haz_check_if,

 output scariv_pkg::done_rpt_t      o_done_report,
 output scariv_pkg::another_flush_t o_another_flush_report
 );

logic   w_commit_flush;

pipe_ctrl_t w_ex0_pipe_ctrl;
pipe_ctrl_t w_ex0_pipe_ctrl_next;
logic                    w_ex0_br_flush;

scariv_vec_pkg::issue_t  r_ex1_issue;
scariv_vec_pkg::issue_t  w_ex1_issue_next;
logic                    w_ex1_stall;
logic                    w_ex1_agu_req_splitted;
logic [$clog2(scariv_vec_pkg::DLENB)-1: 0]    w_ex1_reg_offset;
riscv_pkg::xlen_t        w_ex1_rs1_data;
scariv_pkg::vaddr_t      w_ex1_vaddr;
tlb_req_t                w_ex1_tlb_req;
tlb_resp_t               w_ex1_tlb_resp;
pipe_ctrl_t              r_ex1_pipe_ctrl;
scariv_pkg::maxaddr_t    w_ex1_addr; // VADDR(when exception) and PADDR
scariv_vec_pkg::dlen_t   w_ex1_vpr_rs_data[2];
logic                    w_ex1_br_flush;
logic                    w_ex1_ld_except_valid;
logic                    w_ex1_st_except_valid;
scariv_pkg::except_t     w_ex1_tlb_except_type;

logic                    w_ex1_replay_selected_next;
scariv_vec_pkg::vlsu_replay_info_t  w_ex1_replay_info_next;
logic                    r_ex1_replay_selected;
scariv_vec_pkg::vlsu_replay_info_t  r_ex1_replay_info;

scariv_vec_pkg::issue_t  r_ex2_issue;
scariv_vec_pkg::issue_t  w_ex2_issue_next;
logic                    r_ex2_replay_selected;
logic                    r_ex2_replay_haz_1st_req;
scariv_pkg::maxaddr_t    r_ex2_addr;
scariv_vec_pkg::vlenbmax_t   w_ex2_vl;
logic [ 1: 0]            r_ex2_req_splitted;
logic [$clog2(scariv_vec_pkg::DLENB)-1: 0]    r_ex2_reg_offset;
pipe_ctrl_t              r_ex2_pipe_ctrl;
logic                    r_ex2_except_valid;
scariv_pkg::except_t     r_ex2_except_type;
logic                    w_ex2_br_flush;
logic                    w_ex2_l1d_missed;
logic                    w_ex2_l1d_conflicted;
logic                    w_ex2_l1d_hazard;
logic                    w_ex2_hazard;
logic                    r_ex2_is_uc;
scariv_lsu_pkg::dc_data_t w_ex2_l1d_data;
scariv_vec_pkg::dlen_t   w_ex2_aligned_data;
logic                    w_ex2_l1d_vec_step_success;
logic                    w_ex2_vec_step_success;
logic                    w_ex2_is_1st_request;
logic                    w_ex2_stq_alloc_neglected;
logic                    w_ex2_stq_alloc_full_flush;

scariv_vec_pkg::issue_t  r_ex3_issue;
scariv_vec_pkg::issue_t  w_ex3_issue_next;
pipe_ctrl_t r_ex3_pipe_ctrl;
logic [ 1: 0]            r_ex3_req_splitted;
logic [$clog2(scariv_vec_pkg::DLENB)-1: 0]    r_ex3_reg_offset;
logic                    r_ex3_except_valid;
scariv_pkg::except_t     r_ex3_except_type;
scariv_pkg::maxaddr_t    r_ex3_addr;
logic                    r_ex3_mis_valid;
scariv_vec_pkg::dlen_t   r_ex3_aligned_data;
scariv_vec_pkg::dlen_t   w_ex3_aligned_data_next;
logic                    r_ex3_vec_step_success;
scariv_vec_pkg::dlenb_t  r_ex3_mask;

assign w_commit_flush = commit_if.is_flushed_commit();


// ---------------------
// EX0
// ---------------------

decoder_vlsu_ctrl u_pipe_ctrl (
  .inst (i_ex0_issue.inst),
  .op   (w_ex0_pipe_ctrl.op),
  .size (w_ex0_pipe_ctrl.size)
);

assign w_ex0_br_flush = scariv_pkg::is_br_flush_target(i_ex0_issue.cmt_id, i_ex0_issue.grp_id, br_upd_if.cmt_id, br_upd_if.grp_id,
                                                       br_upd_if.dead, br_upd_if.mispredict) & br_upd_if.update & i_ex0_issue.valid;

assign ex0_xpr_regread_rs1.valid = i_ex0_issue.valid & (i_ex0_issue.rd_regs[0].typ == scariv_pkg::GPR) & i_ex0_issue.rd_regs[0].valid;
assign ex0_xpr_regread_rs1.rnid  = i_ex0_issue.rd_regs[0].rnid;

generate for (genvar rs_idx = 0; rs_idx < 2; rs_idx++) begin : rs_vec_rd_loop
  assign vec_phy_rd_if[rs_idx].valid = i_ex0_issue.valid & (i_ex0_issue.rd_regs[rs_idx].typ == scariv_pkg::VPR) & i_ex0_issue.rd_regs[rs_idx].valid;
  assign vec_phy_rd_if[rs_idx].rnid  = i_ex0_issue.rd_regs[rs_idx].rnid;
  assign vec_phy_rd_if[rs_idx].pos   = i_ex0_issue.vec_step_index;
end endgenerate

// ---------------------
// EX1
// ---------------------

always_comb begin
  if (w_ex1_stall) begin
    w_ex1_issue_next           = r_ex1_issue;
    w_ex0_pipe_ctrl_next       = r_ex1_pipe_ctrl;
    w_ex1_replay_selected_next = r_ex1_replay_selected;
    w_ex1_replay_info_next     = r_ex1_replay_info;
  end else begin
    w_ex1_issue_next       = i_ex0_issue;
    w_ex1_issue_next.valid = i_ex0_issue.valid;
    w_ex1_replay_selected_next = i_ex0_replay_selected;
    w_ex1_replay_info_next     = i_ex0_replay_info;
    w_ex0_pipe_ctrl_next       = w_ex0_pipe_ctrl;
  end // else: !if(w_ex1_stall)

  // Aplly flush
  w_ex1_issue_next.valid = w_ex1_issue_next.valid & !w_commit_flush & !w_ex0_br_flush;
end

always_ff @(posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_ex1_issue.valid <= 1'b0;
  end else begin
    r_ex1_issue     <= w_ex1_issue_next;
    r_ex1_pipe_ctrl <= w_ex0_pipe_ctrl_next;

    r_ex1_replay_selected     <= w_ex1_replay_selected_next;
    r_ex1_replay_info         <= w_ex1_replay_info_next;

  end // else: !if(!i_reset_n)
end // always_ff @ (posedge i_clk, negedge i_reset_n)

assign w_ex1_rs1_data       = ex0_xpr_regread_rs1.data;
assign w_ex1_vpr_rs_data[0] = vec_phy_rd_if[0].data;
assign w_ex1_vpr_rs_data[1] = vec_phy_rd_if[1].data;


assign w_ex1_tlb_req.valid       = r_ex1_issue.valid; //  & ~r_ex1_issue.paddr_valid;
assign w_ex1_tlb_req.cmd         = r_ex1_pipe_ctrl.op == OP_LOAD ? M_XRD : M_XWR;
assign w_ex1_tlb_req.vaddr       = w_ex1_vaddr;
assign w_ex1_tlb_req.size        = r_ex1_pipe_ctrl.size == SIZE_DW ? 8 :
                                   r_ex1_pipe_ctrl.size == SIZE_W  ? 4 :
                                   r_ex1_pipe_ctrl.size == SIZE_H  ? 2 :
                                   r_ex1_pipe_ctrl.size == SIZE_B  ? 1 : 0;
assign w_ex1_tlb_req.passthrough = 1'b0;
assign w_ex1_addr = r_ex1_replay_selected ? r_ex1_replay_info.paddr : w_ex1_tlb_resp.paddr;

assign w_ex1_ld_except_valid = (r_ex1_pipe_ctrl.op == OP_LOAD)  & w_ex1_tlb_req.valid & (w_ex1_tlb_resp.pf.ld | w_ex1_tlb_resp.ae.ld | w_ex1_tlb_resp.ma.ld);
assign w_ex1_st_except_valid = (r_ex1_pipe_ctrl.op == OP_STORE) & w_ex1_tlb_req.valid & (w_ex1_tlb_resp.pf.st | w_ex1_tlb_resp.ae.st | w_ex1_tlb_resp.ma.st);
assign w_ex1_tlb_except_type = (r_ex1_pipe_ctrl.op == OP_LOAD)  & w_ex1_tlb_resp.ma.ld ? scariv_pkg::LOAD_ADDR_MISALIGN :
                               (r_ex1_pipe_ctrl.op == OP_LOAD)  & w_ex1_tlb_resp.pf.ld ? scariv_pkg::LOAD_PAGE_FAULT    :  // PF<-->AE priority is opposite, TLB generate
                               (r_ex1_pipe_ctrl.op == OP_LOAD)  & w_ex1_tlb_resp.ae.ld ? scariv_pkg::LOAD_ACC_FAULT     :  // PF and AE same time, PF is at first
                               (r_ex1_pipe_ctrl.op == OP_STORE) & w_ex1_tlb_resp.ma.st ? scariv_pkg::STAMO_ADDR_MISALIGN:
                               (r_ex1_pipe_ctrl.op == OP_STORE) & w_ex1_tlb_resp.pf.st ? scariv_pkg::STAMO_PAGE_FAULT   :  // PF and AE same time, PF is at first
                               (r_ex1_pipe_ctrl.op == OP_STORE) & w_ex1_tlb_resp.ae.st ? scariv_pkg::STAMO_ACC_FAULT    :  // PF<-->AE priority is opposite, TLB generate
                               scariv_pkg::SILENT_FLUSH;

scariv_vlsu_address_gen
u_address_gen
  (
   .i_clk     (i_clk),
   .i_reset_n (i_reset_n),

   .i_valid          (r_ex1_issue.valid & ~r_ex1_replay_selected),
   .i_flush_valid    (w_ex0_br_flush | w_commit_flush),
   .i_rs1_base       (w_ex1_rs1_data            ),

   .i_is_last_lmul_index (r_ex1_issue.vec_lmul_index == scariv_vec_pkg::calc_num_req(r_ex1_issue)-1),
   .i_vec_step_index (r_ex1_issue.vec_step_index),
   .o_vaddr          (w_ex1_vaddr               ),
   .o_reg_offset     (w_ex1_reg_offset          ),
   .o_stall          (w_ex1_stall               ),
   .o_req_splitted   (w_ex1_agu_req_splitted        )
   );

assign o_pipe_stall = w_ex1_stall;

// TLB
tlb
  #(.USING_VM(1'b1))
u_tlb
(
 .i_clk    (i_clk),
 .i_reset_n(i_reset_n),

 .i_kill   (1'b0),
 .sfence_if(sfence_if),

 .i_csr_update (csr_info.update),
 .i_status_prv (csr_info.mstatus[`MSTATUS_MPRV] ? csr_info.mstatus[`MSTATUS_MPP] : csr_info.priv),
 .i_csr_status (csr_info.mstatus),
 .i_csr_satp   (csr_info.satp   ),

 .i_tlb_req (w_ex1_tlb_req ),
 .o_tlb_ready(),
 .o_tlb_resp(w_ex1_tlb_resp),

 .o_tlb_update(o_tlb_resolve),
 .o_tlb_resp_miss (),

 .ptw_if (ptw_if)
 );

assign l1d_rd_if.s0_valid         = r_ex1_issue.valid &
                                    (r_ex1_pipe_ctrl.op == OP_LOAD);
assign l1d_rd_if.s0_paddr         = {w_ex1_addr[riscv_pkg::PADDR_W-1:$clog2(DCACHE_DATA_B_W)], {$clog2(DCACHE_DATA_B_W){1'b0}}};
assign l1d_rd_if.s0_high_priority = 1'b0;  // r_ex1_issue.l1d_high_priority;

// ---------------------
// EX2
// ---------------------

assign w_ex1_br_flush = scariv_pkg::is_br_flush_target(r_ex1_issue.cmt_id, r_ex1_issue.grp_id, br_upd_if.cmt_id, br_upd_if.grp_id,
                                                       br_upd_if.dead, br_upd_if.mispredict) & br_upd_if.update & r_ex1_issue.valid;

logic w_ex1_req_splitted;
assign w_ex1_req_splitted = r_ex1_replay_selected ? r_ex1_replay_info.req_splitted[1] : w_ex1_agu_req_splitted;
assign vec_phy_old_wr_if.valid = r_ex1_issue.valid & (r_ex1_issue.wr_old_reg.typ == scariv_pkg::VPR);
assign vec_phy_old_wr_if.rnid  = w_ex1_req_splitted ? r_ex1_issue.wr_reg.rnid : r_ex1_issue.wr_old_reg.rnid;
assign vec_phy_old_wr_if.pos   = r_ex1_issue.vec_step_index;

always_comb begin
  w_ex2_issue_next       = r_ex1_issue;
  w_ex2_issue_next.valid = r_ex1_issue.valid & ~w_commit_flush & ~w_ex1_br_flush;
end

always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_ex2_issue.valid <= 1'b0;
  end else begin
    r_ex2_issue        <= w_ex2_issue_next;
    r_ex2_pipe_ctrl    <= r_ex1_pipe_ctrl;
    r_ex2_addr         <= w_ex1_ld_except_valid | w_ex1_st_except_valid ? w_ex1_vaddr : w_ex1_addr;
    r_ex2_is_uc        <= !w_ex1_tlb_resp.cacheable;

    if (r_ex1_replay_selected) begin
      r_ex2_req_splitted <= r_ex1_replay_info.req_splitted;
      r_ex2_reg_offset   <= r_ex1_replay_info.reg_offset;
    end else begin
      r_ex2_req_splitted[1] <= w_ex1_agu_req_splitted;
      r_ex2_req_splitted[0] <= w_ex1_stall;
      r_ex2_reg_offset      <= w_ex1_reg_offset;
    end

    r_ex2_replay_selected    <= r_ex1_replay_selected;
    r_ex2_replay_haz_1st_req <= r_ex1_replay_info.haz_1st_req;

    r_ex2_except_valid <= w_ex1_ld_except_valid | w_ex1_st_except_valid;
    r_ex2_except_type  <= w_ex1_tlb_except_type;
  end // else: !if(!i_reset_n)
end // always_ff @ (posedge i_clk, negedge i_reset_n)

assign w_ex2_l1d_data   = l1d_rd_if.s1_data;
assign w_ex2_l1d_missed     = r_ex2_issue.valid & l1d_rd_if.s1_miss & ~l1d_rd_if.s1_conflict;
assign w_ex2_l1d_conflicted = r_ex2_issue.valid & l1d_rd_if.s1_conflict;
assign w_ex2_l1d_hazard         = w_ex2_l1d_missed | w_ex2_l1d_conflicted;

assign l1d_missu_if.load              = w_ex2_l1d_missed &
                                        !r_ex2_except_valid & !(l1d_rd_if.s1_conflict | l1d_rd_if.s1_hit);
assign l1d_missu_if.req_payload.paddr = r_ex2_addr;
assign l1d_missu_if.req_payload.is_uc = r_ex2_is_uc;
assign l1d_missu_if.req_payload.way   = l1d_rd_if.s1_hit_way;

assign w_ex2_hazard = w_ex2_l1d_hazard | w_ex2_stq_alloc_neglected;

assign w_ex2_l1d_vec_step_success = w_ex2_is_1st_request ? ~w_ex2_l1d_hazard : ~w_ex2_l1d_hazard & r_ex3_vec_step_success;
assign w_ex2_vec_step_success = w_ex2_is_1st_request ? ~w_ex2_hazard : ~w_ex2_hazard & r_ex3_vec_step_success;

scariv_vec_pkg::vlenbmax_t w_ex2_vl_ew8;
scariv_vec_pkg::vlenbmax_t w_ex2_vl_ew16;
scariv_vec_pkg::vlenbmax_t w_ex2_vl_ew32;
scariv_vec_pkg::vlenbmax_t w_ex2_vl_ew64;
scariv_vec_pkg::dlenb_t    w_ex2_mask;

assign w_ex2_vl_ew8  = r_ex2_issue.vec_step_index * (riscv_vec_conf_pkg::DLEN_W /  8);
assign w_ex2_vl_ew16 = r_ex2_issue.vec_step_index * (riscv_vec_conf_pkg::DLEN_W / 16);
assign w_ex2_vl_ew32 = r_ex2_issue.vec_step_index * (riscv_vec_conf_pkg::DLEN_W / 32);
assign w_ex2_vl_ew64 = r_ex2_issue.vec_step_index * (riscv_vec_conf_pkg::DLEN_W / 64);


function automatic scariv_vec_pkg::vlenbmax_t min(scariv_vec_pkg::vlenbmax_t a, scariv_vec_pkg::vlenbmax_t b);
  return a > b ? b : a;
endfunction // min
function automatic scariv_vec_pkg::vlenbmax_t max(scariv_vec_pkg::vlenbmax_t a, scariv_vec_pkg::vlenbmax_t b);
  return a > b ? a : b;
endfunction // max

always_comb begin
  scariv_vec_pkg::vlenbmax_t w_ex2_temp_vl;

  if (r_ex2_issue.subcat == decoder_inst_cat_pkg::INST_SUBCAT_WHOLE) begin
    case (r_ex2_issue.inst[31:29])
      3'b000 : w_ex2_vl = scariv_vec_pkg::VLENB * 1;
      3'b001 : w_ex2_vl = scariv_vec_pkg::VLENB * 2;
      3'b010 : w_ex2_vl = scariv_vec_pkg::VLENB * 3;
      3'b011 : w_ex2_vl = scariv_vec_pkg::VLENB * 4;
      3'b100 : w_ex2_vl = scariv_vec_pkg::VLENB * 5;
      3'b101 : w_ex2_vl = scariv_vec_pkg::VLENB * 6;
      3'b110 : w_ex2_vl = scariv_vec_pkg::VLENB * 7;
      3'b111 : w_ex2_vl = scariv_vec_pkg::VLENB * 8;
      default : w_ex2_vl = scariv_vec_pkg::VLENB;
    endcase // case (r_ex2_issue.inst[31:29])
  end else begin // if (r_ex2_issue.subcat == decoder_inst_cat_pkg::INST_SUBCAT_WHOLE)
    w_ex2_vl = r_ex2_issue.vlvtype.vl;
  end // else: !if(r_ex2_issue.subcat == decoder_inst_cat_pkg::INST_SUBCAT_WHOLE)


  unique case (r_ex2_issue.vlvtype.vtype.vsew)
    scariv_vec_pkg::EW8 : w_ex2_temp_vl = min(w_ex2_vl > w_ex2_vl_ew8  ? w_ex2_vl - w_ex2_vl_ew8  : 0, riscv_vec_conf_pkg::DLEN_W /  8);
    scariv_vec_pkg::EW16: w_ex2_temp_vl = min(w_ex2_vl > w_ex2_vl_ew16 ? w_ex2_vl - w_ex2_vl_ew16 : 0, riscv_vec_conf_pkg::DLEN_W / 16);
    scariv_vec_pkg::EW32: w_ex2_temp_vl = min(w_ex2_vl > w_ex2_vl_ew32 ? w_ex2_vl - w_ex2_vl_ew32 : 0, riscv_vec_conf_pkg::DLEN_W / 32);
    scariv_vec_pkg::EW64: w_ex2_temp_vl = min(w_ex2_vl > w_ex2_vl_ew64 ? w_ex2_vl - w_ex2_vl_ew64 : 0, riscv_vec_conf_pkg::DLEN_W / 64);
    default             : w_ex2_temp_vl = 'h0;
  endcase // unique case (i_sew)

  if (r_ex2_req_splitted[1]) begin
    // w_ex2_mask = ~(('h1 << (r_ex2_reg_offset << int'(r_ex2_issue.vlvtype.vtype.vsew))) - 1) & ((1 << (w_ex2_temp_vl*1)) - 1);
    unique case (r_ex2_issue.vlvtype.vtype.vsew)
      scariv_vec_pkg::EW8 : w_ex2_mask = ~(('h1 << r_ex2_reg_offset) - 1) & ((1 << (w_ex2_temp_vl*1)) - 1);
      scariv_vec_pkg::EW16: w_ex2_mask = ~(('h1 << r_ex2_reg_offset) - 1) & ((1 << (w_ex2_temp_vl*2)) - 1);
      scariv_vec_pkg::EW32: w_ex2_mask = ~(('h1 << r_ex2_reg_offset) - 1) & ((1 << (w_ex2_temp_vl*4)) - 1);
      scariv_vec_pkg::EW64: w_ex2_mask = ~(('h1 << r_ex2_reg_offset) - 1) & ((1 << (w_ex2_temp_vl*8)) - 1);
      default :             w_ex2_mask = 'h0;
    endcase // unique case (r_ex2_issue.vlvtype.vtype.vsew)
  end else begin
    unique case (r_ex2_issue.vlvtype.vtype.vsew)
      scariv_vec_pkg::EW8 : w_ex2_mask = w_ex2_vl > w_ex2_vl_ew8  + riscv_vec_conf_pkg::DLEN_W /  8 ? {(riscv_vec_conf_pkg::DLEN_W / 8){1'b1}} : (1 << (w_ex2_temp_vl*1)) - 1;
      scariv_vec_pkg::EW16: w_ex2_mask = w_ex2_vl > w_ex2_vl_ew16 + riscv_vec_conf_pkg::DLEN_W / 16 ? {(riscv_vec_conf_pkg::DLEN_W / 8){1'b1}} : (1 << (w_ex2_temp_vl*2)) - 1;
      scariv_vec_pkg::EW32: w_ex2_mask = w_ex2_vl > w_ex2_vl_ew32 + riscv_vec_conf_pkg::DLEN_W / 32 ? {(riscv_vec_conf_pkg::DLEN_W / 8){1'b1}} : (1 << (w_ex2_temp_vl*4)) - 1;
      scariv_vec_pkg::EW64: w_ex2_mask = w_ex2_vl > w_ex2_vl_ew64 + riscv_vec_conf_pkg::DLEN_W / 64 ? {(riscv_vec_conf_pkg::DLEN_W / 8){1'b1}} : (1 << (w_ex2_temp_vl*8)) - 1;
      default             : w_ex2_mask = 'h0;
    endcase // unique case (i_sew)
  end // else: !if(r_ex2_req_splitted[1])

end // always_comb

// ---------------------
// EX3
// ---------------------
assign w_ex2_br_flush = scariv_pkg::is_br_flush_target(r_ex2_issue.cmt_id, r_ex2_issue.grp_id, br_upd_if.cmt_id, br_upd_if.grp_id,
                                                       br_upd_if.dead, br_upd_if.mispredict) & br_upd_if.update & r_ex2_issue.valid;

assign w_ex2_aligned_data = w_ex2_l1d_data >> {r_ex2_addr[$clog2(DCACHE_DATA_B_W)-1: 0], 3'b000} << {r_ex2_reg_offset, 3'b000};

always_comb begin
  w_ex3_issue_next       = r_ex2_issue;
  w_ex3_issue_next.valid = r_ex2_issue.valid & ~w_ex2_l1d_hazard & ~w_ex2_stq_alloc_neglected & ~w_commit_flush & ~w_ex2_br_flush;

  for(int b_idx = 0; b_idx < riscv_vec_conf_pkg::DLEN_W/8; b_idx++) begin
    if (r_ex3_req_splitted[0] & r_ex2_req_splitted[1]) begin
      w_ex3_aligned_data_next[b_idx* 8+: 8] = w_ex2_mask[b_idx] ? w_ex2_aligned_data[b_idx* 8+: 8] : r_ex3_aligned_data    [b_idx* 8+: 8];
    end else begin
      w_ex3_aligned_data_next[b_idx* 8+: 8] = w_ex2_mask[b_idx] ? w_ex2_aligned_data[b_idx* 8+: 8] : vec_phy_old_wr_if.data[b_idx* 8+: 8];
    end
  end
end

assign w_ex2_is_1st_request = (r_ex2_issue.vec_lmul_index == 'h0) & (r_ex2_issue.vec_step_index == 'h0) & ~r_ex2_req_splitted[1] |  // Not splitted 2nd memory requests
                              r_ex2_replay_selected & r_ex2_replay_haz_1st_req;

always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_ex3_issue.valid <= 1'b0;
    r_ex3_vec_step_success <= 1'b1;
  end else begin
    r_ex3_issue     <= w_ex3_issue_next;
    r_ex3_pipe_ctrl <= r_ex2_pipe_ctrl;
    r_ex3_addr      <= r_ex2_addr;
    r_ex3_mis_valid <= w_ex2_l1d_hazard;
    r_ex3_mask      <= w_ex2_mask;

    r_ex3_req_splitted <= r_ex2_req_splitted;
    r_ex3_reg_offset   <= r_ex2_reg_offset;

    r_ex3_aligned_data <= w_ex3_aligned_data_next;

    if (r_ex2_issue.valid) begin
      if (w_ex2_is_1st_request) begin
        r_ex3_vec_step_success <= w_ex3_issue_next.valid;
      end else begin
        r_ex3_vec_step_success <= r_ex3_vec_step_success & w_ex3_issue_next.valid;
      end
    end

    r_ex3_except_valid <= r_ex2_except_valid | w_ex2_stq_alloc_full_flush;
    r_ex3_except_type  <= r_ex2_except_valid ? r_ex2_except_type :
                          scariv_pkg::SELF_KILL_REPLAY;   // When STQ alloc failed, self-kill and kill younger instructions
  end // else: !if(!i_reset_n)
end // always_ff @ (posedge i_clk, negedge i_reset_n)


assign o_done_report.valid                = r_ex3_issue.valid & r_ex3_vec_step_success & ~r_ex3_req_splitted[0] & (r_ex3_issue.vec_lmul_index == scariv_vec_pkg::calc_num_req(r_ex3_issue)-1) & (r_ex3_issue.vec_step_index == scariv_vec_pkg::VEC_STEP_W-1);
assign o_done_report.cmt_id               = r_ex3_issue.cmt_id;
assign o_done_report.grp_id               = r_ex3_issue.grp_id;
assign o_done_report.except_valid         = r_ex3_except_valid;
assign o_done_report.except_type          = r_ex3_except_type;
assign o_done_report.except_tval          = {{(riscv_pkg::XLEN_W-riscv_pkg::VADDR_W){r_ex3_addr[riscv_pkg::VADDR_W-1]}}, r_ex3_addr[riscv_pkg::VADDR_W-1: 0]};
assign o_done_report.cmt_id               = r_ex3_issue.cmt_id;
assign o_done_report.grp_id               = r_ex3_issue.grp_id;

assign o_another_flush_report.valid  = scalar_ldq_haz_check_if.haz_valid;
assign o_another_flush_report.cmt_id = scalar_ldq_haz_check_if.haz_cmt_id;
assign o_another_flush_report.grp_id = scalar_ldq_haz_check_if.haz_grp_id;

assign vec_phy_wr_if.valid   = r_ex3_issue.valid & r_ex3_vec_step_success & r_ex3_issue.wr_reg.valid & ~r_ex3_mis_valid;
assign vec_phy_wr_if.rd_rnid = r_ex3_issue.wr_reg.rnid;
assign vec_phy_wr_if.rd_pos  = r_ex3_issue.vec_step_index;
assign vec_phy_wr_if.rd_data = r_ex3_aligned_data;

assign vec_phy_fwd_if[0].valid   = vec_phy_wr_if.valid & r_ex3_vec_step_success & (r_ex3_issue.vec_lmul_index == scariv_vec_pkg::calc_num_req(r_ex3_issue)-1) & (r_ex3_issue.vec_step_index == scariv_vec_pkg::VEC_STEP_W-1);
assign vec_phy_fwd_if[0].rd_rnid = r_ex3_issue.wr_origin_rnid;

assign vlsu_ldq_req_if.valid  = r_ex2_issue.valid & w_ex2_l1d_vec_step_success & r_ex2_pipe_ctrl.op == OP_LOAD;
assign vlsu_ldq_req_if.paddr  = r_ex2_addr;
assign vlsu_ldq_req_if.cmt_id = r_ex2_issue.cmt_id;
assign vlsu_ldq_req_if.grp_id = r_ex2_issue.grp_id;

assign vlsu_stq_req_if.valid  = r_ex2_issue.valid & w_ex2_l1d_vec_step_success & r_ex2_pipe_ctrl.op == OP_STORE;
assign vlsu_stq_req_if.paddr  = r_ex2_addr;
assign vlsu_stq_req_if.cmt_id = r_ex2_issue.cmt_id;
assign vlsu_stq_req_if.grp_id = r_ex2_issue.grp_id;
assign vlsu_stq_req_if.vs3_phy_idx = r_ex2_issue.rd_regs[2].rnid;
assign vlsu_stq_req_if.vs3_pos     = r_ex2_issue.vec_step_index;
assign vlsu_stq_req_if.strb        = w_ex2_mask;

assign scalar_ldq_haz_check_if.valid  = r_ex2_issue.valid & w_ex2_l1d_vec_step_success & r_ex2_pipe_ctrl.op == OP_STORE;
assign scalar_ldq_haz_check_if.paddr  = r_ex2_addr;
assign scalar_ldq_haz_check_if.cmt_id = r_ex2_issue.cmt_id;
assign scalar_ldq_haz_check_if.grp_id = r_ex2_issue.grp_id;

assign w_ex2_stq_alloc_neglected  = vlsu_stq_req_if.valid & vlsu_stq_req_if.resp == scariv_vec_pkg::VSTQ_RESP_FULL_WAIT;
assign w_ex2_stq_alloc_full_flush = vlsu_stq_req_if.valid & vlsu_stq_req_if.resp == scariv_vec_pkg::VSTQ_RESP_FULL_FLUSH;

// --------------------------
// Interface to Replay Queue
// --------------------------
assign lsu_pipe_haz_if.valid                  = r_ex2_issue.valid & ~r_ex2_except_valid & ~i_replay_queue_full & ~w_ex2_vec_step_success & ~w_commit_flush & ~w_ex2_br_flush;
assign lsu_pipe_haz_if.cmt_id                 = r_ex2_issue.cmt_id;
assign lsu_pipe_haz_if.grp_id                 = r_ex2_issue.grp_id;
assign lsu_pipe_haz_if.payload.inst           = r_ex2_issue.inst;
assign lsu_pipe_haz_if.payload.vlvtype        = r_ex2_issue.vlvtype;
assign lsu_pipe_haz_if.payload.cat            = r_ex2_issue.cat;
assign lsu_pipe_haz_if.payload.subcat         = r_ex2_issue.subcat;
assign lsu_pipe_haz_if.payload.oldest_valid   = 1'b0;
assign lsu_pipe_haz_if.payload.hazard_typ     = l1d_rd_if.s1_conflict ? EX2_HAZ_L1D_CONFLICT   :
                                                l1d_rd_if.s1_miss     ? EX2_HAZ_MISSU_ASSIGNED :
                                                EX2_HAZ_VSTQ_FULL_WAIT;
assign lsu_pipe_haz_if.payload.rd_regs        = r_ex2_issue.rd_regs;
assign lsu_pipe_haz_if.payload.wr_reg         = r_ex2_issue.wr_reg;
assign lsu_pipe_haz_if.payload.wr_old_reg     = r_ex2_issue.wr_old_reg;
assign lsu_pipe_haz_if.payload.wr_origin_rnid = r_ex2_issue.wr_origin_rnid;
assign lsu_pipe_haz_if.payload.is_uc          = 1'b0;
assign lsu_pipe_haz_if.payload.hazard_index   = l1d_missu_if.resp_payload.missu_index_oh;
assign lsu_pipe_haz_if.payload.vec_step_index = r_ex2_issue.vec_step_index;
assign lsu_pipe_haz_if.payload.vec_lmul_index = r_ex2_issue.vec_lmul_index;
assign lsu_pipe_haz_if.payload.replay_info.paddr        = r_ex2_addr;
assign lsu_pipe_haz_if.payload.replay_info.haz_1st_req  = ((r_ex2_issue.vec_lmul_index == 'h0) & (r_ex2_issue.vec_step_index == 'h0)) | r_ex2_replay_selected & r_ex2_replay_haz_1st_req ? w_ex2_hazard :
                                                          r_ex3_vec_step_success & ~w_ex2_vec_step_success;
assign lsu_pipe_haz_if.payload.replay_info.req_splitted = r_ex2_req_splitted;
assign lsu_pipe_haz_if.payload.replay_info.reg_offset   = r_ex2_reg_offset;



endmodule // scariv_vec_lsu_pipe
