// ------------------------------------------------------------------------
// NAME : Resource Allocator
// TYPE : module
// ------------------------------------------------------------------------
// Backend module resource manager
// ------------------------------------------------------------------------
// Controls number of remaining entries in backend modules
// Input : Distpached instruction
// Output: Resource information
// ------------------------------------------------------------------------

module scariv_resource_alloc
  import scariv_pkg::*;
  (
   input logic i_clk,
   input logic i_reset_n,

   disp_if.watch iq_disp,

   // -------------------------------
   // Credit Return Update interface
   // -------------------------------
   cre_ret_if.master rob_cre_ret_if,
   cre_ret_if.master alu_cre_ret_if[scariv_conf_pkg::ALU_INST_NUM],
   cre_ret_if.master ldq_cre_ret_if,
   cre_ret_if.master stq_cre_ret_if,
   cre_ret_if.master csu_cre_ret_if,
   cre_ret_if.master bru_cre_ret_if,
   cre_ret_if.master fpu_cre_ret_if[scariv_conf_pkg::FPU_INST_NUM],

   // Branch Tag Update Signal
   br_upd_if.slave                br_upd_if,

   input scariv_pkg::commit_blk_t   i_commit,
   // Branch Tag Update Signal
   cmt_brtag_if.slave             cmt_brtag_if,

   output logic o_resource_ok,

   output brtag_t o_brtag  [scariv_conf_pkg::DISP_SIZE],
   output brmask_t         o_brmask [scariv_conf_pkg::DISP_SIZE]
   );

logic                                     w_commit_flush;
logic                                     w_br_flush;
logic                                     w_flush_valid;
logic                                     w_iq_fire;

logic                                               w_rob_no_credits_remained;
logic [scariv_conf_pkg::ALU_INST_NUM-1: 0]            w_alu_no_credits_remained;
logic [scariv_conf_pkg::LSU_INST_NUM-1: 0]            w_lsu_no_credits_remained;
logic                                               w_ldq_no_credits_remained;
logic                                               w_stq_no_credits_remained;
logic                                               w_csu_no_credits_remained;
logic                                               w_bru_no_credits_remained;
logic [scariv_conf_pkg::FPU_INST_NUM-1: 0]            w_fpu_no_credits_remained;


assign o_resource_ok = !w_rob_no_credits_remained &
                       !(|w_alu_no_credits_remained) &
                       !(|w_lsu_no_credits_remained) &
                       !w_ldq_no_credits_remained &
                       !w_stq_no_credits_remained &
                       !w_csu_no_credits_remained &
                       !w_bru_no_credits_remained &
                       !(|w_fpu_no_credits_remained);


assign w_commit_flush = scariv_pkg::is_flushed_commit(i_commit);
assign w_br_flush     = br_upd_if.update & ~br_upd_if.dead & br_upd_if.mispredict;
assign w_flush_valid  = w_commit_flush | w_br_flush;

assign w_iq_fire = ~w_flush_valid & iq_disp.valid & iq_disp.ready;

scariv_credit_return_master
  #(.MAX_CREDITS(scariv_conf_pkg::CMT_ENTRY_SIZE))
u_rob_credit_return
(
 .i_clk(i_clk),
 .i_reset_n(i_reset_n),

 .i_get_credit(~w_flush_valid & w_iq_fire),
 .i_credit_val('h1),

 .o_credits(),
 .o_no_credits(w_rob_no_credits_remained),

 .cre_ret_if (rob_cre_ret_if)
);


generate for (genvar a_idx = 0; a_idx < scariv_conf_pkg::ALU_INST_NUM; a_idx++) begin : alu_cre_ret_loop
  logic w_inst_arith_valid;
  assign w_inst_arith_valid = iq_disp.valid & |iq_disp.resource_cnt.alu_inst_cnt[a_idx];
  logic [$clog2(scariv_conf_pkg::RV_ALU_ENTRY_SIZE):0] w_alu_inst_cnt;
  /* verilator lint_off WIDTH */
  assign w_alu_inst_cnt = iq_disp.resource_cnt.alu_inst_cnt[a_idx];

  scariv_credit_return_master
    #(.MAX_CREDITS(scariv_conf_pkg::RV_ALU_ENTRY_SIZE))
  u_alu_credit_return
  (
   .i_clk(i_clk),
   .i_reset_n(i_reset_n),

   .i_get_credit(~w_flush_valid & w_inst_arith_valid & iq_disp.ready),
   .i_credit_val(w_alu_inst_cnt),

   .o_credits(),
   .o_no_credits(w_alu_no_credits_remained[a_idx]),

   .cre_ret_if (alu_cre_ret_if[a_idx])
   );
end // block: alu_cre_ret_loop
endgenerate

generate for (genvar l_idx = 0; l_idx < scariv_conf_pkg::LSU_INST_NUM; l_idx++) begin : lsu_cre_ret_loop
//   logic w_inst_lsu_valid;
//   assign w_inst_lsu_valid = iq_disp.valid & |iq_disp.resource_cnt.lsu_inst_cnt[l_idx];
//   logic [$clog2(scariv_lsu_pkg::MEM_Q_SIZE):0] w_lsu_inst_cnt;
//   assign w_lsu_inst_cnt = iq_disp.resource_cnt.lsu_inst_cnt[l_idx];
//
//   scariv_credit_return_master
//     #(.MAX_CREDITS(scariv_lsu_pkg::MEM_Q_SIZE))
//   u_lsu_credit_return
//   (
//    .i_clk(i_clk),
//    .i_reset_n(i_reset_n),
//
//    .i_get_credit(~w_flush_valid & w_inst_lsu_valid & iq_disp.ready),
//    .i_credit_val(w_lsu_inst_cnt),
//
//    .o_credits(),
//    .o_no_credits(w_lsu_no_credits_remained[l_idx]),
//
//    .cre_ret_if (lsu_cre_ret_if[l_idx])
//    );
  assign w_lsu_no_credits_remained[l_idx] = 1'b0;
end
endgenerate


logic   w_inst_ld_valid;
assign w_inst_ld_valid = iq_disp.valid & |iq_disp.resource_cnt.ld_inst_cnt;
scariv_credit_return_master
  #(.MAX_CREDITS(scariv_conf_pkg::LDQ_SIZE))
u_ldq_credit_return
(
 .i_clk(i_clk),
 .i_reset_n(i_reset_n),

 .i_get_credit(~w_flush_valid & w_inst_ld_valid & iq_disp.ready),
 .i_credit_val(iq_disp.resource_cnt.ld_inst_cnt),

 .o_credits(),
 .o_no_credits(w_ldq_no_credits_remained),

 .cre_ret_if (ldq_cre_ret_if)
);


logic   w_inst_st_valid;
assign w_inst_st_valid = iq_disp.valid & |iq_disp.resource_cnt.st_inst_cnt;
scariv_credit_return_master
  #(.MAX_CREDITS(scariv_conf_pkg::STQ_SIZE))
u_stq_credit_return
(
 .i_clk(i_clk),
 .i_reset_n(i_reset_n),

 .i_get_credit(~w_flush_valid & w_inst_st_valid & iq_disp.ready),
 .i_credit_val(iq_disp.resource_cnt.st_inst_cnt),

 .o_credits    (),
 .o_no_credits (w_stq_no_credits_remained),

 .cre_ret_if (stq_cre_ret_if)
);


logic   w_inst_csu_valid;
assign w_inst_csu_valid = iq_disp.valid & |iq_disp.resource_cnt.csu_inst_cnt;
logic [$clog2(scariv_conf_pkg::RV_CSU_ENTRY_SIZE):0] w_inst_csu_cnt;
assign w_inst_csu_cnt = iq_disp.resource_cnt.csu_inst_cnt;
scariv_credit_return_master
  #(.MAX_CREDITS(scariv_conf_pkg::RV_CSU_ENTRY_SIZE))
u_csu_credit_return
(
 .i_clk(i_clk),
 .i_reset_n(i_reset_n),

 .i_get_credit(~w_flush_valid & w_inst_csu_valid & iq_disp.ready),
 .i_credit_val(w_inst_csu_cnt),

 .o_credits(),
 .o_no_credits(w_csu_no_credits_remained),

 .cre_ret_if (csu_cre_ret_if)
);

logic   w_inst_bru_valid;
assign w_inst_bru_valid = iq_disp.valid & |iq_disp.resource_cnt.bru_inst_cnt;
logic [$clog2(scariv_conf_pkg::RV_BRU_ENTRY_SIZE):0] w_bru_inst_cnt;
assign w_bru_inst_cnt = iq_disp.resource_cnt.bru_inst_cnt;
scariv_credit_return_master
  #(.MAX_CREDITS(scariv_conf_pkg::RV_BRU_ENTRY_SIZE))
u_bru_credit_return
(
 .i_clk(i_clk),
 .i_reset_n(i_reset_n),

 .i_get_credit(~w_flush_valid & w_inst_bru_valid & iq_disp.ready),
 .i_credit_val(w_bru_inst_cnt),

 .o_credits(),
 .o_no_credits(w_bru_no_credits_remained),

 .cre_ret_if (bru_cre_ret_if)
);


generate for (genvar f_idx = 0; f_idx < scariv_conf_pkg::FPU_INST_NUM; f_idx++) begin : fpu_cre_ret_loop
  logic w_inst_fpu_valid;
  assign w_inst_fpu_valid = iq_disp.valid & |iq_disp.resource_cnt.fpu_inst_cnt[f_idx];
  logic [$clog2(scariv_conf_pkg::RV_FPU_ENTRY_SIZE):0] w_fpu_inst_cnt;
  /* verilator lint_off WIDTH */
  assign w_fpu_inst_cnt = iq_disp.resource_cnt.fpu_inst_cnt[f_idx];

  scariv_credit_return_master
    #(.MAX_CREDITS(scariv_conf_pkg::RV_FPU_ENTRY_SIZE))
  u_fpu_credit_return
  (
   .i_clk(i_clk),
   .i_reset_n(i_reset_n),

   .i_get_credit(~w_flush_valid & w_inst_fpu_valid & iq_disp.ready),
   .i_credit_val(w_fpu_inst_cnt),

   .o_credits(),
   .o_no_credits(w_fpu_no_credits_remained[f_idx]),

   .cre_ret_if (fpu_cre_ret_if[f_idx])
   );
end // block: fpu_cre_ret_loop
endgenerate


brmask_t    r_br_mask_valid;
brmask_t    w_br_mask_valid_next;
/* verilator lint_off UNOPTFLAT */
brmask_t    w_br_mask_temp_valid[scariv_conf_pkg::DISP_SIZE+1];

brtag_t w_br_tag_temp_idx[scariv_conf_pkg::DISP_SIZE+1];
brtag_t r_br_tag_current_idx;

generate for (genvar b_idx = 0; b_idx < scariv_conf_pkg::RV_BRU_ENTRY_SIZE; b_idx++) begin : branch_loop
  always_comb begin
    w_br_mask_valid_next[b_idx] = r_br_mask_valid[b_idx];
    // for (int d_idx = 0; d_idx < scariv_conf_pkg::DISP_SIZE; d_idx++) begin : branch_disp_loop
    //   if (cmt_brtag_if.commit & cmt_brtag_if.is_br_inst[d_idx] & cmt_brtag_if.brtag[d_idx] == b_idx) begin
    //     w_br_mask_valid_next[b_idx] = 1'b0;
    //   end
    // end
    if (br_upd_if.update & (br_upd_if.brtag == b_idx)) begin
      w_br_mask_valid_next[b_idx] = 1'b0;
    end
    if (br_upd_if.update & br_upd_if.mispredict & ~br_upd_if.dead & ~br_upd_if.br_mask[b_idx]) begin
      w_br_mask_valid_next[b_idx] = 1'b0;
    end
  end
end
endgenerate


assign w_br_mask_temp_valid[0] = w_br_mask_valid_next;
assign w_br_tag_temp_idx[0] = r_br_tag_current_idx;

generate for (genvar d_idx = 0; d_idx < scariv_conf_pkg::DISP_SIZE; d_idx++) begin : branch_disp_loop

  logic w_is_br_inst;
  assign w_is_br_inst = w_iq_fire &
                        iq_disp.inst[d_idx].valid & (iq_disp.inst[d_idx].cat == decoder_inst_cat_pkg::INST_CAT_BR);

  assign w_br_mask_temp_valid[d_idx+1] = !w_is_br_inst ? w_br_mask_temp_valid[d_idx] : w_br_mask_temp_valid[d_idx] | (1 << w_br_tag_temp_idx[d_idx]);
  assign w_br_tag_temp_idx   [d_idx+1] = !w_is_br_inst ? w_br_tag_temp_idx   [d_idx] : w_br_tag_temp_idx[d_idx] + 'h1;

  assign o_brtag[d_idx]  = w_br_tag_temp_idx   [d_idx];
  assign o_brmask[d_idx] = w_br_mask_temp_valid[d_idx];
end // block: branch_loop
endgenerate


always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_br_mask_valid     <= 'h0;
    r_br_tag_current_idx <= 'h0;
  end else begin
    if (w_commit_flush) begin
      r_br_mask_valid <= 'h0;
    end else begin
      r_br_mask_valid      <= w_br_mask_temp_valid[scariv_conf_pkg::DISP_SIZE];
      r_br_tag_current_idx <= w_br_tag_temp_idx[scariv_conf_pkg::DISP_SIZE];
    end
  end
end


endmodule // scariv_resource_alloc
