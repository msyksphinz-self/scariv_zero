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

   scariv_front_if.watch ibuf_front_if,

   // -------------------------------
   // Credit Return Update interface
   // -------------------------------
   cre_ret_if.master rob_cre_ret_if,
   cre_ret_if.master alu_cre_ret_if[scariv_conf_pkg::ALU_INST_NUM],
   cre_ret_if.master lsu_cre_ret_if[scariv_conf_pkg::LSU_INST_NUM],
   cre_ret_if.master ldq_cre_ret_if,
   cre_ret_if.master stq_cre_ret_if,
   cre_ret_if.master csu_cre_ret_if,
   cre_ret_if.master bru_cre_ret_if,
   cre_ret_if.master fpu_cre_ret_if[scariv_conf_pkg::FPU_INST_NUM],

   // Branch Tag Update Signal
   br_upd_if.slave                br_upd_if,

   commit_if.monitor   commit_if,

   output logic o_resource_ok,

   output brtag_t o_brtag  [scariv_conf_pkg::DISP_SIZE],

   brtag_if.slave  brtag_if
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


assign w_commit_flush = commit_if.is_flushed_commit();
assign w_br_flush     = br_upd_if.update & ~br_upd_if.dead & br_upd_if.mispredict;
assign w_flush_valid  = w_commit_flush | w_br_flush;

assign w_iq_fire = ~w_flush_valid & ibuf_front_if.valid & ibuf_front_if.ready;

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
  assign w_inst_arith_valid = ibuf_front_if.valid & |ibuf_front_if.payload.resource_cnt.alu_inst_cnt[a_idx];
  logic [$clog2(scariv_conf_pkg::RV_ALU_ENTRY_SIZE):0] w_alu_inst_cnt;
  /* verilator lint_off WIDTH */
  assign w_alu_inst_cnt = ibuf_front_if.payload.resource_cnt.alu_inst_cnt[a_idx];

  scariv_credit_return_master
    #(.MAX_CREDITS(scariv_conf_pkg::RV_ALU_ENTRY_SIZE))
  u_alu_credit_return
  (
   .i_clk(i_clk),
   .i_reset_n(i_reset_n),

   .i_get_credit(~w_flush_valid & w_inst_arith_valid & ibuf_front_if.ready),
   .i_credit_val(w_alu_inst_cnt),

   .o_credits(),
   .o_no_credits(w_alu_no_credits_remained[a_idx]),

   .cre_ret_if (alu_cre_ret_if[a_idx])
   );
end // block: alu_cre_ret_loop
endgenerate

localparam LSU_ISS_ENTRY_SIZE = scariv_conf_pkg::RV_LSU_ENTRY_SIZE / scariv_conf_pkg::LSU_INST_NUM;

generate for (genvar l_idx = 0; l_idx < scariv_conf_pkg::LSU_INST_NUM; l_idx++) begin : lsu_cre_ret_loop
  logic w_inst_lsu_valid;
  assign w_inst_lsu_valid = ibuf_front_if.valid & |ibuf_front_if.payload.resource_cnt.lsu_inst_cnt[l_idx];
  logic [$clog2(LSU_ISS_ENTRY_SIZE):0] w_lsu_inst_cnt;
  assign w_lsu_inst_cnt = ibuf_front_if.payload.resource_cnt.lsu_inst_cnt[l_idx];

  scariv_credit_return_master
    #(.MAX_CREDITS(LSU_ISS_ENTRY_SIZE))
  u_lsu_credit_return
  (
   .i_clk(i_clk),
   .i_reset_n(i_reset_n),

   .i_get_credit(~w_flush_valid & w_inst_lsu_valid & ibuf_front_if.ready),
   .i_credit_val(w_lsu_inst_cnt),

   .o_credits(),
   .o_no_credits(w_lsu_no_credits_remained[l_idx]),

  .cre_ret_if (lsu_cre_ret_if[l_idx])
  );
end
endgenerate


logic   w_inst_ld_valid;
assign w_inst_ld_valid = ibuf_front_if.valid & |ibuf_front_if.payload.resource_cnt.ld_inst_cnt;
scariv_credit_return_master
  #(.MAX_CREDITS(scariv_conf_pkg::LDQ_SIZE))
u_ldq_credit_return
(
 .i_clk(i_clk),
 .i_reset_n(i_reset_n),

 .i_get_credit(~w_flush_valid & w_inst_ld_valid & ibuf_front_if.ready),
 .i_credit_val(ibuf_front_if.payload.resource_cnt.ld_inst_cnt),

 .o_credits(),
 .o_no_credits(w_ldq_no_credits_remained),

 .cre_ret_if (ldq_cre_ret_if)
);


logic   w_inst_st_valid;
assign w_inst_st_valid = ibuf_front_if.valid & |ibuf_front_if.payload.resource_cnt.st_inst_cnt;
scariv_credit_return_master
  #(.MAX_CREDITS(scariv_conf_pkg::STQ_SIZE))
u_stq_credit_return
(
 .i_clk(i_clk),
 .i_reset_n(i_reset_n),

 .i_get_credit(~w_flush_valid & w_inst_st_valid & ibuf_front_if.ready),
 .i_credit_val(ibuf_front_if.payload.resource_cnt.st_inst_cnt),

 .o_credits    (),
 .o_no_credits (w_stq_no_credits_remained),

 .cre_ret_if (stq_cre_ret_if)
);


logic   w_inst_csu_valid;
assign w_inst_csu_valid = ibuf_front_if.valid & |ibuf_front_if.payload.resource_cnt.csu_inst_cnt;
logic [$clog2(scariv_conf_pkg::RV_CSU_ENTRY_SIZE):0] w_inst_csu_cnt;
assign w_inst_csu_cnt = ibuf_front_if.payload.resource_cnt.csu_inst_cnt;
scariv_credit_return_master
  #(.MAX_CREDITS(scariv_conf_pkg::RV_CSU_ENTRY_SIZE))
u_csu_credit_return
(
 .i_clk(i_clk),
 .i_reset_n(i_reset_n),

 .i_get_credit(~w_flush_valid & w_inst_csu_valid & ibuf_front_if.ready),
 .i_credit_val(w_inst_csu_cnt),

 .o_credits(),
 .o_no_credits(w_csu_no_credits_remained),

 .cre_ret_if (csu_cre_ret_if)
);

logic   w_inst_bru_valid;
assign w_inst_bru_valid = ibuf_front_if.valid & |ibuf_front_if.payload.resource_cnt.bru_inst_cnt;
logic [$clog2(scariv_conf_pkg::RV_BRU_ENTRY_SIZE):0] w_bru_inst_cnt;
assign w_bru_inst_cnt = ibuf_front_if.payload.resource_cnt.bru_inst_cnt;
scariv_credit_return_master
  #(.MAX_CREDITS(scariv_conf_pkg::RV_BRU_ENTRY_SIZE))
u_bru_credit_return
(
 .i_clk(i_clk),
 .i_reset_n(i_reset_n),

 .i_get_credit(~w_flush_valid & w_inst_bru_valid & ibuf_front_if.ready),
 .i_credit_val(w_bru_inst_cnt),

 .o_credits(),
 .o_no_credits(w_bru_no_credits_remained),

 .cre_ret_if (bru_cre_ret_if)
);


generate for (genvar f_idx = 0; f_idx < scariv_conf_pkg::FPU_INST_NUM; f_idx++) begin : fpu_cre_ret_loop
  logic w_inst_fpu_valid;
  assign w_inst_fpu_valid = ibuf_front_if.valid & |ibuf_front_if.payload.resource_cnt.fpu_inst_cnt[f_idx];
  logic [$clog2(scariv_conf_pkg::RV_FPU_ENTRY_SIZE):0] w_fpu_inst_cnt;
  /* verilator lint_off WIDTH */
  assign w_fpu_inst_cnt = ibuf_front_if.payload.resource_cnt.fpu_inst_cnt[f_idx];

  scariv_credit_return_master
    #(.MAX_CREDITS(scariv_conf_pkg::RV_FPU_ENTRY_SIZE))
  u_fpu_credit_return
  (
   .i_clk(i_clk),
   .i_reset_n(i_reset_n),

   .i_get_credit(~w_flush_valid & w_inst_fpu_valid & ibuf_front_if.ready),
   .i_credit_val(w_fpu_inst_cnt),

   .o_credits(),
   .o_no_credits(w_fpu_no_credits_remained[f_idx]),

   .cre_ret_if (fpu_cre_ret_if[f_idx])
   );
end // block: fpu_cre_ret_loop
endgenerate


logic [$clog2(scariv_conf_pkg::RV_BRU_ENTRY_SIZE)-1: 0] w_brtag_freelist_pop_id[scariv_conf_pkg::DISP_SIZE];
brtag_t r_br_tag_current_idx;
scariv_brtag_freelist
  #(.SIZE  (scariv_conf_pkg::RV_BRU_ENTRY_SIZE),
    .WIDTH ($clog2(scariv_conf_pkg::RV_BRU_ENTRY_SIZE)),
    .PORTS (scariv_conf_pkg::DISP_SIZE)
    )
u_brtag_freelist
(
  .i_clk    (i_clk),
  .i_reset_n(i_reset_n),

  .i_push    (brtag_if.valid),
  .i_push_id (brtag_if.brtag),
  .i_pop     ({scariv_conf_pkg::DISP_SIZE{w_iq_fire}} & ibuf_front_if.payload.resource_cnt.bru_inst_valid),
  .o_pop_id  (w_brtag_freelist_pop_id),
  .o_is_empty()
);


generate for (genvar d_idx = 0; d_idx < scariv_conf_pkg::DISP_SIZE; d_idx++) begin : branch_disp_loop
  assign o_brtag[d_idx]  = w_brtag_freelist_pop_id[d_idx];
end endgenerate

endmodule // scariv_resource_alloc
