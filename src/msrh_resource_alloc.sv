module msrh_resource_alloc
  import msrh_pkg::*;
  (
   input logic i_clk,
   input logic i_reset_n,

   disp_if.slave iq_disp,

   // -------------------------------
   // Credit Return Update interface
   // -------------------------------
   cre_ret_if.master rob_cre_ret_if,
   cre_ret_if.master alu_cre_ret_if[msrh_conf_pkg::ALU_INST_NUM],
   cre_ret_if.master ldq_cre_ret_if,
   cre_ret_if.master stq_cre_ret_if,
   cre_ret_if.master csu_cre_ret_if,
   cre_ret_if.master bru_cre_ret_if,

   input msrh_pkg::commit_blk_t   i_commit,

   output logic o_resource_ok
   );

logic           w_flush_valid;
logic           w_iq_fire;

logic                                               w_rob_no_credits_remained;
logic [msrh_conf_pkg::ALU_INST_NUM-1: 0]            w_alu_no_credits_remained;
logic [msrh_conf_pkg::LSU_INST_NUM-1: 0]            w_lsu_no_credits_remained;
logic                                               w_ldq_no_credits_remained;
logic                                               w_stq_no_credits_remained;
logic                                               w_csu_no_credits_remained;
logic                                               w_bru_no_credits_remained;

assign o_resource_ok = !w_rob_no_credits_remained &
                       !(|w_alu_no_credits_remained) &
                       !(|w_lsu_no_credits_remained) &
                       !w_ldq_no_credits_remained &
                       !w_stq_no_credits_remained &
                       !w_csu_no_credits_remained &
                       !w_bru_no_credits_remained;


assign w_flush_valid = i_commit.commit & i_commit.flush_valid & !i_commit.all_dead;
assign w_iq_fire = ~w_flush_valid & iq_disp.valid & iq_disp.ready;

msrh_credit_return_master
  #(.MAX_CREDITS(msrh_conf_pkg::CMT_ENTRY_SIZE))
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


generate for (genvar a_idx = 0; a_idx < msrh_conf_pkg::ALU_INST_NUM; a_idx++) begin : alu_cre_ret_loop
  logic w_inst_arith_valid;
  assign w_inst_arith_valid = iq_disp.valid & |iq_disp.resource_cnt.alu_inst_cnt[a_idx];
  logic [$clog2(msrh_conf_pkg::RV_ALU_ENTRY_SIZE):0] w_alu_inst_cnt;
  /* verilator lint_off WIDTH */
  assign w_alu_inst_cnt = iq_disp.resource_cnt.alu_inst_cnt[a_idx];

  msrh_credit_return_master
    #(.MAX_CREDITS(msrh_conf_pkg::RV_ALU_ENTRY_SIZE))
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

generate for (genvar l_idx = 0; l_idx < msrh_conf_pkg::LSU_INST_NUM; l_idx++) begin : lsu_cre_ret_loop
//   logic w_inst_lsu_valid;
//   assign w_inst_lsu_valid = iq_disp.valid & |iq_disp.resource_cnt.lsu_inst_cnt[l_idx];
//   logic [$clog2(msrh_lsu_pkg::MEM_Q_SIZE):0] w_lsu_inst_cnt;
//   assign w_lsu_inst_cnt = iq_disp.resource_cnt.lsu_inst_cnt[l_idx];
//
//   msrh_credit_return_master
//     #(.MAX_CREDITS(msrh_lsu_pkg::MEM_Q_SIZE))
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
msrh_credit_return_master
  #(.MAX_CREDITS(msrh_conf_pkg::LDQ_SIZE))
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
msrh_credit_return_master
  #(.MAX_CREDITS(msrh_conf_pkg::STQ_SIZE))
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
logic [$clog2(msrh_conf_pkg::RV_CSU_ENTRY_SIZE):0] w_inst_csu_cnt;
assign w_inst_csu_cnt = iq_disp.resource_cnt.csu_inst_cnt;
msrh_credit_return_master
  #(.MAX_CREDITS(msrh_conf_pkg::RV_CSU_ENTRY_SIZE))
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
logic [$clog2(msrh_conf_pkg::RV_BRU_ENTRY_SIZE):0] w_bru_inst_cnt;
assign w_bru_inst_cnt = iq_disp.resource_cnt.bru_inst_cnt;
msrh_credit_return_master
  #(.MAX_CREDITS(msrh_conf_pkg::RV_BRU_ENTRY_SIZE))
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

endmodule // msrh_resource_alloc
