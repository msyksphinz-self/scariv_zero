// ------------------------------------------------------------------------
// NAME : scariv_muldiv_pipe
// TYPE : module
// ------------------------------------------------------------------------
// MulDiv Pipeline
// ------------------------------------------------------------------------
// ------------------------------------------------------------------------

module scariv_muldiv_pipe
  import decoder_alu_ctrl_pkg::*;
#(
  parameter RV_ENTRY_SIZE = 32,
  parameter MUL_UNROLL = 8
  )
(
 input logic                           i_clk,
 input logic                           i_reset_n,

 // Commit notification
 input scariv_pkg::commit_blk_t          i_commit,
 br_upd_if.slave                       br_upd_if,

 input logic                           i_valid,
 input                                 op_t i_op,

 input scariv_pkg::cmt_id_t              i_cmt_id,
 input scariv_pkg::grp_id_t              i_grp_id,
 input scariv_pkg::brmask_t              i_br_mask,
 input scariv_pkg::rnid_t                i_rd_rnid,
 input scariv_pkg::reg_t                 i_rd_type,
 input logic [RV_ENTRY_SIZE-1: 0]      i_index_oh,

 input riscv_pkg::xlen_t  i_rs1,
 input riscv_pkg::xlen_t  i_rs2,

 output logic                          o_stall,

 output logic                          o_valid,
 output scariv_pkg::cmt_id_t           o_cmt_id,
 output scariv_pkg::grp_id_t           o_grp_id,
 output riscv_pkg::xlen_t              o_res,

 output scariv_pkg::rnid_t             o_rd_rnid,
 output scariv_pkg::reg_t              o_rd_type,
 output logic [RV_ENTRY_SIZE-1: 0]     o_index_oh
 );


logic [riscv_pkg::XLEN_W: 0]           w_op1;
logic [riscv_pkg::XLEN_W: 0]           w_op2;

logic                                  w_is_mul;
logic                                  w_is_mulw_64;
`ifdef RV64
assign w_is_mulw_64 = (i_op == OP_MULW);
`else // RV64
assign w_is_mulw_64 = 1'b0;
`endif // RV64
assign w_is_mul = (i_op == OP_SMUL) | (i_op == OP_MULH) | (i_op == OP_MULHU) | (i_op == OP_MULHSU) | w_is_mulw_64;

assign w_op1 = (i_op == OP_SMUL || i_op == OP_MULH || i_op == OP_MULHSU || w_is_mulw_64) ? {i_rs1[riscv_pkg::XLEN_W-1], i_rs1} : {1'b0, i_rs1};
assign w_op2 = (i_op == OP_SMUL || i_op == OP_MULH                      || w_is_mulw_64) ? {i_rs2[riscv_pkg::XLEN_W-1], i_rs2} : {1'b0, i_rs2};



parameter MUL_STEP = (riscv_pkg::XLEN_W + MUL_UNROLL - 1) / MUL_UNROLL;
logic [MUL_STEP: 0]                    r_mul_valid_pipe;
logic [riscv_pkg::XLEN_W: 0]           multiplicand_pipe [MUL_STEP: 1];
logic [riscv_pkg::XLEN_W: 0]           multiplier_pipe   [MUL_STEP: 1];
logic [riscv_pkg::XLEN_W*2:0]          prod_pipe         [MUL_STEP: 1];
logic                                  neg_out_pipe      [MUL_STEP: 1];
op_t  op_pipe                                            [MUL_STEP: 1];
scariv_pkg::cmt_id_t                     r_cmt_id          [MUL_STEP: 1];
scariv_pkg::grp_id_t                     r_grp_id          [MUL_STEP: 1];
scariv_pkg::brmask_t                     r_br_mask         [MUL_STEP: 1];

scariv_pkg::rnid_t                          r_mul_rd_rnid [MUL_STEP: 1];
scariv_pkg::reg_t                           r_mul_rd_type [MUL_STEP: 1];
scariv_pkg::cmt_id_t                        r_mul_cmt_id  [MUL_STEP: 1];
scariv_pkg::grp_id_t                        r_mul_grp_id  [MUL_STEP: 1];
logic [RV_ENTRY_SIZE-1: 0]                  r_mul_index_oh[MUL_STEP: 1];

logic         w_div_ready;
logic         w_div_valid;
logic [63: 0] w_div_res;

scariv_pkg::cmt_id_t            w_div_cmt_id;
scariv_pkg::grp_id_t            w_div_grp_id;
scariv_pkg::rnid_t w_div_rd_rnid;
scariv_pkg::reg_t               w_div_rd_type;
logic [RV_ENTRY_SIZE-1: 0]    w_div_index_oh;
scariv_pkg::brmask_t            w_div_br_mask;

logic                         w_flush_valid_load;
logic                         w_commit_flush_load;
logic                         w_br_flush_load;

logic                         w_flush_valid;
logic                         w_commit_flush;
logic                         w_br_flush;

generate for (genvar s_idx = 0; s_idx < MUL_STEP; s_idx++) begin : mul_loop
  logic [MUL_UNROLL-1: 0]                                 w_multiplicand_part;
  logic [MUL_UNROLL: 0]                                   w_step_multiplicand;
  logic [riscv_pkg::XLEN_W + MUL_UNROLL * (s_idx+1): 0]   w_prod;
  logic [riscv_pkg::XLEN_W + MUL_UNROLL + 2 - 1: 0]       w_prod_part;
  logic                                                   w_is_s_mul;

  if (s_idx == 0) begin
    assign w_step_multiplicand = {1'b0, w_op2[MUL_UNROLL-1: 0]};
    /* verilator lint_off WIDTH */
    assign w_prod = $signed(w_op1) * $signed(w_step_multiplicand);
    assign w_is_s_mul = (i_op == OP_MULH) | (i_op == OP_SMUL) | w_is_mulw_64;
  end else begin
    assign w_multiplicand_part = multiplicand_pipe[s_idx][MUL_UNROLL*s_idx +: MUL_UNROLL];
    if (s_idx == MUL_STEP - 1) begin
      assign w_step_multiplicand = neg_out_pipe[s_idx] ? $signed({neg_out_pipe[s_idx], w_multiplicand_part}) : {1'b0, w_multiplicand_part};
    end else begin
      assign w_step_multiplicand = {1'b0, w_multiplicand_part};
    end
    assign w_is_s_mul = (op_pipe[s_idx] == OP_MULH) | (op_pipe[s_idx] == OP_SMUL) | (op_pipe[s_idx] == OP_MULHSU) |
`ifdef RV64
                        (op_pipe[s_idx] == OP_MULW)
`else // RV64
                        1'b0
`endif  // RV64
                        ;

    /* verilator lint_off WIDTH */
    assign w_prod_part = $signed(multiplier_pipe[s_idx]) * $signed(w_step_multiplicand);
    assign w_prod[MUL_UNROLL * s_idx -1: 0] = prod_pipe[s_idx][MUL_UNROLL * s_idx -1: 0];
    assign w_prod[riscv_pkg::XLEN_W + MUL_UNROLL * (s_idx+1): MUL_UNROLL * s_idx] = $signed(w_prod_part) +
                                                                                      (w_is_s_mul ? $signed({prod_pipe[s_idx][MUL_UNROLL * s_idx + riscv_pkg::XLEN_W-1], prod_pipe[s_idx][MUL_UNROLL * s_idx +: riscv_pkg::XLEN_W]}) :
                                                                                       $signed({1'b0, prod_pipe[s_idx][MUL_UNROLL * s_idx +: riscv_pkg::XLEN_W]}));

  end // else: !if(s_idx == 0)

  logic w_mul_commit_flush;
  logic w_mul_br_flush;
  logic w_mul_flush_valid;

  scariv_pkg::brmask_t w_br_mask_next;

  if (s_idx != 0) begin
    assign w_mul_commit_flush = scariv_pkg::is_commit_flush_target(r_cmt_id[s_idx], r_grp_id[s_idx], i_commit);
    assign w_mul_br_flush     = scariv_pkg::is_br_flush_target(r_br_mask[s_idx], br_upd_if.brtag,
                                                             br_upd_if.dead, br_upd_if.mispredict) & br_upd_if.update;
    assign w_mul_flush_valid  = w_mul_commit_flush | w_mul_br_flush;

    always_comb begin
      w_br_mask_next = r_br_mask[s_idx];
      if (br_upd_if.update) begin
        w_br_mask_next[br_upd_if.brtag] = 1'b0;
      end
    end
  end else begin
    assign w_mul_flush_valid  = 1'b0;

    always_comb begin
      w_br_mask_next = i_br_mask;
      if (br_upd_if.update) begin
        w_br_mask_next[br_upd_if.brtag] = 1'b0;
      end
    end
  end

  if (s_idx == 0) begin
    always_ff @ (posedge i_clk, negedge i_reset_n) begin
      if (!i_reset_n) begin
        prod_pipe         [1] <= 'h0;
        multiplier_pipe   [1] <= 'h0;
        multiplicand_pipe [1] <= 'h0;
        r_mul_valid_pipe  [1] <= 1'b0;
        op_pipe           [1] <= OP__;
        neg_out_pipe      [1] <= 1'b0;
      end else begin
        /* verilator lint_off WIDTH */
        prod_pipe        [1] <= w_prod;
        multiplier_pipe  [1] <= w_op1;
        multiplicand_pipe[1] <= w_op2;
        r_mul_valid_pipe [1] <= i_valid & ~w_flush_valid_load & w_is_mul;
        op_pipe          [1] <= i_op;
        neg_out_pipe     [1] <= (i_op == OP_MULH || i_op == OP_SMUL) ? i_rs2[riscv_pkg::XLEN_W-1] : 1'b0;
        r_cmt_id         [1] <= i_cmt_id;
        r_grp_id         [1] <= i_grp_id;
        r_br_mask        [1] <= w_br_mask_next;

        r_mul_rd_rnid [1] <= i_rd_rnid;
        r_mul_rd_type [1] <= i_rd_type;
        r_mul_cmt_id  [1] <= i_cmt_id;
        r_mul_grp_id  [1] <= i_grp_id;
        r_mul_index_oh[1] <= i_index_oh;
      end // else: !if(!i_reset_n)
    end // always_ff @ (posedge i_clk, negedge i_reset_n)
  end else begin // if (s_idx == 0)
    always_ff @ (posedge i_clk, negedge i_reset_n) begin
      if (!i_reset_n) begin
        prod_pipe         [s_idx+1] <= 'h0;
        multiplier_pipe   [s_idx+1] <= 'h0;
        multiplicand_pipe [s_idx+1] <= 'h0;
        r_mul_valid_pipe  [s_idx+1] <= 1'b0;
        op_pipe           [s_idx+1] <= OP__;
        neg_out_pipe      [s_idx+1] <= 1'b0;
      end else begin
        /* verilator lint_off WIDTH */
        prod_pipe        [s_idx+1] <= $signed(w_prod);
        multiplier_pipe  [s_idx+1] <= multiplier_pipe  [s_idx];
        multiplicand_pipe[s_idx+1] <= multiplicand_pipe[s_idx];
        r_mul_valid_pipe [s_idx+1] <= r_mul_valid_pipe [s_idx] & ~w_mul_flush_valid;
        op_pipe          [s_idx+1] <= op_pipe          [s_idx];
        neg_out_pipe     [s_idx+1] <= neg_out_pipe     [s_idx];
        r_cmt_id         [s_idx+1] <= r_cmt_id         [s_idx];
        r_grp_id         [s_idx+1] <= r_grp_id         [s_idx];
        r_br_mask        [s_idx+1] <= w_br_mask_next;

        r_mul_rd_rnid [s_idx+1] <= r_mul_rd_rnid [s_idx];
        r_mul_rd_type [s_idx+1] <= r_mul_rd_type [s_idx];
        r_mul_cmt_id  [s_idx+1] <= r_mul_cmt_id  [s_idx];
        r_mul_grp_id  [s_idx+1] <= r_mul_grp_id  [s_idx];
        r_mul_index_oh[s_idx+1] <= r_mul_index_oh[s_idx];
      end // else: !if(!i_reset_n)
    end // always_ff @ (posedge i_clk, negedge i_reset_n)
  end // else: !if(s_idx == 0)
end // block: mul_loop
endgenerate


// ================
// Divide Unit
// ================

assign w_commit_flush_load = scariv_pkg::is_commit_flush_target(i_cmt_id, i_grp_id, i_commit);
assign w_br_flush_load     = scariv_pkg::is_br_flush_target(i_br_mask, br_upd_if.brtag,
                                                          br_upd_if.dead, br_upd_if.mispredict) & br_upd_if.update;
assign w_flush_valid_load = w_commit_flush_load | w_br_flush_load;

assign w_commit_flush = scariv_pkg::is_commit_flush_target(w_div_cmt_id, w_div_grp_id, i_commit);
assign w_br_flush     = scariv_pkg::is_br_flush_target(w_div_br_mask, br_upd_if.brtag,
                                                     br_upd_if.dead, br_upd_if.mispredict) & br_upd_if.update;
assign w_flush_valid  = w_commit_flush | w_br_flush;

assign o_stall = !w_div_ready | r_mul_valid_pipe[MUL_STEP-1-2];

scariv_div_unit
  #(
    .RV_ENTRY_SIZE(RV_ENTRY_SIZE)
    )
u_scariv_div_unit
  (
   .i_clk (i_clk),
   .i_reset_n (i_reset_n),

   .i_flush_valid (w_flush_valid),

   .i_valid (i_valid & ~w_flush_valid_load),
   .o_ready (w_div_ready),
   .i_op (i_op),

   .i_cmt_id   (i_cmt_id  ),
   .i_grp_id   (i_grp_id  ),
   .i_br_mask  (i_br_mask ),
   .i_rd_rnid  (i_rd_rnid ),
   .i_rd_type  (i_rd_type ),
   .i_index_oh (i_index_oh),

   .i_rs1 (i_rs1),
   .i_rs2 (i_rs2),

   .i_resp_ready (~r_mul_valid_pipe[MUL_STEP]),
   .o_valid (w_div_valid),
   .o_res   (w_div_res),

   .o_cmt_id   (w_div_cmt_id  ),
   .o_grp_id   (w_div_grp_id  ),
   .o_br_mask  (w_div_br_mask ),
   .o_rd_rnid  (w_div_rd_rnid ),
   .o_rd_type  (w_div_rd_type ),
   .o_index_oh (w_div_index_oh)
   );


// ================
// Response
// ================

logic                         w_div_out_fire;
assign w_div_out_fire = w_div_valid & ~r_mul_valid_pipe[MUL_STEP];

assign o_valid = r_mul_valid_pipe[MUL_STEP] | w_div_valid;
assign o_res   = w_div_out_fire ? w_div_res :
                 (op_pipe[MUL_STEP] == OP_MULH || op_pipe[MUL_STEP] == OP_MULHU || op_pipe[MUL_STEP] == OP_MULHSU) ? prod_pipe [MUL_STEP][riscv_pkg::XLEN_W +: riscv_pkg::XLEN_W] :
`ifdef RV64
                 (op_pipe[MUL_STEP] == OP_MULW) ? {{(riscv_pkg::XLEN_W-32){prod_pipe [MUL_STEP][31]}}, prod_pipe [MUL_STEP][31 : 0]}:
`endif // RV64
                 prod_pipe [MUL_STEP][riscv_pkg::XLEN_W-1: 0];

assign o_rd_rnid  = w_div_out_fire ? w_div_rd_rnid  : r_mul_rd_rnid[MUL_STEP];
assign o_rd_type  = w_div_out_fire ? w_div_rd_type  : r_mul_rd_type[MUL_STEP];
assign o_cmt_id   = w_div_out_fire ? w_div_cmt_id   : r_mul_cmt_id [MUL_STEP];
assign o_grp_id   = w_div_out_fire ? w_div_grp_id   : r_mul_grp_id [MUL_STEP];
assign o_index_oh = w_div_out_fire ? w_div_index_oh : r_mul_index_oh[MUL_STEP];

endmodule // scariv_muldiv_pipe
