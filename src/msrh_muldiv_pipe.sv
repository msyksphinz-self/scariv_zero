module msrh_muldiv_pipe
  import decoder_alu_ctrl_pkg::*;
#(
  parameter RV_ENTRY_SIZE = 32,
  parameter MUL_UNROLL = 8
  )
(
 input logic                           i_clk,
 input logic                           i_reset_n,

 input logic                           i_valid,
 input                                 op_t i_op,

 input logic [msrh_pkg::RNID_W-1: 0]   i_rd_rnid,
 input msrh_pkg::reg_t                 i_rd_type,
 input logic [RV_ENTRY_SIZE-1: 0]      i_index_oh,

 input logic [riscv_pkg::XLEN_W-1: 0]  i_rs1,
 input logic [riscv_pkg::XLEN_W-1: 0]  i_rs2,

 output logic                          o_stall,

 output logic                          o_valid,
 output logic [riscv_pkg::XLEN_W-1: 0] o_res,

 output logic [msrh_pkg::RNID_W-1: 0]  o_rd_rnid,
 output msrh_pkg::reg_t                o_rd_type,
 output logic [RV_ENTRY_SIZE-1: 0]     o_index_oh
 );

logic [riscv_pkg::XLEN_W: 0]           w_op1;
logic [riscv_pkg::XLEN_W: 0]           w_op2;

logic                                  w_is_mul;
assign w_is_mul = i_op == OP_SMUL || i_op == OP_MULH || i_op == OP_MULHU || i_op == OP_MULHSU;

assign w_op1 = (i_op == OP_SMUL || i_op == OP_MULH || i_op == OP_MULHSU) ? {i_rs1[riscv_pkg::XLEN_W-1], i_rs1} : {1'b0, i_rs1};
assign w_op2 = (i_op == OP_SMUL || i_op == OP_MULH)                      ? {i_rs2[riscv_pkg::XLEN_W-1], i_rs2} : {1'b0, i_rs2};



parameter MUL_STEP = (riscv_pkg::XLEN_W + MUL_UNROLL - 1) / MUL_UNROLL;
logic [MUL_STEP: 0]                    r_mul_valid_pipe;
logic [riscv_pkg::XLEN_W: 0]           multiplicand_pipe  [MUL_STEP + 1];
logic [riscv_pkg::XLEN_W: 0]           multiplier_pipe[MUL_STEP + 1];
logic [riscv_pkg::XLEN_W*2:0]          prod_pipe        [MUL_STEP + 1];
logic [MUL_STEP: 0]                    neg_out_pipe;
op_t  op_pipe                                  [MUL_STEP + 1];

logic [msrh_pkg::RNID_W-1: 0]             r_mul_rd_rnid [MUL_STEP];
msrh_pkg::reg_t                           r_mul_rd_type [MUL_STEP];
logic [RV_ENTRY_SIZE-1: 0]                r_mul_index_oh[MUL_STEP];

generate for (genvar s_idx = 0; s_idx < MUL_STEP; s_idx++) begin : mul_loop
  logic [MUL_UNROLL: 0] w_step_multiplier;
  logic [riscv_pkg::XLEN_W + MUL_UNROLL * (s_idx+1): 0] w_prod;
  logic [riscv_pkg::XLEN_W + MUL_UNROLL + 2 - 1: 0] w_prod_part;
  if (s_idx == 0) begin
    assign w_step_multiplier = {1'b0, w_op1[MUL_UNROLL-1: 0]};
    /* verilator lint_off WIDTH */
    assign w_prod = w_step_multiplier * w_op2;
  end else begin
    if (s_idx == MUL_STEP - 1) begin
      assign w_step_multiplier = {neg_out_pipe[s_idx], multiplier_pipe[s_idx][MUL_UNROLL*s_idx +: MUL_UNROLL]};
    end else begin
      assign w_step_multiplier = {1'b0, multiplier_pipe[s_idx][MUL_UNROLL*s_idx +: MUL_UNROLL]};
    end

    /* verilator lint_off WIDTH */
    assign w_prod_part = $signed(w_step_multiplier) * $signed(multiplicand_pipe[s_idx]);
    assign w_prod[MUL_UNROLL * s_idx -1: 0] = prod_pipe[s_idx][MUL_UNROLL * s_idx -1: 0];
    assign w_prod[riscv_pkg::XLEN_W + MUL_UNROLL * (s_idx+1): MUL_UNROLL * s_idx] = $signed(w_prod_part) +
                                                                                    // $signed({prod_pipe[s_idx][MUL_UNROLL * (s_idx + 1)-1], prod_pipe[s_idx][MUL_UNROLL * s_idx +: riscv_pkg::XLEN_W]});
                                                                                    $signed(prod_pipe[s_idx][MUL_UNROLL * s_idx +: riscv_pkg::XLEN_W]);
  end // else: !if(s_idx == 0)

  always_ff @ (posedge i_clk, negedge i_reset_n) begin
    if (!i_reset_n) begin
      prod_pipe        [s_idx+1] <= 'h0;
      multiplier_pipe[s_idx+1] <= 'h0;
      multiplicand_pipe  [s_idx+1] <= 'h0;
      r_mul_valid_pipe       [s_idx+1] <= 1'b0;
      op_pipe          [s_idx+1] <= 'h0;
      neg_out_pipe     [s_idx+1] <= 1'b0;
    end else begin
      if (s_idx == 0) begin
        /* verilator lint_off WIDTH */
        prod_pipe        [s_idx+1] <= w_prod;
        multiplier_pipe  [s_idx+1] <= {1'b0, i_rs1};
        multiplicand_pipe[s_idx+1] <= w_op2;
        r_mul_valid_pipe [s_idx+1] <= i_valid & w_is_mul;
        op_pipe          [s_idx+1] <= i_op;
        neg_out_pipe     [s_idx+1] <= (i_op == OP_MULH || i_op == OP_MULHSU) ? i_rs1[riscv_pkg::XLEN_W-1] : 1'b0;

        r_mul_rd_rnid [s_idx+1] <= i_rd_rnid;
        r_mul_rd_type [s_idx+1] <= i_rd_type;
        r_mul_index_oh[s_idx+1] <= i_index_oh;
      end else begin
        /* verilator lint_off WIDTH */
        prod_pipe        [s_idx+1] <= $signed(w_prod);
        multiplier_pipe  [s_idx+1] <= multiplier_pipe  [s_idx];
        multiplicand_pipe[s_idx+1] <= multiplicand_pipe[s_idx];
        r_mul_valid_pipe [s_idx+1] <= r_mul_valid_pipe [s_idx];
        op_pipe          [s_idx+1] <= op_pipe          [s_idx];
        neg_out_pipe     [s_idx+1] <= neg_out_pipe     [s_idx];

        r_mul_rd_rnid [s_idx+1] <= r_mul_rd_rnid [s_idx];
        r_mul_rd_type [s_idx+1] <= r_mul_rd_type [s_idx];
        r_mul_index_oh[s_idx+1] <= r_mul_index_oh[s_idx];
      end // else: !if(s_idx == 0)
    end // else: !if(!i_reset_n)
  end // always_ff @ (posedge i_clk, negedge i_reset_n)
end // block: mul_loop
endgenerate


// ================
// Divide Unit
// ================

logic         w_div_ready;
logic         w_div_valid;
logic [63: 0] w_div_res;

logic [msrh_pkg::RNID_W-1: 0] w_div_rd_rnid;
msrh_pkg::reg_t               w_div_rd_type;
logic [RV_ENTRY_SIZE-1: 0]    w_div_index_oh;

assign o_stall = !w_div_ready | r_mul_valid_pipe[MUL_STEP-1-2];

msrh_div_unit
  #(
    .RV_ENTRY_SIZE(RV_ENTRY_SIZE)
    )
u_msrh_div_unit
  (
   .i_clk (i_clk),
   .i_reset_n (i_reset_n),

   .i_valid (i_valid),
   .o_ready (w_div_ready),
   .i_op (i_op),

   .i_rd_rnid  (i_rd_rnid ),
   .i_rd_type  (i_rd_type ),
   .i_index_oh (i_index_oh),

   .i_rs1 (i_rs1),
   .i_rs2 (i_rs2),

   .o_valid (w_div_valid),
   .o_res   (w_div_res),

   .o_rd_rnid  (w_div_rd_rnid ),
   .o_rd_type  (w_div_rd_type ),
   .o_index_oh (w_div_index_oh)
   );


// ================
// Response
// ================

assign o_valid = r_mul_valid_pipe[MUL_STEP] | w_div_valid;
assign o_res   = w_div_valid ? w_div_res :
                 (op_pipe[MUL_STEP] == OP_MULH || op_pipe[MUL_STEP] == OP_MULHU || op_pipe[MUL_STEP] == OP_MULHSU) ? prod_pipe [MUL_STEP][riscv_pkg::XLEN_W +: riscv_pkg::XLEN_W] :
                 prod_pipe [MUL_STEP][riscv_pkg::XLEN_W-1: 0];

assign o_rd_rnid  = w_div_valid ? w_div_rd_rnid  : r_mul_rd_rnid[MUL_STEP];
assign o_rd_type  = w_div_valid ? w_div_rd_type  : r_mul_rd_type[MUL_STEP];
assign o_index_oh = w_div_valid ? w_div_index_oh : r_mul_index_oh[MUL_STEP];

endmodule // msrh_muldiv_pipe
