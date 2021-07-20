module msrh_muldiv_pipe
  import decoder_alu_ctrl_pkg::*;
#(
  parameter MUL_UNROLL = 8
  )
(
 input logic                           i_clk,
 input logic                           i_reset_n,

 input logic                           i_valid,
 input                                 op_t i_op,

 input logic [riscv_pkg::XLEN_W-1: 0]  i_rs1,
 input logic [riscv_pkg::XLEN_W-1: 0]  i_rs2,

 output logic                          o_valid,
 output logic [riscv_pkg::XLEN_W-1: 0] o_res
 );

logic [riscv_pkg::XLEN_W: 0]           w_op1;
logic [riscv_pkg::XLEN_W: 0]           w_op2;

assign w_op1 = (i_op == OP_SMUL || i_op == OP_MULH || i_op == OP_MULHSU) ? {i_rs1[riscv_pkg::XLEN_W-1], i_rs1} : {1'b0, i_rs1};
assign w_op2 = (i_op == OP_SMUL || i_op == OP_MULH)                      ? {i_rs2[riscv_pkg::XLEN_W-1], i_rs2} : {1'b0, i_rs2};



parameter MUL_STEP = (riscv_pkg::XLEN_W + MUL_UNROLL - 1) / MUL_UNROLL;
logic [MUL_STEP: 0]                    valid_pipe;
logic [riscv_pkg::XLEN_W: 0]  multiplier_pipe  [MUL_STEP + 1];
logic [riscv_pkg::XLEN_W: 0]  multiplicand_pipe[MUL_STEP + 1];
logic [riscv_pkg::XLEN_W*2:0] prod_pipe        [MUL_STEP + 1];
op_t  op_pipe                                  [MUL_STEP + 1];

generate for (genvar s_idx = 0; s_idx < MUL_STEP; s_idx++) begin : mul_loop
  logic [MUL_UNROLL: 0] w_step_multiplier;
  logic [riscv_pkg::XLEN_W + MUL_UNROLL * (s_idx+1): 0] w_prod;
  logic [riscv_pkg::XLEN_W: 0] w_step_multiplicand;
  if (s_idx == 0) begin
    assign w_step_multiplier = {1'b0, w_op2[MUL_UNROLL-1: 0]};
    /* verilator lint_off WIDTH */
    assign w_prod = w_op1 * w_step_multiplier;
  end else begin
    assign w_step_multiplier = {1'b0, multiplier_pipe[s_idx][MUL_UNROLL*s_idx +: MUL_UNROLL]};
    /* verilator lint_off WIDTH */
    assign w_prod[MUL_UNROLL * s_idx -1: 0] = prod_pipe[s_idx][MUL_UNROLL * s_idx -1: 0];
    assign w_prod[riscv_pkg::XLEN_W + MUL_UNROLL * (s_idx+1): MUL_UNROLL * s_idx] = multiplicand_pipe[s_idx] * w_step_multiplier +
                                                                                    prod_pipe[s_idx][MUL_UNROLL * s_idx +: riscv_pkg::XLEN_W];
    // assign w_prod = {multiplicand_pipe[s_idx] * w_step_multiplier, {(MUL_UNROLL * s_idx){1'b0}}} +
    //                 prod_pipe[s_idx][riscv_pkg::XLEN_W + MUL_UNROLL * s_idx: MUL_UNROLL * s_idx];
  end // else: !if(s_idx == 0)

  always_ff @ (posedge i_clk, negedge i_reset_n) begin
    if (!i_reset_n) begin
      prod_pipe        [s_idx+1] <= 'h0;
      multiplicand_pipe[s_idx+1] <= 'h0;
      multiplier_pipe  [s_idx+1] <= 'h0;
      valid_pipe       [s_idx+1] <= 1'b0;
      op_pipe          [s_idx+1] <= 'h0;
    end else begin
      if (s_idx == 0) begin
        /* verilator lint_off WIDTH */
        prod_pipe        [s_idx+1] <= w_prod;
        multiplicand_pipe[s_idx+1] <= w_op1;
        multiplier_pipe  [s_idx+1] <= w_op2;
        valid_pipe       [s_idx+1] <= i_valid;
        op_pipe          [s_idx+1] <= i_op;
      end else begin
        /* verilator lint_off WIDTH */
        prod_pipe        [s_idx+1] <= w_prod;
        multiplicand_pipe[s_idx+1] <= multiplicand_pipe[s_idx];
        multiplier_pipe  [s_idx+1] <= multiplier_pipe  [s_idx];
        valid_pipe       [s_idx+1] <= valid_pipe       [s_idx];
        op_pipe          [s_idx+1] <= op_pipe          [s_idx];
      end // else: !if(s_idx == 0)
    end // else: !if(!i_reset_n)
  end // always_ff @ (posedge i_clk, negedge i_reset_n)
end // block: mul_loop
endgenerate


assign o_valid = valid_pipe[MUL_STEP];
assign o_res   = (op_pipe[MUL_STEP] == OP_MULH || op_pipe[MUL_STEP] == OP_MULHU || op_pipe[MUL_STEP] == OP_MULHSU) ? prod_pipe [MUL_STEP][riscv_pkg::XLEN_W+1 +: riscv_pkg::XLEN_W] :
                 prod_pipe [MUL_STEP][riscv_pkg::XLEN_W-1: 0];

endmodule // msrh_muldiv_pipe
