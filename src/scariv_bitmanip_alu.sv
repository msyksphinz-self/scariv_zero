// ------------------------------------------------------------------------
// NAME : scariv_bitmanip_alu
// TYPE : module
// ------------------------------------------------------------------------
// Bit-manipulation extension ALU
// ------------------------------------------------------------------------
// ------------------------------------------------------------------------

module scariv_bitmanip_alu
  import decoder_alu_ctrl_pkg::*;
(
 input riscv_pkg::xlen_t  i_rs1,
 input riscv_pkg::xlen_t  i_rs2,
 input op_t               i_op,

 output riscv_pkg::xlen_t o_out
 );

localparam XLEN_W_W = $clog2(riscv_pkg::XLEN_W);

riscv_pkg::xlen_t   w_bitwise_or;
riscv_pkg::xlen_t   w_byte_rev;

riscv_pkg::xlen_t   w_extract_msb_xlen;
logic [XLEN_W_W: 0] w_leading_zero_count_xlen;

logic [31: 0]       w_extract_msb_32;
logic [ 4: 0]       w_leading_zero_count_32;

logic [XLEN_W_W: 0] w_bit_cnt_xlen;
logic [       4: 0] w_bit_cnt_32;

riscv_pkg::xlen_t   w_extract_lsb_xlen;
logic [XLEN_W_W: 0] w_trailing_zero_count_xlen;

logic [31: 0]       w_extract_lsb_32;
logic [ 4: 0]       w_trailing_zero_count_32;

logic [riscv_pkg::XLEN_W*2-1: 0] w_clmul_temp[riscv_pkg::XLEN_W];
logic [riscv_pkg::XLEN_W*2-1: 0] w_clmul;

always_comb begin
  case (i_op)
    OP_UNSIGND_ADD_32         : o_out = i_rs1 + {31'h0, i_rs2[31: 0]};
    OP_AND_INV                : o_out = i_rs1 & ~i_rs2;
    OP_CARRY_LESS_MUL         : o_out = w_clmul[riscv_pkg::XLEN_W-1: 0];
    OP_CARRY_LESS_MULH        : o_out = w_clmul[riscv_pkg::XLEN_W*2-1: riscv_pkg::XLEN_W];
    OP_CARRY_LESS_MULR        : o_out = w_clmul[riscv_pkg::XLEN_W*2-2: riscv_pkg::XLEN_W-1];
    OP_CLZ                    : o_out = w_leading_zero_count_xlen;
    OP_CLZW                   : o_out = w_leading_zero_count_32;
    OP_CPOP                   : o_out = w_bit_cnt_xlen;
    OP_CPOPW                  : o_out = w_bit_cnt_32;
    OP_CTZ                    : o_out = w_trailing_zero_count_xlen;
    OP_CTZW                   : o_out = w_trailing_zero_count_32;
    OP_SIGNED_MAX             : o_out = $signed(i_rs1) > $signed(i_rs2) ? i_rs1 : i_rs2;
    OP_UNSIGNED_MAX           : o_out =         i_rs1  >         i_rs2  ? i_rs1 : i_rs2;
    OP_SIGNED_MIN             : o_out = $signed(i_rs1) < $signed(i_rs2) ? i_rs1 : i_rs2;
    OP_UNSIGNED_MIN           : o_out =         i_rs1  <         i_rs2  ? i_rs1 : i_rs2;
    OP_BITWISE_OR             : o_out = w_bitwise_or;
    OP_INVERTED_OR            : o_out = i_rs1 | ~i_rs2;
    OP_BYTE_REVERSE           : o_out = w_byte_rev;
    OP_ROTATE_LEFT            : o_out = i_rs1 << i_rs2[XLEN_W_W-1: 0] | i_rs1 >> (riscv_pkg::XLEN_W - i_rs2[XLEN_W_W-1: 0]);
    OP_ROTATE_LEFT_WORD       : o_out = i_rs1 << i_rs2[         4: 0] | i_rs1 >> (               32 - i_rs2[         4: 0]);
    OP_ROTATE_RIGHT           : o_out = i_rs1 >> i_rs2[XLEN_W_W-1: 0] | i_rs1 << (riscv_pkg::XLEN_W - i_rs2[XLEN_W_W-1: 0]);
    OP_ROTATE_RIGHT_32        : o_out = i_rs1 >> i_rs2[         4: 0] | i_rs1 << (               32 - i_rs2[         4: 0]);
    OP_BIT_CLEAR              : o_out = i_rs1 & ~(1 << i_rs2[XLEN_W_W-1: 0]);
    OP_BIT_EXTRACT            : o_out = i_rs1[i_rs2[XLEN_W_W-1: 0]];
    OP_BIT_INVERT             : o_out = i_rs1 ^ (1 << i_rs2[XLEN_W_W-1: 0]);
    OP_BIT_SET                : o_out = i_rs1 | (1 << i_rs2[XLEN_W_W-1: 0]);
    OP_SIGN_EXTEND_8          : o_out = {{(riscv_pkg::XLEN_W- 8){i_rs1[ 8]}}, i_rs1[ 7: 0]};
    OP_SIGN_EXTEND_16         : o_out = {{(riscv_pkg::XLEN_W-16){i_rs1[16]}}, i_rs1[15: 0]};
    OP_SIGNED_SH1ADD          : o_out = i_rs1 + {i_rs2[riscv_pkg::XLEN_W-2: 0], 1'b0};
    OP_UNSIGNED_SH1ADD_32     : o_out = i_rs1 + {{(riscv_pkg::XLEN_W-31){1'b0}}, i_rs2[31: 0], 1'b0};
    OP_SIGNED_SH2ADD          : o_out = i_rs1 + {i_rs2[riscv_pkg::XLEN_W-3: 0], 2'b00};
    OP_UNSIGNED_SH2ADD_32     : o_out = i_rs1 + {{(riscv_pkg::XLEN_W-30){1'b0}}, i_rs2[31: 0], 2'b00};
    OP_SIGNED_SH3ADD          : o_out = i_rs1 + {i_rs2[riscv_pkg::XLEN_W-4: 0], 3'b000};
    OP_UNSIGNED_SH3ADD_32     : o_out = i_rs1 + {{(riscv_pkg::XLEN_W-29){1'b0}}, i_rs2[31: 0], 3'b000};
    OP_UNSIGNED_SHIFT_LEFT_32 : o_out = {{(riscv_pkg::XLEN_W-32){1'b0}}, i_rs1[31: 0]} << i_rs2;
    OP_XNOR                   : o_out = ~(i_rs1 ^ i_rs2);
    OP_ZERO_EXTEND_16         : o_out = {{(riscv_pkg::XLEN_W-16){1'b0}}, i_rs1[15: 0]};
    default                   : o_out = 'h0;
  endcase // case (i_op)
end // always_comb

// bitwise-or
generate for (genvar b_idx = 0; b_idx < riscv_pkg::XLEN_W; b_idx += 8) begin: byte_loop
  assign w_bitwise_or[b_idx +:     8] = {8{|i_rs1[b_idx +: 8]}};
  /* verilator lint_off SELRANGE */
  assign w_byte_rev  [b_idx+7: b_idx] =     i_rs1[b_idx : b_idx+7];
end endgenerate

bit_tree_msb #(.WIDTH(riscv_pkg::XLEN_W)) u_bit_tree_msb_xlen     (.in(i_rs1),                .out(w_extract_msb_xlen));
bit_encoder  #(.WIDTH(riscv_pkg::XLEN_W)) u_bit_msb_encoder_xlen  (.i_in(w_extract_msb_xlen), .o_out(w_leading_zero_count_xlen));

bit_tree_msb #(.WIDTH(32)) u_bit_tree_msb_32    (.in(i_rs1[31: 0]),       .out(w_extract_msb_32  ));
bit_encoder  #(.WIDTH(32)) u_bit_msb_encoder_32 (.i_in(w_extract_msb_32), .o_out(w_leading_zero_count_32));

bit_cnt #(.WIDTH(riscv_pkg::XLEN_W)) u_bit_cnt_xlen (.in(i_rs1       ), .out(w_bit_cnt_xlen));
bit_cnt #(.WIDTH(32))                u_bit_cnt_32   (.in(i_rs1[31: 0]), .out(w_bit_cnt_32));

bit_tree_lsb #(.WIDTH(riscv_pkg::XLEN_W)) u_bit_tree_lsb_xlen    (.in(i_rs1),                 .out(w_extract_lsb_xlen));
bit_encoder  #(.WIDTH(riscv_pkg::XLEN_W)) u_bit_lsb_encoder_xlen (.i_in(~w_extract_lsb_xlen), .o_out(w_trailing_zero_count_xlen));

bit_tree_lsb #(.WIDTH(32)) u_bit_tree_lsb_32    (.in(i_rs1[31: 0]),        .out(w_extract_lsb_32  ));
bit_encoder  #(.WIDTH(32)) u_bit_lsb_encoder_32 (.i_in(~w_extract_lsb_32), .o_out(w_trailing_zero_count_32));

generate for (genvar idx = 0; idx < riscv_pkg::XLEN_W; idx++) begin : clmul_loop
  assign w_clmul_temp[idx] = i_rs1 << idx;
end endgenerate
bit_or #(.WIDTH(riscv_pkg::XLEN_W*2), .WORDS(riscv_pkg::XLEN_W)) u_bit_or (.i_data(w_clmul_temp), .o_selected(w_clmul));

endmodule // scariv_bitmanip_alu
