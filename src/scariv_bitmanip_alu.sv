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

 output logic             o_valid,
 output riscv_pkg::xlen_t o_out
 );

localparam XLEN_W_W = $clog2(riscv_pkg::XLEN_W);

riscv_pkg::xlen_t   w_bitwise_or;
riscv_pkg::xlen_t   w_byte_rev;
logic [31: 0]       w_shift_tmp_32;

riscv_pkg::xlen_t   w_extract_msb_xlen;
logic [XLEN_W_W: 0] w_leading_zero_count_xlen;

logic [31: 0]       w_extract_msb_32;
logic [ 5: 0]       w_leading_zero_count_32;

logic [XLEN_W_W: 0] w_bit_cnt_xlen;
logic [       5: 0] w_bit_cnt_32;

riscv_pkg::xlen_t   w_extract_lsb_xlen;
logic [XLEN_W_W: 0] w_trailing_zero_count_xlen;

logic [31: 0]       w_extract_lsb_32;
logic [ 5: 0]       w_trailing_zero_count_32;

logic [riscv_pkg::XLEN_W*2-1: 0] w_clmul_temp[riscv_pkg::XLEN_W];
logic [riscv_pkg::XLEN_W*2-1: 0] w_clmul;

always_comb begin
  o_valid = 1'b1;
  w_shift_tmp_32 = 'h0;

  case (i_op)
    OP_UNSIGND_ADD_32         : o_out = {31'h0, i_rs1[31: 0]} + i_rs2;
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
    OP_ROTATE_LEFT            : o_out = (i_rs1        << i_rs2[XLEN_W_W-1: 0]) | (i_rs1        >> (riscv_pkg::XLEN_W - i_rs2[XLEN_W_W-1: 0]));
    OP_ROTATE_LEFT_WORD       : begin
      w_shift_tmp_32 = (i_rs1[31: 0] << i_rs2[ 4: 0]) | (i_rs1[31: 0] >> (32 - i_rs2[ 4: 0]));
      o_out = {{(riscv_pkg::XLEN_W-32){w_shift_tmp_32[31]}}, w_shift_tmp_32};
    end
    OP_ROTATE_RIGHT           : o_out = (i_rs1        >> i_rs2[XLEN_W_W-1: 0]) | (i_rs1        << (riscv_pkg::XLEN_W - i_rs2[XLEN_W_W-1: 0]));
    OP_ROTATE_RIGHT_32        : begin
      w_shift_tmp_32 = (i_rs1[31: 0] >> i_rs2[4: 0]) | (i_rs1[31: 0] << (32 - i_rs2[4: 0]));
      o_out = {{(riscv_pkg::XLEN_W-32){w_shift_tmp_32[31]}}, w_shift_tmp_32};
    end
    OP_BIT_CLEAR              : o_out = i_rs1 & ~(1 << i_rs2[XLEN_W_W-1: 0]);
    OP_BIT_EXTRACT            : o_out = i_rs1[i_rs2[XLEN_W_W-1: 0]];
    OP_BIT_INVERT             : o_out = i_rs1 ^ (1 << i_rs2[XLEN_W_W-1: 0]);
    OP_BIT_SET                : o_out = i_rs1 | (1 << i_rs2[XLEN_W_W-1: 0]);
    OP_SIGN_EXTEND_8          : o_out = {{(riscv_pkg::XLEN_W- 8){i_rs1[ 7]}}, i_rs1[ 7: 0]};
    OP_SIGN_EXTEND_16         : o_out = {{(riscv_pkg::XLEN_W-16){i_rs1[15]}}, i_rs1[15: 0]};
    OP_SIGNED_SH1ADD          : o_out = i_rs2 + {i_rs1[riscv_pkg::XLEN_W-2: 0], 1'b0};
    OP_UNSIGNED_SH1ADD_32     : o_out = i_rs2 + {{(riscv_pkg::XLEN_W-31){1'b0}}, i_rs1[31: 0], 1'b0};
    OP_SIGNED_SH2ADD          : o_out = i_rs2 + {i_rs1[riscv_pkg::XLEN_W-3: 0], 2'b00};
    OP_UNSIGNED_SH2ADD_32     : o_out = i_rs2 + {{(riscv_pkg::XLEN_W-30){1'b0}}, i_rs1[31: 0], 2'b00};
    OP_SIGNED_SH3ADD          : o_out = i_rs2 + {i_rs1[riscv_pkg::XLEN_W-4: 0], 3'b000};
    OP_UNSIGNED_SH3ADD_32     : o_out = i_rs2 + {{(riscv_pkg::XLEN_W-29){1'b0}}, i_rs1[31: 0], 3'b000};
    OP_UNSIGNED_SHIFT_LEFT_32 : o_out = {{(riscv_pkg::XLEN_W-32){1'b0}}, i_rs1[31: 0]} << i_rs2[ 5: 0];
    OP_XNOR                   : o_out = ~(i_rs1 ^ i_rs2);
    OP_ZERO_EXTEND_16         : o_out = {{(riscv_pkg::XLEN_W-16){1'b0}}, i_rs1[15: 0]};
    default                   : begin
      o_out = 'h0;
      o_valid = 1'b0;
    end
  endcase // case (i_op)
end // always_comb

// bitwise-or
generate for (genvar b_idx = 0; b_idx < riscv_pkg::XLEN_W; b_idx += 8) begin: byte_loop
  assign w_bitwise_or[b_idx +: 8] = {8{|i_rs1[b_idx +: 8]}};
  /* verilator lint_off SELRANGE */
  assign w_byte_rev  [b_idx +: 8] = i_rs1[riscv_pkg::XLEN_W-b_idx-1: riscv_pkg::XLEN_W-b_idx-8];
end endgenerate

bit_clz_64 u_bit_clz_64 (.i_in(i_rs1       ), .o_out(w_leading_zero_count_xlen));
bit_clz_32 u_bit_clz_32 (.i_in(i_rs1[31: 0]), .o_out(w_leading_zero_count_32));

bit_cnt #(.WIDTH(riscv_pkg::XLEN_W)) u_bit_cnt_xlen (.in(i_rs1       ), .out(w_bit_cnt_xlen));
bit_cnt #(.WIDTH(32))                u_bit_cnt_32   (.in(i_rs1[31: 0]), .out(w_bit_cnt_32));

bit_clz_64 u_bit_ctz_64 (.i_in({<<1{i_rs1[63: 0]}}), .o_out(w_trailing_zero_count_xlen));
bit_clz_32 u_bit_ctz_32 (.i_in({<<1{i_rs1[31: 0]}}), .o_out(w_trailing_zero_count_32));

generate for (genvar idx = 0; idx < riscv_pkg::XLEN_W; idx++) begin : clmul_loop
  assign w_clmul_temp[idx] = i_rs2[idx] ? i_rs1 << idx : 'h0;
end endgenerate
generate for (genvar w_idx = 0; w_idx < riscv_pkg::XLEN_W*2; w_idx++) begin : clmul_width_loop
  logic [riscv_pkg::XLEN_W-1: 0] w_clmul_ver_tmp;
  for (genvar v_idx = 0; v_idx < riscv_pkg::XLEN_W; v_idx++) begin
    assign w_clmul_ver_tmp[v_idx] = w_clmul_temp[v_idx][w_idx];
  end
  assign w_clmul[w_idx] = ^w_clmul_ver_tmp;
end endgenerate

endmodule // scariv_bitmanip_alu
