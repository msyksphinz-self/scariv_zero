/*
 * Divide Unit: Import from Rocket-Chip
 * from chipyard.TestHarness.MediumBoomConfig/chipyard.TestHarness.MediumBoomConfig.top.v
 * Note: Multiplier also included but ignored.
 */


module msrh_div_unit
  import decoder_alu_ctrl_pkg::*;
#(
  parameter RV_ENTRY_SIZE = 32
  )
(
 input logic                           i_clk,
 input logic                           i_reset_n,

 input logic                           i_valid,
 output logic                          o_ready,
 input op_t                            i_op,

 input logic [msrh_pkg::RNID_W-1: 0]   i_rd_rnid,
 input msrh_pkg::reg_t                 i_rd_type,
 input logic [RV_ENTRY_SIZE-1: 0]      i_index_oh,

 input logic [riscv_pkg::XLEN_W-1: 0]  i_rs1,
 input logic [riscv_pkg::XLEN_W-1: 0]  i_rs2,

 output logic                          o_valid,
 output logic [riscv_pkg::XLEN_W-1: 0] o_res,

 output logic [msrh_pkg::RNID_W-1: 0]   o_rd_rnid,
 output msrh_pkg::reg_t                 o_rd_type,
 output logic [RV_ENTRY_SIZE-1: 0]      o_index_oh
 );

logic                                  w_valid;
logic                                  w_is_64bit;
logic [ 3: 0]                          w_fn;

always_comb begin
  case(i_op)
`ifdef RV64
    OP_DIVW,
    OP_DIVUW,
    OP_REMW,
    OP_REMUW,
`endif // RV64
    OP_SDIV,
    OP_UDIV,
    OP_SREM,
    OP_UREM
      : w_valid = 1'b1;
    default  : w_valid = 1'b0;
  endcase // case (i_op)

  case (i_op)
    OP_SDIV,
    OP_UDIV,
    OP_SREM,
    OP_UREM : w_is_64bit = 1'b1;
    default : w_is_64bit = 1'b0;
  endcase // case (i_op)

  case (i_op)
    OP_SDIV  : w_fn = 'h04;
    OP_UDIV  : w_fn = 'h05;
    OP_SREM  : w_fn = 'h06;
    OP_UREM  : w_fn = 'h07;
`ifdef // RV64
    OP_DIVW  : w_fn = 'h04;
    OP_DIVUW : w_fn = 'h05;
    OP_REMW  : w_fn = 'h06;
    OP_REMUW : w_fn = 'h07;
`endif // RV64
    default  : w_fn = 'h00;
  endcase // case (i_op)

end // always_comb

always_ff @ (posedge i_clk) begin
  if (w_valid) begin
    o_rd_rnid  <= i_rd_rnid;
    o_rd_type  <= i_rd_type;
    o_index_oh <= i_index_oh;
  end
end


MulDiv u_MulDiv
  (
   .clock (i_clk     ),
   .reset (~i_reset_n),
   .io_req_valid (w_valid),
   .io_req_ready    (o_ready),
   .io_req_bits_fn  (w_fn),
`ifdef RV64
   .io_req_bits_dw  (w_is_64bit),
`endif // RV64
`ifdef RV32
   .io_req_bits_tag ('h0),
   .io_resp_bits_tag (),
`endif // RV32
   .io_req_bits_in1 (i_rs1),
   .io_req_bits_in2 (i_rs2),
   .io_kill (1'b0),
   .io_resp_ready (1'b1),
   .io_resp_valid (o_valid),
   .io_resp_bits_data (o_res)
   );

endmodule // msrh_div_unit


`ifdef RV64

module MulDiv(
  input         clock,
  input         reset,
  output        io_req_ready,
  input         io_req_valid,
  input  [3:0]  io_req_bits_fn,
  input         io_req_bits_dw,
  input  [63:0] io_req_bits_in1,
  input  [63:0] io_req_bits_in2,
  input         io_kill,
  input         io_resp_ready,
  output        io_resp_valid,
  output [63:0] io_resp_bits_data
);
`ifdef RANDOMIZE_REG_INIT
  reg [31:0] _RAND_0;
  reg [31:0] _RAND_1;
  reg [31:0] _RAND_2;
  reg [31:0] _RAND_3;
  reg [31:0] _RAND_4;
  reg [31:0] _RAND_5;
  reg [95:0] _RAND_6;
  reg [159:0] _RAND_7;
`endif // RANDOMIZE_REG_INIT
  reg [2:0] state; // @[Multiplier.scala 52:22]
  reg  req_dw; // @[Multiplier.scala 54:16]
  reg [6:0] count; // @[Multiplier.scala 55:18]
  reg  neg_out; // @[Multiplier.scala 58:20]
  reg  isHi; // @[Multiplier.scala 59:17]
  reg  resHi; // @[Multiplier.scala 60:18]
  reg [64:0] divisor; // @[Multiplier.scala 61:20]
  reg [129:0] remainder; // @[Multiplier.scala 62:22]
  wire [3:0] _T = io_req_bits_fn & 4'h4; // @[Decode.scala 14:65]
  wire  cmdMul = _T == 4'h0; // @[Decode.scala 14:121]
  wire [3:0] _T_3 = io_req_bits_fn & 4'h5; // @[Decode.scala 14:65]
  wire  _T_4 = _T_3 == 4'h1; // @[Decode.scala 14:121]
  wire [3:0] _T_5 = io_req_bits_fn & 4'h2; // @[Decode.scala 14:65]
  wire  _T_6 = _T_5 == 4'h2; // @[Decode.scala 14:121]
  wire  cmdHi = _T_4 | _T_6; // @[Decode.scala 15:30]
  wire [3:0] _T_9 = io_req_bits_fn & 4'h6; // @[Decode.scala 14:65]
  wire  _T_10 = _T_9 == 4'h0; // @[Decode.scala 14:121]
  wire [3:0] _T_11 = io_req_bits_fn & 4'h1; // @[Decode.scala 14:65]
  wire  _T_12 = _T_11 == 4'h0; // @[Decode.scala 14:121]
  wire  lhsSigned = _T_10 | _T_12; // @[Decode.scala 15:30]
  wire  _T_16 = _T_3 == 4'h4; // @[Decode.scala 14:121]
  wire  rhsSigned = _T_10 | _T_16; // @[Decode.scala 15:30]
  wire  _T_19 = ~io_req_bits_dw; // @[Multiplier.scala 79:60]
  wire  _sign_T_2 = _T_19 ? io_req_bits_in1[31] : io_req_bits_in1[63]; // @[Multiplier.scala 82:29]
  wire  lhs_sign = lhsSigned & _sign_T_2; // @[Multiplier.scala 82:23]
  wire [31:0] _hi_T_1 = lhs_sign ? 32'hffffffff : 32'h0; // @[Bitwise.scala 72:12]
  wire [31:0] hi = _T_19 ? _hi_T_1 : io_req_bits_in1[63:32]; // @[Multiplier.scala 83:17]
  wire [31:0] lo = io_req_bits_in1[31:0]; // @[Multiplier.scala 84:15]
  wire [63:0] lhs_in = {hi,lo}; // @[Cat.scala 30:58]
  wire  _sign_T_5 = _T_19 ? io_req_bits_in2[31] : io_req_bits_in2[63]; // @[Multiplier.scala 82:29]
  wire  rhs_sign = rhsSigned & _sign_T_5; // @[Multiplier.scala 82:23]
  wire [31:0] _hi_T_4 = rhs_sign ? 32'hffffffff : 32'h0; // @[Bitwise.scala 72:12]
  wire [31:0] hi_1 = _T_19 ? _hi_T_4 : io_req_bits_in2[63:32]; // @[Multiplier.scala 83:17]
  wire [31:0] lo_1 = io_req_bits_in2[31:0]; // @[Multiplier.scala 84:15]
  wire [64:0] subtractor = remainder[128:64] - divisor; // @[Multiplier.scala 89:37]
  wire [63:0] result = resHi ? remainder[128:65] : remainder[63:0]; // @[Multiplier.scala 90:19]
  wire [63:0] negated_remainder = 64'h0 - result; // @[Multiplier.scala 91:27]
  wire [129:0] _GEN_0 = remainder[63] ? {{66'd0}, negated_remainder} : remainder; // @[Multiplier.scala 94:27 Multiplier.scala 95:17 Multiplier.scala 62:22]
  wire [129:0] _GEN_2 = state == 3'h1 ? _GEN_0 : remainder; // @[Multiplier.scala 93:57 Multiplier.scala 62:22]
  wire [2:0] _GEN_4 = state == 3'h1 ? 3'h3 : state; // @[Multiplier.scala 93:57 Multiplier.scala 100:11 Multiplier.scala 52:22]
  wire [2:0] _GEN_6 = state == 3'h5 ? 3'h7 : _GEN_4; // @[Multiplier.scala 102:57 Multiplier.scala 104:11]
  wire  _GEN_7 = state == 3'h5 ? 1'h0 : resHi; // @[Multiplier.scala 102:57 Multiplier.scala 105:11 Multiplier.scala 60:18]
  wire [64:0] mulReg_hi = remainder[129:65]; // @[Multiplier.scala 108:31]
  wire [128:0] mulReg = {mulReg_hi,remainder[63:0]}; // @[Cat.scala 30:58]
  wire  prod_hi = remainder[64]; // @[Multiplier.scala 109:31]
  wire [63:0] mplier = mulReg[63:0]; // @[Multiplier.scala 110:24]
  wire [64:0] accum = mulReg[128:64]; // @[Multiplier.scala 111:37]
  wire  prod_lo = mplier[0]; // @[Multiplier.scala 113:38]
  wire [1:0] _prod_T_1 = {prod_hi,prod_lo}; // @[Multiplier.scala 113:60]
  wire [64:0] _GEN_37 = {{63{_prod_T_1[1]}},_prod_T_1}; // @[Multiplier.scala 113:67]
  wire [66:0] _prod_T_2 = $signed(_GEN_37) * $signed(divisor); // @[Multiplier.scala 113:67]
  wire [66:0] _GEN_38 = {{2{accum[64]}},accum}; // @[Multiplier.scala 113:76]
  wire [62:0] nextMulReg_lo = mplier[63:1]; // @[Multiplier.scala 114:38]
  wire [66:0] nextMulReg_hi = $signed(_prod_T_2) + $signed(_GEN_38); // @[Cat.scala 30:58]
  wire [129:0] nextMulReg = {nextMulReg_hi,nextMulReg_lo}; // @[Cat.scala 30:58]
  wire  remainder_hi_lo = count == 7'h3e & neg_out; // @[Multiplier.scala 115:57]
  wire  _eOut_T_4 = ~isHi; // @[Multiplier.scala 119:7]
  wire [64:0] nextMulReg1_hi = nextMulReg[128:64]; // @[Multiplier.scala 121:37]
  wire [63:0] nextMulReg1_lo = nextMulReg[63:0]; // @[Multiplier.scala 121:82]
  wire [128:0] nextMulReg1 = {nextMulReg1_hi,nextMulReg1_lo}; // @[Cat.scala 30:58]
  wire [64:0] remainder_hi_hi = nextMulReg1[128:64]; // @[Multiplier.scala 122:34]
  wire [63:0] remainder_lo = nextMulReg1[63:0]; // @[Multiplier.scala 122:67]
  wire [129:0] _remainder_T = {remainder_hi_hi,remainder_hi_lo,remainder_lo}; // @[Cat.scala 30:58]
  wire [6:0] _count_T_1 = count + 7'h1; // @[Multiplier.scala 124:20]
  wire [2:0] _GEN_8 = count == 7'h3f ? 3'h6 : _GEN_6; // @[Multiplier.scala 125:51 Multiplier.scala 126:13]
  wire  _GEN_9 = count == 7'h3f ? isHi : _GEN_7; // @[Multiplier.scala 125:51 Multiplier.scala 127:13]
  wire [2:0] _GEN_12 = state == 3'h2 ? _GEN_8 : _GEN_6; // @[Multiplier.scala 107:50]
  wire  _GEN_13 = state == 3'h2 ? _GEN_9 : _GEN_7; // @[Multiplier.scala 107:50]
  wire  unrolls_less = subtractor[64]; // @[Multiplier.scala 134:28]
  wire [63:0] unrolls_hi_hi = unrolls_less ? remainder[127:64] : subtractor[63:0]; // @[Multiplier.scala 135:14]
  wire  unrolls_lo = ~unrolls_less; // @[Multiplier.scala 135:67]
  wire [128:0] unrolls_0 = {unrolls_hi_hi,remainder[63:0],unrolls_lo}; // @[Cat.scala 30:58]
  wire [2:0] _state_T = neg_out ? 3'h5 : 3'h7; // @[Multiplier.scala 140:19]
  wire [2:0] _GEN_14 = count == 7'h40 ? _state_T : _GEN_12; // @[Multiplier.scala 139:38 Multiplier.scala 140:13]
  wire  _divby0_T = count == 7'h0; // @[Multiplier.scala 147:24]
  wire  divby0 = count == 7'h0 & unrolls_lo; // @[Multiplier.scala 147:30]
  wire [31:0] divisorMSB_hi = divisor[63:32]; // @[CircuitMath.scala 35:17]
  wire [31:0] divisorMSB_lo = divisor[31:0]; // @[CircuitMath.scala 36:17]
  wire  divisorMSB_hi_1 = |divisorMSB_hi; // @[CircuitMath.scala 37:22]
  wire [15:0] divisorMSB_hi_2 = divisorMSB_hi[31:16]; // @[CircuitMath.scala 35:17]
  wire [15:0] divisorMSB_lo_1 = divisorMSB_hi[15:0]; // @[CircuitMath.scala 36:17]
  wire  divisorMSB_hi_3 = |divisorMSB_hi_2; // @[CircuitMath.scala 37:22]
  wire [7:0] divisorMSB_hi_4 = divisorMSB_hi_2[15:8]; // @[CircuitMath.scala 35:17]
  wire [7:0] divisorMSB_lo_2 = divisorMSB_hi_2[7:0]; // @[CircuitMath.scala 36:17]
  wire  divisorMSB_hi_5 = |divisorMSB_hi_4; // @[CircuitMath.scala 37:22]
  wire [3:0] divisorMSB_hi_6 = divisorMSB_hi_4[7:4]; // @[CircuitMath.scala 35:17]
  wire [3:0] divisorMSB_lo_3 = divisorMSB_hi_4[3:0]; // @[CircuitMath.scala 36:17]
  wire  divisorMSB_hi_7 = |divisorMSB_hi_6; // @[CircuitMath.scala 37:22]
  wire [1:0] _divisorMSB_T_4 = divisorMSB_hi_6[2] ? 2'h2 : {{1'd0}, divisorMSB_hi_6[1]}; // @[CircuitMath.scala 32:10]
  wire [1:0] _divisorMSB_T_5 = divisorMSB_hi_6[3] ? 2'h3 : _divisorMSB_T_4; // @[CircuitMath.scala 32:10]
  wire [1:0] _divisorMSB_T_9 = divisorMSB_lo_3[2] ? 2'h2 : {{1'd0}, divisorMSB_lo_3[1]}; // @[CircuitMath.scala 32:10]
  wire [1:0] _divisorMSB_T_10 = divisorMSB_lo_3[3] ? 2'h3 : _divisorMSB_T_9; // @[CircuitMath.scala 32:10]
  wire [1:0] divisorMSB_lo_4 = divisorMSB_hi_7 ? _divisorMSB_T_5 : _divisorMSB_T_10; // @[CircuitMath.scala 38:21]
  wire [2:0] _divisorMSB_T_11 = {divisorMSB_hi_7,divisorMSB_lo_4}; // @[Cat.scala 30:58]
  wire [3:0] divisorMSB_hi_8 = divisorMSB_lo_2[7:4]; // @[CircuitMath.scala 35:17]
  wire [3:0] divisorMSB_lo_5 = divisorMSB_lo_2[3:0]; // @[CircuitMath.scala 36:17]
  wire  divisorMSB_hi_9 = |divisorMSB_hi_8; // @[CircuitMath.scala 37:22]
  wire [1:0] _divisorMSB_T_15 = divisorMSB_hi_8[2] ? 2'h2 : {{1'd0}, divisorMSB_hi_8[1]}; // @[CircuitMath.scala 32:10]
  wire [1:0] _divisorMSB_T_16 = divisorMSB_hi_8[3] ? 2'h3 : _divisorMSB_T_15; // @[CircuitMath.scala 32:10]
  wire [1:0] _divisorMSB_T_20 = divisorMSB_lo_5[2] ? 2'h2 : {{1'd0}, divisorMSB_lo_5[1]}; // @[CircuitMath.scala 32:10]
  wire [1:0] _divisorMSB_T_21 = divisorMSB_lo_5[3] ? 2'h3 : _divisorMSB_T_20; // @[CircuitMath.scala 32:10]
  wire [1:0] divisorMSB_lo_6 = divisorMSB_hi_9 ? _divisorMSB_T_16 : _divisorMSB_T_21; // @[CircuitMath.scala 38:21]
  wire [2:0] _divisorMSB_T_22 = {divisorMSB_hi_9,divisorMSB_lo_6}; // @[Cat.scala 30:58]
  wire [2:0] divisorMSB_lo_7 = divisorMSB_hi_5 ? _divisorMSB_T_11 : _divisorMSB_T_22; // @[CircuitMath.scala 38:21]
  wire [3:0] _divisorMSB_T_23 = {divisorMSB_hi_5,divisorMSB_lo_7}; // @[Cat.scala 30:58]
  wire [7:0] divisorMSB_hi_10 = divisorMSB_lo_1[15:8]; // @[CircuitMath.scala 35:17]
  wire [7:0] divisorMSB_lo_8 = divisorMSB_lo_1[7:0]; // @[CircuitMath.scala 36:17]
  wire  divisorMSB_hi_11 = |divisorMSB_hi_10; // @[CircuitMath.scala 37:22]
  wire [3:0] divisorMSB_hi_12 = divisorMSB_hi_10[7:4]; // @[CircuitMath.scala 35:17]
  wire [3:0] divisorMSB_lo_9 = divisorMSB_hi_10[3:0]; // @[CircuitMath.scala 36:17]
  wire  divisorMSB_hi_13 = |divisorMSB_hi_12; // @[CircuitMath.scala 37:22]
  wire [1:0] _divisorMSB_T_27 = divisorMSB_hi_12[2] ? 2'h2 : {{1'd0}, divisorMSB_hi_12[1]}; // @[CircuitMath.scala 32:10]
  wire [1:0] _divisorMSB_T_28 = divisorMSB_hi_12[3] ? 2'h3 : _divisorMSB_T_27; // @[CircuitMath.scala 32:10]
  wire [1:0] _divisorMSB_T_32 = divisorMSB_lo_9[2] ? 2'h2 : {{1'd0}, divisorMSB_lo_9[1]}; // @[CircuitMath.scala 32:10]
  wire [1:0] _divisorMSB_T_33 = divisorMSB_lo_9[3] ? 2'h3 : _divisorMSB_T_32; // @[CircuitMath.scala 32:10]
  wire [1:0] divisorMSB_lo_10 = divisorMSB_hi_13 ? _divisorMSB_T_28 : _divisorMSB_T_33; // @[CircuitMath.scala 38:21]
  wire [2:0] _divisorMSB_T_34 = {divisorMSB_hi_13,divisorMSB_lo_10}; // @[Cat.scala 30:58]
  wire [3:0] divisorMSB_hi_14 = divisorMSB_lo_8[7:4]; // @[CircuitMath.scala 35:17]
  wire [3:0] divisorMSB_lo_11 = divisorMSB_lo_8[3:0]; // @[CircuitMath.scala 36:17]
  wire  divisorMSB_hi_15 = |divisorMSB_hi_14; // @[CircuitMath.scala 37:22]
  wire [1:0] _divisorMSB_T_38 = divisorMSB_hi_14[2] ? 2'h2 : {{1'd0}, divisorMSB_hi_14[1]}; // @[CircuitMath.scala 32:10]
  wire [1:0] _divisorMSB_T_39 = divisorMSB_hi_14[3] ? 2'h3 : _divisorMSB_T_38; // @[CircuitMath.scala 32:10]
  wire [1:0] _divisorMSB_T_43 = divisorMSB_lo_11[2] ? 2'h2 : {{1'd0}, divisorMSB_lo_11[1]}; // @[CircuitMath.scala 32:10]
  wire [1:0] _divisorMSB_T_44 = divisorMSB_lo_11[3] ? 2'h3 : _divisorMSB_T_43; // @[CircuitMath.scala 32:10]
  wire [1:0] divisorMSB_lo_12 = divisorMSB_hi_15 ? _divisorMSB_T_39 : _divisorMSB_T_44; // @[CircuitMath.scala 38:21]
  wire [2:0] _divisorMSB_T_45 = {divisorMSB_hi_15,divisorMSB_lo_12}; // @[Cat.scala 30:58]
  wire [2:0] divisorMSB_lo_13 = divisorMSB_hi_11 ? _divisorMSB_T_34 : _divisorMSB_T_45; // @[CircuitMath.scala 38:21]
  wire [3:0] _divisorMSB_T_46 = {divisorMSB_hi_11,divisorMSB_lo_13}; // @[Cat.scala 30:58]
  wire [3:0] divisorMSB_lo_14 = divisorMSB_hi_3 ? _divisorMSB_T_23 : _divisorMSB_T_46; // @[CircuitMath.scala 38:21]
  wire [4:0] _divisorMSB_T_47 = {divisorMSB_hi_3,divisorMSB_lo_14}; // @[Cat.scala 30:58]
  wire [15:0] divisorMSB_hi_16 = divisorMSB_lo[31:16]; // @[CircuitMath.scala 35:17]
  wire [15:0] divisorMSB_lo_15 = divisorMSB_lo[15:0]; // @[CircuitMath.scala 36:17]
  wire  divisorMSB_hi_17 = |divisorMSB_hi_16; // @[CircuitMath.scala 37:22]
  wire [7:0] divisorMSB_hi_18 = divisorMSB_hi_16[15:8]; // @[CircuitMath.scala 35:17]
  wire [7:0] divisorMSB_lo_16 = divisorMSB_hi_16[7:0]; // @[CircuitMath.scala 36:17]
  wire  divisorMSB_hi_19 = |divisorMSB_hi_18; // @[CircuitMath.scala 37:22]
  wire [3:0] divisorMSB_hi_20 = divisorMSB_hi_18[7:4]; // @[CircuitMath.scala 35:17]
  wire [3:0] divisorMSB_lo_17 = divisorMSB_hi_18[3:0]; // @[CircuitMath.scala 36:17]
  wire  divisorMSB_hi_21 = |divisorMSB_hi_20; // @[CircuitMath.scala 37:22]
  wire [1:0] _divisorMSB_T_51 = divisorMSB_hi_20[2] ? 2'h2 : {{1'd0}, divisorMSB_hi_20[1]}; // @[CircuitMath.scala 32:10]
  wire [1:0] _divisorMSB_T_52 = divisorMSB_hi_20[3] ? 2'h3 : _divisorMSB_T_51; // @[CircuitMath.scala 32:10]
  wire [1:0] _divisorMSB_T_56 = divisorMSB_lo_17[2] ? 2'h2 : {{1'd0}, divisorMSB_lo_17[1]}; // @[CircuitMath.scala 32:10]
  wire [1:0] _divisorMSB_T_57 = divisorMSB_lo_17[3] ? 2'h3 : _divisorMSB_T_56; // @[CircuitMath.scala 32:10]
  wire [1:0] divisorMSB_lo_18 = divisorMSB_hi_21 ? _divisorMSB_T_52 : _divisorMSB_T_57; // @[CircuitMath.scala 38:21]
  wire [2:0] _divisorMSB_T_58 = {divisorMSB_hi_21,divisorMSB_lo_18}; // @[Cat.scala 30:58]
  wire [3:0] divisorMSB_hi_22 = divisorMSB_lo_16[7:4]; // @[CircuitMath.scala 35:17]
  wire [3:0] divisorMSB_lo_19 = divisorMSB_lo_16[3:0]; // @[CircuitMath.scala 36:17]
  wire  divisorMSB_hi_23 = |divisorMSB_hi_22; // @[CircuitMath.scala 37:22]
  wire [1:0] _divisorMSB_T_62 = divisorMSB_hi_22[2] ? 2'h2 : {{1'd0}, divisorMSB_hi_22[1]}; // @[CircuitMath.scala 32:10]
  wire [1:0] _divisorMSB_T_63 = divisorMSB_hi_22[3] ? 2'h3 : _divisorMSB_T_62; // @[CircuitMath.scala 32:10]
  wire [1:0] _divisorMSB_T_67 = divisorMSB_lo_19[2] ? 2'h2 : {{1'd0}, divisorMSB_lo_19[1]}; // @[CircuitMath.scala 32:10]
  wire [1:0] _divisorMSB_T_68 = divisorMSB_lo_19[3] ? 2'h3 : _divisorMSB_T_67; // @[CircuitMath.scala 32:10]
  wire [1:0] divisorMSB_lo_20 = divisorMSB_hi_23 ? _divisorMSB_T_63 : _divisorMSB_T_68; // @[CircuitMath.scala 38:21]
  wire [2:0] _divisorMSB_T_69 = {divisorMSB_hi_23,divisorMSB_lo_20}; // @[Cat.scala 30:58]
  wire [2:0] divisorMSB_lo_21 = divisorMSB_hi_19 ? _divisorMSB_T_58 : _divisorMSB_T_69; // @[CircuitMath.scala 38:21]
  wire [3:0] _divisorMSB_T_70 = {divisorMSB_hi_19,divisorMSB_lo_21}; // @[Cat.scala 30:58]
  wire [7:0] divisorMSB_hi_24 = divisorMSB_lo_15[15:8]; // @[CircuitMath.scala 35:17]
  wire [7:0] divisorMSB_lo_22 = divisorMSB_lo_15[7:0]; // @[CircuitMath.scala 36:17]
  wire  divisorMSB_hi_25 = |divisorMSB_hi_24; // @[CircuitMath.scala 37:22]
  wire [3:0] divisorMSB_hi_26 = divisorMSB_hi_24[7:4]; // @[CircuitMath.scala 35:17]
  wire [3:0] divisorMSB_lo_23 = divisorMSB_hi_24[3:0]; // @[CircuitMath.scala 36:17]
  wire  divisorMSB_hi_27 = |divisorMSB_hi_26; // @[CircuitMath.scala 37:22]
  wire [1:0] _divisorMSB_T_74 = divisorMSB_hi_26[2] ? 2'h2 : {{1'd0}, divisorMSB_hi_26[1]}; // @[CircuitMath.scala 32:10]
  wire [1:0] _divisorMSB_T_75 = divisorMSB_hi_26[3] ? 2'h3 : _divisorMSB_T_74; // @[CircuitMath.scala 32:10]
  wire [1:0] _divisorMSB_T_79 = divisorMSB_lo_23[2] ? 2'h2 : {{1'd0}, divisorMSB_lo_23[1]}; // @[CircuitMath.scala 32:10]
  wire [1:0] _divisorMSB_T_80 = divisorMSB_lo_23[3] ? 2'h3 : _divisorMSB_T_79; // @[CircuitMath.scala 32:10]
  wire [1:0] divisorMSB_lo_24 = divisorMSB_hi_27 ? _divisorMSB_T_75 : _divisorMSB_T_80; // @[CircuitMath.scala 38:21]
  wire [2:0] _divisorMSB_T_81 = {divisorMSB_hi_27,divisorMSB_lo_24}; // @[Cat.scala 30:58]
  wire [3:0] divisorMSB_hi_28 = divisorMSB_lo_22[7:4]; // @[CircuitMath.scala 35:17]
  wire [3:0] divisorMSB_lo_25 = divisorMSB_lo_22[3:0]; // @[CircuitMath.scala 36:17]
  wire  divisorMSB_hi_29 = |divisorMSB_hi_28; // @[CircuitMath.scala 37:22]
  wire [1:0] _divisorMSB_T_85 = divisorMSB_hi_28[2] ? 2'h2 : {{1'd0}, divisorMSB_hi_28[1]}; // @[CircuitMath.scala 32:10]
  wire [1:0] _divisorMSB_T_86 = divisorMSB_hi_28[3] ? 2'h3 : _divisorMSB_T_85; // @[CircuitMath.scala 32:10]
  wire [1:0] _divisorMSB_T_90 = divisorMSB_lo_25[2] ? 2'h2 : {{1'd0}, divisorMSB_lo_25[1]}; // @[CircuitMath.scala 32:10]
  wire [1:0] _divisorMSB_T_91 = divisorMSB_lo_25[3] ? 2'h3 : _divisorMSB_T_90; // @[CircuitMath.scala 32:10]
  wire [1:0] divisorMSB_lo_26 = divisorMSB_hi_29 ? _divisorMSB_T_86 : _divisorMSB_T_91; // @[CircuitMath.scala 38:21]
  wire [2:0] _divisorMSB_T_92 = {divisorMSB_hi_29,divisorMSB_lo_26}; // @[Cat.scala 30:58]
  wire [2:0] divisorMSB_lo_27 = divisorMSB_hi_25 ? _divisorMSB_T_81 : _divisorMSB_T_92; // @[CircuitMath.scala 38:21]
  wire [3:0] _divisorMSB_T_93 = {divisorMSB_hi_25,divisorMSB_lo_27}; // @[Cat.scala 30:58]
  wire [3:0] divisorMSB_lo_28 = divisorMSB_hi_17 ? _divisorMSB_T_70 : _divisorMSB_T_93; // @[CircuitMath.scala 38:21]
  wire [4:0] _divisorMSB_T_94 = {divisorMSB_hi_17,divisorMSB_lo_28}; // @[Cat.scala 30:58]
  wire [4:0] divisorMSB_lo_29 = divisorMSB_hi_1 ? _divisorMSB_T_47 : _divisorMSB_T_94; // @[CircuitMath.scala 38:21]
  wire [5:0] divisorMSB = {divisorMSB_hi_1,divisorMSB_lo_29}; // @[Cat.scala 30:58]
  wire [31:0] dividendMSB_hi = remainder[63:32]; // @[CircuitMath.scala 35:17]
  wire [31:0] dividendMSB_lo = remainder[31:0]; // @[CircuitMath.scala 36:17]
  wire  dividendMSB_hi_1 = |dividendMSB_hi; // @[CircuitMath.scala 37:22]
  wire [15:0] dividendMSB_hi_2 = dividendMSB_hi[31:16]; // @[CircuitMath.scala 35:17]
  wire [15:0] dividendMSB_lo_1 = dividendMSB_hi[15:0]; // @[CircuitMath.scala 36:17]
  wire  dividendMSB_hi_3 = |dividendMSB_hi_2; // @[CircuitMath.scala 37:22]
  wire [7:0] dividendMSB_hi_4 = dividendMSB_hi_2[15:8]; // @[CircuitMath.scala 35:17]
  wire [7:0] dividendMSB_lo_2 = dividendMSB_hi_2[7:0]; // @[CircuitMath.scala 36:17]
  wire  dividendMSB_hi_5 = |dividendMSB_hi_4; // @[CircuitMath.scala 37:22]
  wire [3:0] dividendMSB_hi_6 = dividendMSB_hi_4[7:4]; // @[CircuitMath.scala 35:17]
  wire [3:0] dividendMSB_lo_3 = dividendMSB_hi_4[3:0]; // @[CircuitMath.scala 36:17]
  wire  dividendMSB_hi_7 = |dividendMSB_hi_6; // @[CircuitMath.scala 37:22]
  wire [1:0] _dividendMSB_T_4 = dividendMSB_hi_6[2] ? 2'h2 : {{1'd0}, dividendMSB_hi_6[1]}; // @[CircuitMath.scala 32:10]
  wire [1:0] _dividendMSB_T_5 = dividendMSB_hi_6[3] ? 2'h3 : _dividendMSB_T_4; // @[CircuitMath.scala 32:10]
  wire [1:0] _dividendMSB_T_9 = dividendMSB_lo_3[2] ? 2'h2 : {{1'd0}, dividendMSB_lo_3[1]}; // @[CircuitMath.scala 32:10]
  wire [1:0] _dividendMSB_T_10 = dividendMSB_lo_3[3] ? 2'h3 : _dividendMSB_T_9; // @[CircuitMath.scala 32:10]
  wire [1:0] dividendMSB_lo_4 = dividendMSB_hi_7 ? _dividendMSB_T_5 : _dividendMSB_T_10; // @[CircuitMath.scala 38:21]
  wire [2:0] _dividendMSB_T_11 = {dividendMSB_hi_7,dividendMSB_lo_4}; // @[Cat.scala 30:58]
  wire [3:0] dividendMSB_hi_8 = dividendMSB_lo_2[7:4]; // @[CircuitMath.scala 35:17]
  wire [3:0] dividendMSB_lo_5 = dividendMSB_lo_2[3:0]; // @[CircuitMath.scala 36:17]
  wire  dividendMSB_hi_9 = |dividendMSB_hi_8; // @[CircuitMath.scala 37:22]
  wire [1:0] _dividendMSB_T_15 = dividendMSB_hi_8[2] ? 2'h2 : {{1'd0}, dividendMSB_hi_8[1]}; // @[CircuitMath.scala 32:10]
  wire [1:0] _dividendMSB_T_16 = dividendMSB_hi_8[3] ? 2'h3 : _dividendMSB_T_15; // @[CircuitMath.scala 32:10]
  wire [1:0] _dividendMSB_T_20 = dividendMSB_lo_5[2] ? 2'h2 : {{1'd0}, dividendMSB_lo_5[1]}; // @[CircuitMath.scala 32:10]
  wire [1:0] _dividendMSB_T_21 = dividendMSB_lo_5[3] ? 2'h3 : _dividendMSB_T_20; // @[CircuitMath.scala 32:10]
  wire [1:0] dividendMSB_lo_6 = dividendMSB_hi_9 ? _dividendMSB_T_16 : _dividendMSB_T_21; // @[CircuitMath.scala 38:21]
  wire [2:0] _dividendMSB_T_22 = {dividendMSB_hi_9,dividendMSB_lo_6}; // @[Cat.scala 30:58]
  wire [2:0] dividendMSB_lo_7 = dividendMSB_hi_5 ? _dividendMSB_T_11 : _dividendMSB_T_22; // @[CircuitMath.scala 38:21]
  wire [3:0] _dividendMSB_T_23 = {dividendMSB_hi_5,dividendMSB_lo_7}; // @[Cat.scala 30:58]
  wire [7:0] dividendMSB_hi_10 = dividendMSB_lo_1[15:8]; // @[CircuitMath.scala 35:17]
  wire [7:0] dividendMSB_lo_8 = dividendMSB_lo_1[7:0]; // @[CircuitMath.scala 36:17]
  wire  dividendMSB_hi_11 = |dividendMSB_hi_10; // @[CircuitMath.scala 37:22]
  wire [3:0] dividendMSB_hi_12 = dividendMSB_hi_10[7:4]; // @[CircuitMath.scala 35:17]
  wire [3:0] dividendMSB_lo_9 = dividendMSB_hi_10[3:0]; // @[CircuitMath.scala 36:17]
  wire  dividendMSB_hi_13 = |dividendMSB_hi_12; // @[CircuitMath.scala 37:22]
  wire [1:0] _dividendMSB_T_27 = dividendMSB_hi_12[2] ? 2'h2 : {{1'd0}, dividendMSB_hi_12[1]}; // @[CircuitMath.scala 32:10]
  wire [1:0] _dividendMSB_T_28 = dividendMSB_hi_12[3] ? 2'h3 : _dividendMSB_T_27; // @[CircuitMath.scala 32:10]
  wire [1:0] _dividendMSB_T_32 = dividendMSB_lo_9[2] ? 2'h2 : {{1'd0}, dividendMSB_lo_9[1]}; // @[CircuitMath.scala 32:10]
  wire [1:0] _dividendMSB_T_33 = dividendMSB_lo_9[3] ? 2'h3 : _dividendMSB_T_32; // @[CircuitMath.scala 32:10]
  wire [1:0] dividendMSB_lo_10 = dividendMSB_hi_13 ? _dividendMSB_T_28 : _dividendMSB_T_33; // @[CircuitMath.scala 38:21]
  wire [2:0] _dividendMSB_T_34 = {dividendMSB_hi_13,dividendMSB_lo_10}; // @[Cat.scala 30:58]
  wire [3:0] dividendMSB_hi_14 = dividendMSB_lo_8[7:4]; // @[CircuitMath.scala 35:17]
  wire [3:0] dividendMSB_lo_11 = dividendMSB_lo_8[3:0]; // @[CircuitMath.scala 36:17]
  wire  dividendMSB_hi_15 = |dividendMSB_hi_14; // @[CircuitMath.scala 37:22]
  wire [1:0] _dividendMSB_T_38 = dividendMSB_hi_14[2] ? 2'h2 : {{1'd0}, dividendMSB_hi_14[1]}; // @[CircuitMath.scala 32:10]
  wire [1:0] _dividendMSB_T_39 = dividendMSB_hi_14[3] ? 2'h3 : _dividendMSB_T_38; // @[CircuitMath.scala 32:10]
  wire [1:0] _dividendMSB_T_43 = dividendMSB_lo_11[2] ? 2'h2 : {{1'd0}, dividendMSB_lo_11[1]}; // @[CircuitMath.scala 32:10]
  wire [1:0] _dividendMSB_T_44 = dividendMSB_lo_11[3] ? 2'h3 : _dividendMSB_T_43; // @[CircuitMath.scala 32:10]
  wire [1:0] dividendMSB_lo_12 = dividendMSB_hi_15 ? _dividendMSB_T_39 : _dividendMSB_T_44; // @[CircuitMath.scala 38:21]
  wire [2:0] _dividendMSB_T_45 = {dividendMSB_hi_15,dividendMSB_lo_12}; // @[Cat.scala 30:58]
  wire [2:0] dividendMSB_lo_13 = dividendMSB_hi_11 ? _dividendMSB_T_34 : _dividendMSB_T_45; // @[CircuitMath.scala 38:21]
  wire [3:0] _dividendMSB_T_46 = {dividendMSB_hi_11,dividendMSB_lo_13}; // @[Cat.scala 30:58]
  wire [3:0] dividendMSB_lo_14 = dividendMSB_hi_3 ? _dividendMSB_T_23 : _dividendMSB_T_46; // @[CircuitMath.scala 38:21]
  wire [4:0] _dividendMSB_T_47 = {dividendMSB_hi_3,dividendMSB_lo_14}; // @[Cat.scala 30:58]
  wire [15:0] dividendMSB_hi_16 = dividendMSB_lo[31:16]; // @[CircuitMath.scala 35:17]
  wire [15:0] dividendMSB_lo_15 = dividendMSB_lo[15:0]; // @[CircuitMath.scala 36:17]
  wire  dividendMSB_hi_17 = |dividendMSB_hi_16; // @[CircuitMath.scala 37:22]
  wire [7:0] dividendMSB_hi_18 = dividendMSB_hi_16[15:8]; // @[CircuitMath.scala 35:17]
  wire [7:0] dividendMSB_lo_16 = dividendMSB_hi_16[7:0]; // @[CircuitMath.scala 36:17]
  wire  dividendMSB_hi_19 = |dividendMSB_hi_18; // @[CircuitMath.scala 37:22]
  wire [3:0] dividendMSB_hi_20 = dividendMSB_hi_18[7:4]; // @[CircuitMath.scala 35:17]
  wire [3:0] dividendMSB_lo_17 = dividendMSB_hi_18[3:0]; // @[CircuitMath.scala 36:17]
  wire  dividendMSB_hi_21 = |dividendMSB_hi_20; // @[CircuitMath.scala 37:22]
  wire [1:0] _dividendMSB_T_51 = dividendMSB_hi_20[2] ? 2'h2 : {{1'd0}, dividendMSB_hi_20[1]}; // @[CircuitMath.scala 32:10]
  wire [1:0] _dividendMSB_T_52 = dividendMSB_hi_20[3] ? 2'h3 : _dividendMSB_T_51; // @[CircuitMath.scala 32:10]
  wire [1:0] _dividendMSB_T_56 = dividendMSB_lo_17[2] ? 2'h2 : {{1'd0}, dividendMSB_lo_17[1]}; // @[CircuitMath.scala 32:10]
  wire [1:0] _dividendMSB_T_57 = dividendMSB_lo_17[3] ? 2'h3 : _dividendMSB_T_56; // @[CircuitMath.scala 32:10]
  wire [1:0] dividendMSB_lo_18 = dividendMSB_hi_21 ? _dividendMSB_T_52 : _dividendMSB_T_57; // @[CircuitMath.scala 38:21]
  wire [2:0] _dividendMSB_T_58 = {dividendMSB_hi_21,dividendMSB_lo_18}; // @[Cat.scala 30:58]
  wire [3:0] dividendMSB_hi_22 = dividendMSB_lo_16[7:4]; // @[CircuitMath.scala 35:17]
  wire [3:0] dividendMSB_lo_19 = dividendMSB_lo_16[3:0]; // @[CircuitMath.scala 36:17]
  wire  dividendMSB_hi_23 = |dividendMSB_hi_22; // @[CircuitMath.scala 37:22]
  wire [1:0] _dividendMSB_T_62 = dividendMSB_hi_22[2] ? 2'h2 : {{1'd0}, dividendMSB_hi_22[1]}; // @[CircuitMath.scala 32:10]
  wire [1:0] _dividendMSB_T_63 = dividendMSB_hi_22[3] ? 2'h3 : _dividendMSB_T_62; // @[CircuitMath.scala 32:10]
  wire [1:0] _dividendMSB_T_67 = dividendMSB_lo_19[2] ? 2'h2 : {{1'd0}, dividendMSB_lo_19[1]}; // @[CircuitMath.scala 32:10]
  wire [1:0] _dividendMSB_T_68 = dividendMSB_lo_19[3] ? 2'h3 : _dividendMSB_T_67; // @[CircuitMath.scala 32:10]
  wire [1:0] dividendMSB_lo_20 = dividendMSB_hi_23 ? _dividendMSB_T_63 : _dividendMSB_T_68; // @[CircuitMath.scala 38:21]
  wire [2:0] _dividendMSB_T_69 = {dividendMSB_hi_23,dividendMSB_lo_20}; // @[Cat.scala 30:58]
  wire [2:0] dividendMSB_lo_21 = dividendMSB_hi_19 ? _dividendMSB_T_58 : _dividendMSB_T_69; // @[CircuitMath.scala 38:21]
  wire [3:0] _dividendMSB_T_70 = {dividendMSB_hi_19,dividendMSB_lo_21}; // @[Cat.scala 30:58]
  wire [7:0] dividendMSB_hi_24 = dividendMSB_lo_15[15:8]; // @[CircuitMath.scala 35:17]
  wire [7:0] dividendMSB_lo_22 = dividendMSB_lo_15[7:0]; // @[CircuitMath.scala 36:17]
  wire  dividendMSB_hi_25 = |dividendMSB_hi_24; // @[CircuitMath.scala 37:22]
  wire [3:0] dividendMSB_hi_26 = dividendMSB_hi_24[7:4]; // @[CircuitMath.scala 35:17]
  wire [3:0] dividendMSB_lo_23 = dividendMSB_hi_24[3:0]; // @[CircuitMath.scala 36:17]
  wire  dividendMSB_hi_27 = |dividendMSB_hi_26; // @[CircuitMath.scala 37:22]
  wire [1:0] _dividendMSB_T_74 = dividendMSB_hi_26[2] ? 2'h2 : {{1'd0}, dividendMSB_hi_26[1]}; // @[CircuitMath.scala 32:10]
  wire [1:0] _dividendMSB_T_75 = dividendMSB_hi_26[3] ? 2'h3 : _dividendMSB_T_74; // @[CircuitMath.scala 32:10]
  wire [1:0] _dividendMSB_T_79 = dividendMSB_lo_23[2] ? 2'h2 : {{1'd0}, dividendMSB_lo_23[1]}; // @[CircuitMath.scala 32:10]
  wire [1:0] _dividendMSB_T_80 = dividendMSB_lo_23[3] ? 2'h3 : _dividendMSB_T_79; // @[CircuitMath.scala 32:10]
  wire [1:0] dividendMSB_lo_24 = dividendMSB_hi_27 ? _dividendMSB_T_75 : _dividendMSB_T_80; // @[CircuitMath.scala 38:21]
  wire [2:0] _dividendMSB_T_81 = {dividendMSB_hi_27,dividendMSB_lo_24}; // @[Cat.scala 30:58]
  wire [3:0] dividendMSB_hi_28 = dividendMSB_lo_22[7:4]; // @[CircuitMath.scala 35:17]
  wire [3:0] dividendMSB_lo_25 = dividendMSB_lo_22[3:0]; // @[CircuitMath.scala 36:17]
  wire  dividendMSB_hi_29 = |dividendMSB_hi_28; // @[CircuitMath.scala 37:22]
  wire [1:0] _dividendMSB_T_85 = dividendMSB_hi_28[2] ? 2'h2 : {{1'd0}, dividendMSB_hi_28[1]}; // @[CircuitMath.scala 32:10]
  wire [1:0] _dividendMSB_T_86 = dividendMSB_hi_28[3] ? 2'h3 : _dividendMSB_T_85; // @[CircuitMath.scala 32:10]
  wire [1:0] _dividendMSB_T_90 = dividendMSB_lo_25[2] ? 2'h2 : {{1'd0}, dividendMSB_lo_25[1]}; // @[CircuitMath.scala 32:10]
  wire [1:0] _dividendMSB_T_91 = dividendMSB_lo_25[3] ? 2'h3 : _dividendMSB_T_90; // @[CircuitMath.scala 32:10]
  wire [1:0] dividendMSB_lo_26 = dividendMSB_hi_29 ? _dividendMSB_T_86 : _dividendMSB_T_91; // @[CircuitMath.scala 38:21]
  wire [2:0] _dividendMSB_T_92 = {dividendMSB_hi_29,dividendMSB_lo_26}; // @[Cat.scala 30:58]
  wire [2:0] dividendMSB_lo_27 = dividendMSB_hi_25 ? _dividendMSB_T_81 : _dividendMSB_T_92; // @[CircuitMath.scala 38:21]
  wire [3:0] _dividendMSB_T_93 = {dividendMSB_hi_25,dividendMSB_lo_27}; // @[Cat.scala 30:58]
  wire [3:0] dividendMSB_lo_28 = dividendMSB_hi_17 ? _dividendMSB_T_70 : _dividendMSB_T_93; // @[CircuitMath.scala 38:21]
  wire [4:0] _dividendMSB_T_94 = {dividendMSB_hi_17,dividendMSB_lo_28}; // @[Cat.scala 30:58]
  wire [4:0] dividendMSB_lo_29 = dividendMSB_hi_1 ? _dividendMSB_T_47 : _dividendMSB_T_94; // @[CircuitMath.scala 38:21]
  wire [5:0] dividendMSB = {dividendMSB_hi_1,dividendMSB_lo_29}; // @[Cat.scala 30:58]
  wire [5:0] _eOutPos_T_1 = dividendMSB - divisorMSB; // @[Multiplier.scala 153:35]
  wire [5:0] eOutPos = ~_eOutPos_T_1; // @[Multiplier.scala 153:21]
  wire  eOut_1 = _divby0_T & ~divby0 & eOutPos >= 6'h1; // @[Multiplier.scala 154:41]
  wire [126:0] _GEN_39 = {{63'd0}, remainder[63:0]}; // @[Multiplier.scala 156:39]
  wire [126:0] _remainder_T_2 = _GEN_39 << eOutPos; // @[Multiplier.scala 156:39]
  wire [128:0] _GEN_16 = eOut_1 ? {{2'd0}, _remainder_T_2} : unrolls_0; // @[Multiplier.scala 155:19 Multiplier.scala 156:19 Multiplier.scala 138:15]
  wire  _T_34 = io_resp_ready & io_resp_valid; // @[Decoupled.scala 40:37]
  wire  _T_36 = io_req_ready & io_req_valid; // @[Decoupled.scala 40:37]
  wire [5:0] _count_T_8 = cmdMul & _T_19 ? 6'h20 : 6'h0; // @[Multiplier.scala 169:38]
  wire [64:0] _divisor_T = {rhs_sign,hi_1,lo_1}; // @[Cat.scala 30:58]
  wire [2:0] _outMul_T_1 = state & 3'h1; // @[Multiplier.scala 176:23]
  wire  outMul = _outMul_T_1 == 3'h0; // @[Multiplier.scala 176:52]
  wire  _loOut_T = ~req_dw; // @[Multiplier.scala 79:60]
  wire [31:0] loOut = _loOut_T & outMul ? result[63:32] : result[31:0]; // @[Multiplier.scala 177:18]
  wire [31:0] _hiOut_T_4 = loOut[31] ? 32'hffffffff : 32'h0; // @[Bitwise.scala 72:12]
  wire [31:0] hiOut = _loOut_T ? _hiOut_T_4 : result[63:32]; // @[Multiplier.scala 178:18]
  assign io_req_ready = state == 3'h0; // @[Multiplier.scala 183:25]
  assign io_resp_valid = state == 3'h6 | state == 3'h7; // @[Multiplier.scala 182:42]
  assign io_resp_bits_data = {hiOut,loOut}; // @[Cat.scala 30:58]
  always @(posedge clock) begin
    if (reset) begin // @[Multiplier.scala 52:22]
      state <= 3'h0; // @[Multiplier.scala 52:22]
    end else if (_T_36) begin // @[Multiplier.scala 165:24]
      if (cmdMul) begin // @[Multiplier.scala 166:17]
        state <= 3'h2;
      end else if (lhs_sign | rhs_sign) begin // @[Multiplier.scala 166:36]
        state <= 3'h1;
      end else begin
        state <= 3'h3;
      end
    end else if (_T_34 | io_kill) begin // @[Multiplier.scala 162:36]
      state <= 3'h0; // @[Multiplier.scala 163:11]
    end else if (state == 3'h3) begin // @[Multiplier.scala 130:50]
      state <= _GEN_14;
    end else begin
      state <= _GEN_12;
    end
    if (_T_36) begin // @[Multiplier.scala 165:24]
      req_dw <= io_req_bits_dw; // @[Multiplier.scala 173:9]
    end
    if (_T_36) begin // @[Multiplier.scala 165:24]
      count <= {{1'd0}, _count_T_8}; // @[Multiplier.scala 169:11]
    end else if (state == 3'h3) begin // @[Multiplier.scala 130:50]
      if (eOut_1) begin // @[Multiplier.scala 155:19]
        count <= {{1'd0}, eOutPos}; // @[Multiplier.scala 157:15]
      end else begin
        count <= _count_T_1; // @[Multiplier.scala 145:11]
      end
    end else if (state == 3'h2) begin // @[Multiplier.scala 107:50]
      count <= _count_T_1; // @[Multiplier.scala 124:11]
    end
    if (_T_36) begin // @[Multiplier.scala 165:24]
      if (cmdHi) begin // @[Multiplier.scala 170:19]
        neg_out <= lhs_sign;
      end else begin
        neg_out <= lhs_sign != rhs_sign;
      end
    end else if (state == 3'h3) begin // @[Multiplier.scala 130:50]
      if (divby0 & _eOut_T_4) begin // @[Multiplier.scala 160:28]
        neg_out <= 1'h0; // @[Multiplier.scala 160:38]
      end
    end
    if (_T_36) begin // @[Multiplier.scala 165:24]
      isHi <= cmdHi; // @[Multiplier.scala 167:10]
    end
    if (_T_36) begin // @[Multiplier.scala 165:24]
      resHi <= 1'h0; // @[Multiplier.scala 168:11]
    end else if (state == 3'h3) begin // @[Multiplier.scala 130:50]
      if (count == 7'h40) begin // @[Multiplier.scala 139:38]
        resHi <= isHi; // @[Multiplier.scala 141:13]
      end else begin
        resHi <= _GEN_13;
      end
    end else begin
      resHi <= _GEN_13;
    end
    if (_T_36) begin // @[Multiplier.scala 165:24]
      divisor <= _divisor_T; // @[Multiplier.scala 171:13]
    end else if (state == 3'h1) begin // @[Multiplier.scala 93:57]
      if (divisor[63]) begin // @[Multiplier.scala 97:25]
        divisor <= subtractor; // @[Multiplier.scala 98:15]
      end
    end
    if (_T_36) begin // @[Multiplier.scala 165:24]
      remainder <= {{66'd0}, lhs_in}; // @[Multiplier.scala 172:15]
    end else if (state == 3'h3) begin // @[Multiplier.scala 130:50]
      remainder <= {{1'd0}, _GEN_16};
    end else if (state == 3'h2) begin // @[Multiplier.scala 107:50]
      remainder <= _remainder_T; // @[Multiplier.scala 122:15]
    end else if (state == 3'h5) begin // @[Multiplier.scala 102:57]
      remainder <= {{66'd0}, negated_remainder}; // @[Multiplier.scala 103:15]
    end else begin
      remainder <= _GEN_2;
    end
  end
// Register and memory initialization
`ifdef RANDOMIZE_GARBAGE_ASSIGN
`define RANDOMIZE
`endif
`ifdef RANDOMIZE_INVALID_ASSIGN
`define RANDOMIZE
`endif
`ifdef RANDOMIZE_REG_INIT
`define RANDOMIZE
`endif
`ifdef RANDOMIZE_MEM_INIT
`define RANDOMIZE
`endif
`ifndef RANDOM
`define RANDOM $random
`endif
`ifdef RANDOMIZE_MEM_INIT
  integer initvar;
`endif
`ifndef SYNTHESIS
`ifdef FIRRTL_BEFORE_INITIAL
`FIRRTL_BEFORE_INITIAL
`endif
initial begin
  `ifdef RANDOMIZE
    `ifdef INIT_RANDOM
      `INIT_RANDOM
    `endif
    `ifndef VERILATOR
      `ifdef RANDOMIZE_DELAY
        #`RANDOMIZE_DELAY begin end
      `else
        #0.002 begin end
      `endif
    `endif
`ifdef RANDOMIZE_REG_INIT
  _RAND_0 = {1{`RANDOM}};
  state = _RAND_0[2:0];
  _RAND_1 = {1{`RANDOM}};
  req_dw = _RAND_1[0:0];
  _RAND_2 = {1{`RANDOM}};
  count = _RAND_2[6:0];
  _RAND_3 = {1{`RANDOM}};
  neg_out = _RAND_3[0:0];
  _RAND_4 = {1{`RANDOM}};
  isHi = _RAND_4[0:0];
  _RAND_5 = {1{`RANDOM}};
  resHi = _RAND_5[0:0];
  _RAND_6 = {3{`RANDOM}};
  divisor = _RAND_6[64:0];
  _RAND_7 = {5{`RANDOM}};
  remainder = _RAND_7[129:0];
`endif // RANDOMIZE_REG_INIT
  `endif // RANDOMIZE
end // initial
`ifdef FIRRTL_AFTER_INITIAL
`FIRRTL_AFTER_INITIAL
`endif
`endif // SYNTHESIS
endmodule

`endif //  `ifdef RV64

`ifdef RV32

module MulDiv(
  input         clock,
  input         reset,
  output        io_req_ready,
  input         io_req_valid,
  input  [3:0]  io_req_bits_fn,
  input  [31:0] io_req_bits_in1,
  input  [31:0] io_req_bits_in2,
  input  [4:0]  io_req_bits_tag,
  input         io_kill,
  input         io_resp_ready,
  output        io_resp_valid,
  output [31:0] io_resp_bits_data,
  output [4:0]  io_resp_bits_tag
);
`ifdef RANDOMIZE_REG_INIT
  reg [31:0] _RAND_0;
  reg [31:0] _RAND_1;
  reg [31:0] _RAND_2;
  reg [31:0] _RAND_3;
  reg [31:0] _RAND_4;
  reg [31:0] _RAND_5;
  reg [63:0] _RAND_6;
  reg [95:0] _RAND_7;
`endif // RANDOMIZE_REG_INIT
  reg [2:0] state; // @[Multiplier.scala 52:22]
  reg [4:0] req_tag; // @[Multiplier.scala 54:16]
  reg [5:0] count; // @[Multiplier.scala 55:18]
  reg  neg_out; // @[Multiplier.scala 58:20]
  reg  isHi; // @[Multiplier.scala 59:17]
  reg  resHi; // @[Multiplier.scala 60:18]
  reg [32:0] divisor; // @[Multiplier.scala 61:20]
  reg [65:0] remainder; // @[Multiplier.scala 62:22]
  wire [3:0] _T = io_req_bits_fn & 4'h4; // @[Decode.scala 14:65]
  wire  cmdMul = _T == 4'h0; // @[Decode.scala 14:121]
  wire [3:0] _T_3 = io_req_bits_fn & 4'h5; // @[Decode.scala 14:65]
  wire  _T_4 = _T_3 == 4'h1; // @[Decode.scala 14:121]
  wire [3:0] _T_5 = io_req_bits_fn & 4'h2; // @[Decode.scala 14:65]
  wire  _T_6 = _T_5 == 4'h2; // @[Decode.scala 14:121]
  wire  cmdHi = _T_4 | _T_6; // @[Decode.scala 15:30]
  wire [3:0] _T_9 = io_req_bits_fn & 4'h6; // @[Decode.scala 14:65]
  wire  _T_10 = _T_9 == 4'h0; // @[Decode.scala 14:121]
  wire [3:0] _T_11 = io_req_bits_fn & 4'h1; // @[Decode.scala 14:65]
  wire  _T_12 = _T_11 == 4'h0; // @[Decode.scala 14:121]
  wire  lhsSigned = _T_10 | _T_12; // @[Decode.scala 15:30]
  wire  _T_16 = _T_3 == 4'h4; // @[Decode.scala 14:121]
  wire  rhsSigned = _T_10 | _T_16; // @[Decode.scala 15:30]
  wire  lhs_sign = lhsSigned & io_req_bits_in1[31]; // @[Multiplier.scala 82:23]
  wire [15:0] hi = io_req_bits_in1[31:16]; // @[Multiplier.scala 83:43]
  wire [15:0] lo = io_req_bits_in1[15:0]; // @[Multiplier.scala 84:15]
  wire [31:0] lhs_in = {hi,lo}; // @[Cat.scala 30:58]
  wire  rhs_sign = rhsSigned & io_req_bits_in2[31]; // @[Multiplier.scala 82:23]
  wire [15:0] hi_1 = io_req_bits_in2[31:16]; // @[Multiplier.scala 83:43]
  wire [15:0] lo_1 = io_req_bits_in2[15:0]; // @[Multiplier.scala 84:15]
  wire [32:0] subtractor = remainder[64:32] - divisor; // @[Multiplier.scala 89:37]
  wire [31:0] result = resHi ? remainder[64:33] : remainder[31:0]; // @[Multiplier.scala 90:19]
  wire [31:0] negated_remainder = 32'h0 - result; // @[Multiplier.scala 91:27]
  wire [65:0] _GEN_0 = remainder[31] ? {{34'd0}, negated_remainder} : remainder; // @[Multiplier.scala 94:27 Multiplier.scala 95:17 Multiplier.scala 62:22]
  wire [65:0] _GEN_2 = state == 3'h1 ? _GEN_0 : remainder; // @[Multiplier.scala 93:57 Multiplier.scala 62:22]
  wire [2:0] _GEN_4 = state == 3'h1 ? 3'h3 : state; // @[Multiplier.scala 93:57 Multiplier.scala 100:11 Multiplier.scala 52:22]
  wire [2:0] _GEN_6 = state == 3'h5 ? 3'h7 : _GEN_4; // @[Multiplier.scala 102:57 Multiplier.scala 104:11]
  wire  _GEN_7 = state == 3'h5 ? 1'h0 : resHi; // @[Multiplier.scala 102:57 Multiplier.scala 105:11 Multiplier.scala 60:18]
  wire [32:0] mulReg_hi = remainder[65:33]; // @[Multiplier.scala 108:31]
  wire [64:0] mulReg = {mulReg_hi,remainder[31:0]}; // @[Cat.scala 30:58]
  wire  prod_hi = remainder[32]; // @[Multiplier.scala 109:31]
  wire [31:0] mplier = mulReg[31:0]; // @[Multiplier.scala 110:24]
  wire [32:0] accum = mulReg[64:32]; // @[Multiplier.scala 111:37]
  wire [7:0] prod_lo = mplier[7:0]; // @[Multiplier.scala 113:38]
  wire [8:0] _prod_T_1 = {prod_hi,prod_lo}; // @[Multiplier.scala 113:60]
  wire [32:0] _GEN_35 = {{24{_prod_T_1[8]}},_prod_T_1}; // @[Multiplier.scala 113:67]
  wire [41:0] _prod_T_2 = $signed(_GEN_35) * $signed(divisor); // @[Multiplier.scala 113:67]
  wire [41:0] _GEN_36 = {{9{accum[32]}},accum}; // @[Multiplier.scala 113:76]
  wire [23:0] nextMulReg_lo = mplier[31:8]; // @[Multiplier.scala 114:38]
  wire [41:0] nextMulReg_hi = $signed(_prod_T_2) + $signed(_GEN_36); // @[Cat.scala 30:58]
  wire [65:0] nextMulReg = {nextMulReg_hi,nextMulReg_lo}; // @[Cat.scala 30:58]
  wire  remainder_hi_lo = count == 6'h2 & neg_out; // @[Multiplier.scala 115:57]
  wire  _eOut_T_4 = ~isHi; // @[Multiplier.scala 119:7]
  wire [32:0] nextMulReg1_hi = nextMulReg[64:32]; // @[Multiplier.scala 121:37]
  wire [31:0] nextMulReg1_lo = nextMulReg[31:0]; // @[Multiplier.scala 121:82]
  wire [64:0] nextMulReg1 = {nextMulReg1_hi,nextMulReg1_lo}; // @[Cat.scala 30:58]
  wire [32:0] remainder_hi_hi = nextMulReg1[64:32]; // @[Multiplier.scala 122:34]
  wire [31:0] remainder_lo = nextMulReg1[31:0]; // @[Multiplier.scala 122:67]
  wire [65:0] _remainder_T = {remainder_hi_hi,remainder_hi_lo,remainder_lo}; // @[Cat.scala 30:58]
  wire [5:0] _count_T_1 = count + 6'h1; // @[Multiplier.scala 124:20]
  wire [2:0] _GEN_8 = count == 6'h3 ? 3'h6 : _GEN_6; // @[Multiplier.scala 125:51 Multiplier.scala 126:13]
  wire  _GEN_9 = count == 6'h3 ? isHi : _GEN_7; // @[Multiplier.scala 125:51 Multiplier.scala 127:13]
  wire [2:0] _GEN_12 = state == 3'h2 ? _GEN_8 : _GEN_6; // @[Multiplier.scala 107:50]
  wire  _GEN_13 = state == 3'h2 ? _GEN_9 : _GEN_7; // @[Multiplier.scala 107:50]
  wire  unrolls_less = subtractor[32]; // @[Multiplier.scala 134:28]
  wire [31:0] unrolls_hi_hi = unrolls_less ? remainder[63:32] : subtractor[31:0]; // @[Multiplier.scala 135:14]
  wire  unrolls_lo = ~unrolls_less; // @[Multiplier.scala 135:67]
  wire [64:0] unrolls_0 = {unrolls_hi_hi,remainder[31:0],unrolls_lo}; // @[Cat.scala 30:58]
  wire [2:0] _state_T = neg_out ? 3'h5 : 3'h7; // @[Multiplier.scala 140:19]
  wire [2:0] _GEN_14 = count == 6'h20 ? _state_T : _GEN_12; // @[Multiplier.scala 139:38 Multiplier.scala 140:13]
  wire  divby0 = count == 6'h0 & unrolls_lo; // @[Multiplier.scala 147:30]
  wire  _T_34 = io_resp_ready & io_resp_valid; // @[Decoupled.scala 40:37]
  wire  _T_36 = io_req_ready & io_req_valid; // @[Decoupled.scala 40:37]
  wire [32:0] _divisor_T = {rhs_sign,hi_1,lo_1}; // @[Cat.scala 30:58]
  wire [15:0] loOut = result[15:0]; // @[Multiplier.scala 177:82]
  assign io_req_ready = state == 3'h0; // @[Multiplier.scala 183:25]
  assign io_resp_valid = state == 3'h6 | state == 3'h7; // @[Multiplier.scala 182:42]
  assign io_resp_bits_data = {result[31:16],loOut}; // @[Cat.scala 30:58]
  assign io_resp_bits_tag = req_tag; // @[Multiplier.scala 179:20]
  always @(posedge clock) begin
    if (reset) begin // @[Multiplier.scala 52:22]
      state <= 3'h0; // @[Multiplier.scala 52:22]
    end else if (_T_36) begin // @[Multiplier.scala 165:24]
      if (cmdMul) begin // @[Multiplier.scala 166:17]
        state <= 3'h2;
      end else if (lhs_sign | rhs_sign) begin // @[Multiplier.scala 166:36]
        state <= 3'h1;
      end else begin
        state <= 3'h3;
      end
    end else if (_T_34 | io_kill) begin // @[Multiplier.scala 162:36]
      state <= 3'h0; // @[Multiplier.scala 163:11]
    end else if (state == 3'h3) begin // @[Multiplier.scala 130:50]
      state <= _GEN_14;
    end else begin
      state <= _GEN_12;
    end
    if (_T_36) begin // @[Multiplier.scala 165:24]
      req_tag <= io_req_bits_tag; // @[Multiplier.scala 173:9]
    end
    if (_T_36) begin // @[Multiplier.scala 165:24]
      count <= 6'h0; // @[Multiplier.scala 169:11]
    end else if (state == 3'h3) begin // @[Multiplier.scala 130:50]
      count <= _count_T_1; // @[Multiplier.scala 145:11]
    end else if (state == 3'h2) begin // @[Multiplier.scala 107:50]
      count <= _count_T_1; // @[Multiplier.scala 124:11]
    end
    if (_T_36) begin // @[Multiplier.scala 165:24]
      if (cmdHi) begin // @[Multiplier.scala 170:19]
        neg_out <= lhs_sign;
      end else begin
        neg_out <= lhs_sign != rhs_sign;
      end
    end else if (state == 3'h3) begin // @[Multiplier.scala 130:50]
      if (divby0 & _eOut_T_4) begin // @[Multiplier.scala 160:28]
        neg_out <= 1'h0; // @[Multiplier.scala 160:38]
      end
    end
    if (_T_36) begin // @[Multiplier.scala 165:24]
      isHi <= cmdHi; // @[Multiplier.scala 167:10]
    end
    if (_T_36) begin // @[Multiplier.scala 165:24]
      resHi <= 1'h0; // @[Multiplier.scala 168:11]
    end else if (state == 3'h3) begin // @[Multiplier.scala 130:50]
      if (count == 6'h20) begin // @[Multiplier.scala 139:38]
        resHi <= isHi; // @[Multiplier.scala 141:13]
      end else begin
        resHi <= _GEN_13;
      end
    end else begin
      resHi <= _GEN_13;
    end
    if (_T_36) begin // @[Multiplier.scala 165:24]
      divisor <= _divisor_T; // @[Multiplier.scala 171:13]
    end else if (state == 3'h1) begin // @[Multiplier.scala 93:57]
      if (divisor[31]) begin // @[Multiplier.scala 97:25]
        divisor <= subtractor; // @[Multiplier.scala 98:15]
      end
    end
    if (_T_36) begin // @[Multiplier.scala 165:24]
      remainder <= {{34'd0}, lhs_in}; // @[Multiplier.scala 172:15]
    end else if (state == 3'h3) begin // @[Multiplier.scala 130:50]
      remainder <= {{1'd0}, unrolls_0}; // @[Multiplier.scala 138:15]
    end else if (state == 3'h2) begin // @[Multiplier.scala 107:50]
      remainder <= _remainder_T; // @[Multiplier.scala 122:15]
    end else if (state == 3'h5) begin // @[Multiplier.scala 102:57]
      remainder <= {{34'd0}, negated_remainder}; // @[Multiplier.scala 103:15]
    end else begin
      remainder <= _GEN_2;
    end
  end
// Register and memory initialization
`ifdef RANDOMIZE_GARBAGE_ASSIGN
`define RANDOMIZE
`endif
`ifdef RANDOMIZE_INVALID_ASSIGN
`define RANDOMIZE
`endif
`ifdef RANDOMIZE_REG_INIT
`define RANDOMIZE
`endif
`ifdef RANDOMIZE_MEM_INIT
`define RANDOMIZE
`endif
`ifndef RANDOM
`define RANDOM $random
`endif
`ifdef RANDOMIZE_MEM_INIT
  integer initvar;
`endif
`ifndef SYNTHESIS
`ifdef FIRRTL_BEFORE_INITIAL
`FIRRTL_BEFORE_INITIAL
`endif
initial begin
  `ifdef RANDOMIZE
    `ifdef INIT_RANDOM
      `INIT_RANDOM
    `endif
    `ifndef VERILATOR
      `ifdef RANDOMIZE_DELAY
        #`RANDOMIZE_DELAY begin end
      `else
        #0.002 begin end
      `endif
    `endif
`ifdef RANDOMIZE_REG_INIT
  _RAND_0 = {1{`RANDOM}};
  state = _RAND_0[2:0];
  _RAND_1 = {1{`RANDOM}};
  req_tag = _RAND_1[4:0];
  _RAND_2 = {1{`RANDOM}};
  count = _RAND_2[5:0];
  _RAND_3 = {1{`RANDOM}};
  neg_out = _RAND_3[0:0];
  _RAND_4 = {1{`RANDOM}};
  isHi = _RAND_4[0:0];
  _RAND_5 = {1{`RANDOM}};
  resHi = _RAND_5[0:0];
  _RAND_6 = {2{`RANDOM}};
  divisor = _RAND_6[32:0];
  _RAND_7 = {3{`RANDOM}};
  remainder = _RAND_7[65:0];
`endif // RANDOMIZE_REG_INIT
  `endif // RANDOMIZE
end // initial
`ifdef FIRRTL_AFTER_INITIAL
`FIRRTL_AFTER_INITIAL
`endif
`endif // SYNTHESIS
endmodule
module PlusArgTimeout(
  input         clock,
  input         reset,
  input  [31:0] io_count
);
  wire [31:0] plusarg_reader_out; // @[PlusArg.scala 62:19]
  wire  _T = plusarg_reader_out > 32'h0; // @[PlusArg.scala 63:13]
  plusarg_reader #(.FORMAT("max_core_cycles=%d"), .DEFAULT(0), .WIDTH(32)) plusarg_reader ( // @[PlusArg.scala 62:19]
    .out(plusarg_reader_out)
  );
  always @(posedge clock) begin
    `ifndef SYNTHESIS
    `ifdef PRINTF_COND
      if (`PRINTF_COND) begin
    `endif
        if (_T & ~(io_count < plusarg_reader_out | reset)) begin
          $fwrite(32'h80000002,
            "Assertion failed: Timeout exceeded: Kill the emulation after INT rdtime cycles. Off if 0.\n    at PlusArg.scala:64 assert (io.count < max, s\"Timeout exceeded: $docstring\")\n"
            ); // @[PlusArg.scala 64:12]
        end
    `ifdef PRINTF_COND
      end
    `endif
    `endif // SYNTHESIS
    `ifndef SYNTHESIS
    `ifdef STOP_COND
      if (`STOP_COND) begin
    `endif
        if (_T & ~(io_count < plusarg_reader_out | reset)) begin
          $fatal; // @[PlusArg.scala 64:12]
        end
    `ifdef STOP_COND
      end
    `endif
    `endif // SYNTHESIS
  end
endmodule

  `endif //  `ifdef RV32
