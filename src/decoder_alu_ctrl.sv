package decoder_alu_ctrl_pkg;
  typedef enum logic [3: 0] {
    OP__ = 0,
    OP_SIGN_LUI = 1,
    OP_SIGN_AUIPC = 2,
    OP_SIGN_ADD = 3,
    OP_SIGN_SUB = 4,
    OP_SIGN_ADD_32 = 5,
    OP_SLL = 6,
    OP_SRL = 7,
    OP_SRA = 8,
    OP_SLL_32 = 9,
    OP_SRL_32 = 10,
    OP_SRA_32 = 11
  } op_t;
  typedef enum logic [1: 0] {
    IMM__ = 0,
    IMM_S = 1,
    IMM_SH = 2
  } imm_t;
endpackage

module internal_decoder_alu_ctrl (
  input logic [31:0] inst,
  output logic [3: 0]  op,
  output logic [1: 0]  imm
);
wire tmp_0 = !inst[31] & inst[30] & !inst[29] & !inst[28] & !inst[27] & !inst[26] & !inst[25] & !inst[14] & !inst[13] & !inst[12] & !inst[6] & inst[5] & inst[4] & !inst[3] & !inst[2] & inst[1] & inst[0] & 1'b1;
wire tmp_1 = !inst[31] & inst[30] & !inst[29] & !inst[28] & !inst[27] & !inst[26] & !inst[25] & inst[14] & !inst[13] & inst[12] & !inst[6] & inst[4] & inst[3] & !inst[2] & inst[1] & inst[0] & 1'b1;
wire tmp_2 = !inst[31] & !inst[29] & !inst[28] & !inst[27] & !inst[26] & !inst[25] & inst[14] & !inst[13] & inst[12] & !inst[6] & !inst[5] & inst[4] & !inst[2] & inst[1] & inst[0] & 1'b1;
wire tmp_3 = !inst[31] & !inst[30] & !inst[29] & !inst[28] & !inst[27] & !inst[26] & !inst[25] & !inst[13] & inst[12] & !inst[6] & !inst[5] & inst[4] & !inst[2] & inst[1] & inst[0] & 1'b1;
wire tmp_4 = !inst[31] & inst[30] & !inst[29] & !inst[28] & !inst[27] & !inst[26] & inst[14] & !inst[13] & inst[12] & !inst[6] & !inst[5] & inst[4] & !inst[3] & !inst[2] & inst[1] & inst[0] & 1'b1;
wire tmp_5 = !inst[31] & !inst[30] & !inst[29] & !inst[28] & !inst[27] & !inst[26] & !inst[25] & !inst[14] & !inst[13] & !inst[12] & !inst[6] & inst[4] & !inst[3] & !inst[2] & inst[1] & inst[0] & 1'b1;
wire tmp_6 = !inst[31] & !inst[30] & !inst[29] & !inst[28] & !inst[27] & !inst[26] & inst[14] & !inst[13] & inst[12] & !inst[6] & !inst[5] & inst[4] & !inst[3] & !inst[2] & inst[1] & inst[0] & 1'b1;
wire tmp_7 = !inst[31] & !inst[30] & !inst[29] & !inst[28] & !inst[27] & !inst[26] & !inst[25] & !inst[14] & !inst[13] & inst[12] & !inst[6] & inst[4] & inst[3] & !inst[2] & inst[1] & inst[0] & 1'b1;
wire tmp_8 = !inst[31] & inst[30] & !inst[29] & !inst[28] & !inst[27] & !inst[26] & !inst[25] & inst[14] & !inst[13] & inst[12] & !inst[6] & inst[4] & !inst[2] & inst[1] & inst[0] & 1'b1;
wire tmp_9 = !inst[31] & !inst[30] & !inst[29] & !inst[28] & !inst[27] & !inst[26] & !inst[25] & inst[14] & !inst[13] & inst[12] & !inst[6] & inst[4] & !inst[3] & !inst[2] & inst[1] & inst[0] & 1'b1;
wire tmp_10 = !inst[31] & !inst[29] & !inst[28] & !inst[27] & !inst[26] & !inst[25] & inst[14] & !inst[13] & inst[12] & !inst[6] & inst[4] & inst[3] & !inst[2] & inst[1] & inst[0] & 1'b1;
wire tmp_11 = !inst[31] & !inst[30] & !inst[29] & !inst[28] & !inst[27] & !inst[26] & !inst[25] & !inst[13] & inst[12] & !inst[6] & inst[4] & !inst[3] & !inst[2] & inst[1] & inst[0] & 1'b1;
wire tmp_12 = !inst[31] & !inst[30] & !inst[29] & !inst[28] & !inst[27] & !inst[26] & !inst[13] & inst[12] & !inst[6] & !inst[5] & inst[4] & !inst[3] & !inst[2] & inst[1] & inst[0] & 1'b1;
wire tmp_13 = !inst[14] & !inst[13] & !inst[12] & !inst[6] & !inst[5] & inst[4] & inst[3] & !inst[2] & inst[1] & inst[0] & 1'b1;
wire tmp_14 = !inst[14] & !inst[13] & !inst[12] & !inst[6] & !inst[5] & inst[4] & !inst[3] & !inst[2] & inst[1] & inst[0] & 1'b1;
wire tmp_15 = !inst[6] & inst[5] & inst[4] & !inst[3] & inst[2] & inst[1] & inst[0] & 1'b1;
wire tmp_16 = !inst[6] & !inst[5] & inst[4] & !inst[3] & inst[2] & inst[1] & inst[0] & 1'b1;
assign op[3] = tmp_4 | tmp_7 | tmp_8 | tmp_10 | 1'b0;
assign op[2] = tmp_0 | tmp_11 | tmp_12 | tmp_13 | 1'b0;
assign op[1] = tmp_5 | tmp_10 | tmp_11 | tmp_12 | tmp_14 | tmp_16 | 1'b0;
assign op[0] = tmp_1 | tmp_5 | tmp_6 | tmp_7 | tmp_9 | tmp_13 | tmp_14 | tmp_15 | 1'b0;
assign imm[1] = tmp_2 | tmp_3 | tmp_4 | tmp_12 | 1'b0;
assign imm[0] = tmp_13 | tmp_14 | tmp_15 | tmp_16 | 1'b0;
endmodule

module decoder_alu_ctrl (
  input logic [31:0] inst,
  output decoder_alu_ctrl_pkg::op_t op,
  output decoder_alu_ctrl_pkg::imm_t imm
);
logic [3: 0] raw_op;
logic [1: 0] raw_imm;
internal_decoder_alu_ctrl u_inst (
 .inst(inst),
 .op(raw_op),
 .imm(raw_imm)
);
assign op = decoder_alu_ctrl_pkg::op_t'(raw_op);
assign imm = decoder_alu_ctrl_pkg::imm_t'(raw_imm);
endmodule