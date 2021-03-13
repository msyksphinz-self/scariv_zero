package decoder_alu_ctrl_pkg;
  typedef enum logic [2: 0] {
    OP__ = 0,
    OP_SIGN_LUI = 1,
    OP_SIGN_AUIPC = 2,
    OP_SIGN_ADD = 3,
    OP_SIGN_SUB = 4,
    OP_SIGN_ADD_32 = 5
  } op_t;
  typedef enum logic [0: 0] {
    IMM__ = 0,
    IMM_S = 1
  } imm_t;
endpackage

module decoder_alu_ctrl (
  input logic [31:0] inst,
  output logic [2: 0]  op,
  output logic imm
);
wire tmp_0 = !inst[14] & !inst[13] & !inst[12] & !inst[6] & !inst[5] & inst[4] & !inst[3] & !inst[2] & inst[1] & inst[0] & 1'b1;
wire tmp_1 = !inst[31] & inst[30] & !inst[29] & !inst[28] & !inst[27] & !inst[26] & !inst[25] & !inst[14] & !inst[13] & !inst[12] & !inst[6] & inst[5] & inst[4] & !inst[3] & !inst[2] & inst[1] & inst[0] & 1'b1;
wire tmp_2 = !inst[31] & !inst[30] & !inst[29] & !inst[28] & !inst[27] & !inst[26] & !inst[25] & !inst[14] & !inst[13] & !inst[12] & !inst[6] & inst[4] & !inst[3] & !inst[2] & inst[1] & inst[0] & 1'b1;
wire tmp_3 = !inst[14] & !inst[13] & !inst[12] & !inst[6] & !inst[5] & inst[4] & inst[3] & !inst[2] & inst[1] & inst[0] & 1'b1;
wire tmp_4 = !inst[6] & inst[5] & inst[4] & !inst[3] & inst[2] & inst[1] & inst[0] & 1'b1;
wire tmp_5 = !inst[6] & !inst[5] & inst[4] & !inst[3] & inst[2] & inst[1] & inst[0] & 1'b1;
assign op[2] = tmp_1 | tmp_3 | 1'b0;
assign op[1] = tmp_0 | tmp_2 | tmp_5 | 1'b0;
assign op[0] = tmp_0 | tmp_2 | tmp_3 | tmp_4 | 1'b0;
assign imm = tmp_0 | tmp_3 | tmp_4 | tmp_5 | 1'b0;
endmodule
