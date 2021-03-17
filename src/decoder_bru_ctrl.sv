package decoder_bru_ctrl_pkg;
  typedef enum logic [1: 0] {
    OP__ = 0,
    OP_EQ = 1,
    OP_NE = 2
  } op_t;
  typedef enum logic [1: 0] {
    IMM__ = 0,
    IMM_SB = 1,
    IMM_UJ = 2,
    IMM_I = 3
  } imm_t;
endpackage;

module internal_decoder_bru_ctrl (
  input logic [31:0] inst,
  output logic [1: 0]  op,
  output logic [1: 0]  imm
);
wire tmp_0 = !inst[14] & !inst[13] & !inst[12] & inst[6] & inst[5] & !inst[4] & !inst[3] & inst[2] & inst[1] & inst[0] & 1'b1;
wire tmp_1 = !inst[14] & !inst[13] & inst[12] & inst[6] & inst[5] & !inst[4] & !inst[3] & !inst[2] & inst[1] & inst[0] & 1'b1;
wire tmp_2 = !inst[14] & !inst[13] & !inst[12] & inst[6] & inst[5] & !inst[4] & !inst[3] & !inst[2] & inst[1] & inst[0] & 1'b1;
wire tmp_3 = inst[6] & inst[5] & !inst[4] & inst[3] & inst[2] & inst[1] & inst[0] & 1'b1;
assign op[1] = tmp_1 | 1'b0;
assign op[0] = tmp_2 | 1'b0;
assign imm[1] = tmp_0 | tmp_3 | 1'b0;
assign imm[0] = tmp_0 | tmp_1 | tmp_2 | 1'b0;
endmodule

module decoder_bru_ctrl (
  input logic [31:0] inst,
  output decoder_bru_ctrl_pkg::op_t op,
  output decoder_bru_ctrl_pkg::imm_t imm
);
logic [1: 0] raw_op;
logic [1: 0] raw_imm;
internal_decoder_bru_ctrl u_inst (
 .inst(inst),
 .op(raw_op),
 .imm(raw_imm)
);
assign op = decoder_bru_ctrl_pkg::op_t'(raw_op);
assign imm = decoder_bru_ctrl_pkg::imm_t'(raw_imm);
endmodule