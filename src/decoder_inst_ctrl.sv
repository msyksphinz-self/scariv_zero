module decoder_inst_ctrl (
  input logic [31:0] inst,
  output logic rd,
  output logic [1: 0]  op,
  output logic imm,
  output logic r1,
  output logic r2,
  output logic size,
  output logic sign
);
wire tmp_0 = !inst[31] & inst[30] & !inst[29] & !inst[28] & !inst[27] & !inst[26] & !inst[25] & !inst[14] & !inst[13] & !inst[12] & !inst[6] & inst[5] & inst[4] & !inst[3] & !inst[2] & inst[1] & inst[0] & 1'b1;
wire tmp_1 = !inst[31] & !inst[29] & !inst[28] & !inst[27] & !inst[26] & !inst[25] & !inst[14] & !inst[13] & !inst[12] & !inst[6] & inst[5] & inst[4] & !inst[3] & !inst[2] & inst[1] & inst[0] & 1'b1;
wire tmp_2 = !inst[14] & inst[13] & inst[12] & !inst[6] & !inst[4] & !inst[3] & !inst[2] & inst[1] & inst[0] & 1'b1;
wire tmp_3 = !inst[6] & !inst[5] & inst[4] & !inst[3] & inst[2] & inst[1] & inst[0] & 1'b1;
assign rd = 1'b0;
assign op[1] = tmp_1 | 1'b0;
assign op[0] = tmp_0 | tmp_3 | 1'b0;
assign imm = 1'b0;
assign r1 = tmp_1 | tmp_2 | 1'b0;
assign r2 = 1'b0;
assign size = 1'b0;
assign sign = 1'b0;
endmodule
