module decoder_inst_ctrl (
  input logic [31:0] inst,
  output logic [2: 0]  op,
  output logic imm,
  output logic size,
  output logic sign
);
wire tmp_0 = !inst[31] & inst[30] & !inst[29] & !inst[28] & !inst[27] & !inst[26] & !inst[25] & !inst[14] & !inst[13] & !inst[12] & !inst[6] & inst[5] & inst[4] & !inst[3] & !inst[2] & inst[1] & inst[0] & 1'b1;
wire tmp_1 = !inst[31] & !inst[30] & !inst[29] & !inst[28] & !inst[27] & !inst[26] & !inst[25] & !inst[14] & !inst[13] & !inst[12] & !inst[6] & inst[4] & !inst[3] & !inst[2] & inst[1] & inst[0] & 1'b1;
wire tmp_2 = !inst[14] & inst[13] & inst[12] & !inst[6] & !inst[4] & !inst[3] & !inst[2] & inst[1] & inst[0] & 1'b1;
wire tmp_3 = !inst[14] & !inst[13] & !inst[12] & !inst[6] & !inst[5] & inst[4] & !inst[3] & !inst[2] & inst[1] & inst[0] & 1'b1;
wire tmp_4 = !inst[6] & !inst[5] & inst[4] & !inst[3] & inst[2] & inst[1] & inst[0] & 1'b1;
wire tmp_5 = !inst[6] & inst[5] & inst[4] & !inst[3] & inst[2] & inst[1] & inst[0] & 1'b1;
assign op[2] = tmp_0 | 1'b0;
assign op[1] = tmp_1 | tmp_3 | tmp_4 | 1'b0;
assign op[0] = tmp_1 | tmp_3 | tmp_5 | 1'b0;
assign imm = tmp_3 | tmp_4 | tmp_5 | 1'b0;
assign size = tmp_2 | 1'b0;
assign sign = tmp_2 | 1'b0;
endmodule
