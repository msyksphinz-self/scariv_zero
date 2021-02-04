module decoder_inst_ctrl (
  input logic [31:0] inst,
  output logic rd,
  output logic [2: 0]  op,
  output logic imm,
  output logic [1: 0]  r1,
  output logic r2,
  output logic size,
  output logic sign
);
wire tmp_0 = 1'b1;
wire tmp_1 = 1'b1;
wire tmp_2 = 1'b1;
wire tmp_3 = !inst[31] & !inst[30] & !inst[29] & !inst[18] & !inst[17] & !inst[16] & !inst[10] & inst[9] & inst[8] & !inst[7] & !inst[6] & inst[5] & inst[4] & inst[3] & inst[2] & inst[1] & !inst[0] & 1'b1;
wire tmp_4 = !inst[31] & !inst[30] & !inst[19] & !inst[18] & !inst[17] & !inst[11] & inst[10] & inst[9] & !inst[8] & !inst[7] & inst[6] & inst[5] & inst[4] & inst[3] & !inst[2] & !inst[1] & !inst[0] & 1'b1;
wire tmp_5 = !inst[19] & inst[18] & inst[17] & !inst[11] & !inst[10] & !inst[9] & !inst[8] & !inst[7] & inst[6] & inst[5] & inst[4] & !inst[3] & !inst[2] & !inst[1] & inst[0] & 1'b1;
wire tmp_6 = !inst[8] & !inst[7] & inst[6] & !inst[5] & inst[4] & inst[3] & inst[2] & inst[1] & inst[0] & 1'b1;
wire tmp_7 = !inst[6] & inst[5] & inst[4] & !inst[3] & inst[2] & inst[1] & inst[0] & 1'b1;
assign rd = tmp_3 | tmp_4 | tmp_7 | 1'b0;
assign op[2] = tmp_5 | tmp_6 | 1'b0;
assign op[1] = tmp_3 | tmp_4 | tmp_5 | tmp_6 | tmp_7 | 1'b0;
assign op[0] = tmp_5 | tmp_7 | 1'b0;
assign imm = 1'b0;
assign r1[1] = 1'b0;
assign r1[0] = tmp_3 | 1'b0;
assign r2 = 1'b0;
assign size = 1'b0;
assign sign = 1'b0;
endmodule
