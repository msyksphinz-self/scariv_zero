module decoder_cat (
  input logic [31:0] inst,
  output logic [1: 0]  cat
);
wire tmp_0 = !inst[31] & !inst[29] & !inst[28] & !inst[27] & !inst[26] & !inst[25] & !inst[14] & !inst[13] & !inst[12] & !inst[6] & inst[4] & !inst[3] & inst[1] & inst[0] & 1'b1;
wire tmp_1 = !inst[14] & inst[13] & inst[12] & !inst[6] & !inst[4] & !inst[3] & !inst[2] & inst[1] & inst[0] & 1'b1;
wire tmp_2 = !inst[14] & !inst[13] & !inst[12] & !inst[6] & !inst[5] & inst[4] & !inst[3] & inst[1] & inst[0] & 1'b1;
wire tmp_3 = !inst[6] & inst[4] & !inst[3] & inst[2] & inst[1] & inst[0] & 1'b1;
assign cat[1] = tmp_1 | 1'b0;
assign cat[0] = tmp_0 | tmp_2 | tmp_3 | 1'b0;
endmodule
