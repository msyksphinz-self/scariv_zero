module decoder_cat (
  input logic [31:0] inst,
  output logic cat
);
wire tmp_0 = !inst[14] & inst[13] & inst[12] & !inst[6] & !inst[4] & !inst[3] & !inst[2] & inst[1] & inst[0] & 1'b1;
assign cat = tmp_0 | 1'b0;
endmodule
