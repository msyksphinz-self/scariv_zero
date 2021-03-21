package decoder_inst_cat_pkg;
  typedef enum logic [2: 0] {
    INST_CAT__ = 0,
    INST_CAT_ARITH = 1,
    INST_CAT_LD = 2,
    INST_CAT_ST = 3,
    INST_CAT_BR = 4
  } inst_cat_t;
endpackage

module internal_decoder_inst_cat (
  input logic [31:0] inst,
  output logic [2: 0]  inst_cat
);
wire tmp_0 = !inst[31] & !inst[29] & !inst[28] & !inst[27] & !inst[26] & !inst[25] & !inst[14] & !inst[13] & !inst[12] & !inst[6] & inst[4] & !inst[3] & inst[1] & inst[0] & 1'b1;
wire tmp_1 = !inst[14] & inst[13] & inst[12] & !inst[6] & inst[5] & !inst[4] & !inst[3] & !inst[2] & inst[1] & inst[0] & 1'b1;
wire tmp_2 = !inst[14] & inst[13] & inst[12] & !inst[6] & !inst[4] & !inst[3] & !inst[2] & inst[1] & inst[0] & 1'b1;
wire tmp_3 = !inst[14] & !inst[13] & !inst[12] & !inst[6] & !inst[5] & inst[4] & !inst[2] & inst[1] & inst[0] & 1'b1;
wire tmp_4 = !inst[14] & !inst[13] & !inst[12] & inst[6] & inst[5] & !inst[4] & inst[2] & inst[1] & inst[0] & 1'b1;
wire tmp_5 = !inst[14] & !inst[13] & inst[6] & inst[5] & !inst[4] & !inst[3] & !inst[2] & inst[1] & inst[0] & 1'b1;
wire tmp_6 = inst[6] & inst[5] & !inst[4] & inst[3] & inst[2] & inst[1] & inst[0] & 1'b1;
wire tmp_7 = !inst[6] & inst[4] & !inst[3] & inst[2] & inst[1] & inst[0] & 1'b1;
assign inst_cat[2] = tmp_4 | tmp_5 | tmp_6 | 1'b0;
assign inst_cat[1] = tmp_2 | 1'b0;
assign inst_cat[0] = tmp_0 | tmp_1 | tmp_3 | tmp_7 | 1'b0;
endmodule

module decoder_inst_cat (
  input logic [31:0] inst,
  output decoder_inst_cat_pkg::inst_cat_t inst_cat
);
logic [2: 0] raw_inst_cat;
internal_decoder_inst_cat u_inst (
 .inst(inst),
 .inst_cat(raw_inst_cat)
);
assign inst_cat = decoder_inst_cat_pkg::inst_cat_t'(raw_inst_cat);
endmodule
