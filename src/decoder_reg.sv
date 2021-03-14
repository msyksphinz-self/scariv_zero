package decoder_reg_pkg;
  typedef enum logic [0: 0] {
    RD__ = 0,
    RD_R3 = 1
  } rd_t;
  typedef enum logic [1: 0] {
    R1__ = 0,
    R1_PC = 1,
    R1_R1 = 2
  } r1_t;
  typedef enum logic [0: 0] {
    R2__ = 0,
    R2_R2 = 1
  } r2_t;
endpackage;

module internal_decoder_reg (
  input logic [31:0] inst,
  output logic rd,
  output logic [1: 0]  r1,
  output logic r2
);
wire tmp_0 = !inst[31] & !inst[29] & !inst[28] & !inst[27] & !inst[26] & !inst[25] & !inst[14] & !inst[13] & !inst[12] & !inst[6] & inst[5] & inst[4] & !inst[3] & !inst[2] & inst[1] & inst[0] & 1'b1;
wire tmp_1 = !inst[14] & inst[13] & inst[12] & !inst[6] & inst[5] & !inst[4] & !inst[3] & !inst[2] & inst[1] & inst[0] & 1'b1;
wire tmp_2 = !inst[14] & inst[13] & inst[12] & !inst[6] & !inst[5] & !inst[4] & !inst[3] & !inst[2] & inst[1] & inst[0] & 1'b1;
wire tmp_3 = !inst[14] & !inst[13] & !inst[12] & inst[6] & inst[5] & !inst[4] & !inst[3] & inst[2] & inst[1] & inst[0] & 1'b1;
wire tmp_4 = inst[6] & inst[5] & !inst[4] & inst[3] & inst[2] & inst[1] & inst[0] & 1'b1;
wire tmp_5 = !inst[14] & !inst[13] & !inst[12] & !inst[6] & !inst[5] & inst[4] & !inst[2] & inst[1] & inst[0] & 1'b1;
wire tmp_6 = !inst[6] & !inst[5] & inst[4] & !inst[3] & inst[2] & inst[1] & inst[0] & 1'b1;
wire tmp_7 = !inst[14] & !inst[13] & inst[6] & inst[5] & !inst[4] & !inst[3] & !inst[2] & inst[1] & inst[0] & 1'b1;
wire tmp_8 = !inst[6] & inst[4] & !inst[3] & inst[2] & inst[1] & inst[0] & 1'b1;
assign rd = tmp_0 | tmp_2 | tmp_3 | tmp_4 | tmp_5 | tmp_8 | 1'b0;
assign r1[1] = tmp_0 | tmp_1 | tmp_2 | tmp_3 | tmp_5 | tmp_7 | 1'b0;
assign r1[0] = tmp_6 | 1'b0;
assign r2 = tmp_0 | tmp_1 | tmp_7 | 1'b0;
endmodule

module decoder_reg (
  input logic [31:0] inst,
  output decoder_reg_pkg::rd_t rd,
  output decoder_reg_pkg::r1_t r1,
  output decoder_reg_pkg::r2_t r2
);
logic raw_rd;
logic [1: 0] raw_r1;
logic raw_r2;
internal_decoder_reg u_inst (
 .inst(inst),
 .rd(raw_rd),
 .r1(raw_r1),
 .r2(raw_r2)
);
assign rd = decoder_reg_pkg::rd_t'(raw_rd);
assign r1 = decoder_reg_pkg::r1_t'(raw_r1);
assign r2 = decoder_reg_pkg::r2_t'(raw_r2);
endmodule