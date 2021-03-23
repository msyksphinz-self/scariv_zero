package decoder_lsu_ctrl_pkg;
  typedef enum logic [0: 0] {
    SIZE__ = 0,
    SIZE_DW = 1
  } size_t;
  typedef enum logic [0: 0] {
    IS_LOAD__ = 0,
    IS_LOAD_1 = 1
  } is_load_t;
  typedef enum logic [0: 0] {
    IS_STORE__ = 0,
    IS_STORE_1 = 1
  } is_store_t;
endpackage

module internal_decoder_lsu_ctrl (
  input logic [31:0] inst,
  output logic size,
  output logic is_load,
  output logic is_store
);
wire tmp_0 = !inst[14] & inst[13] & inst[12] & !inst[6] & !inst[5] & !inst[4] & !inst[3] & !inst[2] & inst[1] & inst[0] & 1'b1;
wire tmp_1 = !inst[14] & inst[13] & inst[12] & !inst[6] & inst[5] & !inst[4] & !inst[3] & !inst[2] & inst[1] & inst[0] & 1'b1;
assign size = tmp_0 | tmp_1 | 1'b0;
assign is_load = tmp_0 | 1'b0;
assign is_store = tmp_1 | 1'b0;
endmodule

module decoder_lsu_ctrl (
  input logic [31:0] inst,
  output decoder_lsu_ctrl_pkg::size_t size,
  output decoder_lsu_ctrl_pkg::is_load_t is_load,
  output decoder_lsu_ctrl_pkg::is_store_t is_store
);
logic raw_size;
logic raw_is_load;
logic raw_is_store;
internal_decoder_lsu_ctrl u_inst (
 .inst(inst),
 .size(raw_size),
 .is_load(raw_is_load),
 .is_store(raw_is_store)
);
assign size = decoder_lsu_ctrl_pkg::size_t'(raw_size);
assign is_load = decoder_lsu_ctrl_pkg::is_load_t'(raw_is_load);
assign is_store = decoder_lsu_ctrl_pkg::is_store_t'(raw_is_store);
endmodule