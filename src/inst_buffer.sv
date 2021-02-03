module inst_buffer
  #(
    parameter DISPATCH_SIZE = 5
    )
(
 input logic                                i_clk,
 input logic                                i_reset_n,

 input logic                                i_inst_vld,

 output logic                               o_inst_rdy,
 input logic [mrh_pkg::ICACHE_DATA_W-1: 0]  i_inst_in,
 input logic [mrh_pkg::ICACHE_DATA_B_W-1:0] i_inst_byte_en,

 output logic                               o_inst_buf_valid,
 output mrh_pkg::inst_buf_t                 o_inst_buf[DISPATCH_SIZE],
 input logic                                i_inst_buf_ready
 );

logic [ 1: 0]                               inst_buffer_vld_q;
logic [mrh_pkg::ICACHE_DATA_W-1: 0]         inst_buffer_q[2];
logic [mrh_pkg::ICACHE_DATA_B_W-1: 0]       inst_buffer_byte_en_q[2];
logic [mrh_pkg::ICACHE_DATA_B_W-1: 0]       inst_buffer_en_pick_up;
logic [$clog2(mrh_pkg::ICACHE_DATA_B_W)-1:0] inst_buffer_en_ff_idx;


always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    inst_buffer_vld_q <= 2'b00;
  end else begin
    if (i_inst_vld & o_inst_rdy) begin
      if (!inst_buffer_vld_q[0]) begin
        inst_buffer_q[0]         <= i_inst_in;
        inst_buffer_vld_q[0]     <= 1'b1;
        inst_buffer_byte_en_q[0] <= i_inst_byte_en;
      end else begin
        inst_buffer_q[1]         <= i_inst_in;
        inst_buffer_vld_q[1]     <= 1'b1;
        inst_buffer_byte_en_q[1] <= i_inst_byte_en;
      end
    end // if (i_inst_vld & o_inst_rdy)
  end // else: !if(!i_reset_n)
end // always_ff @ (posedge i_clk, negedge i_reset_n)

assign o_inst_rdy = !(&inst_buffer_vld_q);

localparam ic_word_num = mrh_pkg::ICACHE_DATA_B_W / 4;
mrh_pkg::inst_cat_t [ic_word_num-1: 0] w_inst_cat;
logic [ic_word_num-1:0] w_inst_is_arith;
logic [ic_word_num-1:0] w_inst_is_mem;

logic [ic_word_num-1:0] w_inst_arith_msb;
logic [ic_word_num-1:0] w_inst_mem_msb;

generate for (genvar w_idx = 0; w_idx < ic_word_num; w_idx++) begin : word_loop
  logic raw_cat;
  decoder_cat
  u_decoder_cat (
                .inst(inst_buffer_q[0][w_idx*32+:32]),
                .cat(raw_cat)
                );
  assign w_inst_cat[w_idx] = mrh_pkg::inst_cat_t'(raw_cat);

  assign w_inst_is_arith[w_idx] = w_inst_cat[w_idx] == mrh_pkg::CAT_ARITH;
  assign w_inst_is_mem  [w_idx] = w_inst_cat[w_idx] == mrh_pkg::CAT_MEM;

end
endgenerate

bit_extract_msb #(.WIDTH(ic_word_num)) u_bit_arith_msb (.in(w_inst_is_arith), .out(w_inst_arith_msb));
bit_extract_msb #(.WIDTH(ic_word_num)) u_bit_mem_msb   (.in(w_inst_is_mem  ), .out(w_inst_mem_msb  ));

endmodule // inst_buffer
