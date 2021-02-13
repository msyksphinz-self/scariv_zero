module bit_pick_1_index
  #(
    parameter NUM = 5,
    parameter SEL_WIDTH = 10,
    parameter DATA_WIDTH = 32
    )
(
 input logic [SEL_WIDTH-1:0]   i_valids,
 input logic [DATA_WIDTH-1: 0] i_data[SEL_WIDTH],

 output logic                  o_valid,
 output logic [DATA_WIDTH-1:0] o_data,
 output logic [SEL_WIDTH-1:0]  o_picked_pos
 );

/* verilator lint_off UNOPTFLAT */
logic [SEL_WIDTH-1:0]    w_index_hit;
/* verilator lint_off UNOPTFLAT */
logic [$clog2(DATA_WIDTH)-1:0] w_valid_cnt[DATA_WIDTH];
logic [$clog2(DATA_WIDTH)-1:0] w_valid_next_cnt[DATA_WIDTH];

assign w_valid_cnt[0]      = 'h0;
assign w_index_hit[0]      = i_valids[0] && w_valid_cnt[0] == NUM[$clog2(DATA_WIDTH)-1:0];
assign w_valid_next_cnt[0] = i_valids[0] ? w_valid_cnt[0] + 'h1 : w_valid_cnt[0];

generate for (genvar i = 1; i < SEL_WIDTH; i++) begin : bit_pick_loop
  always_comb begin
    if (i_valids[i]) begin
      /* verilator lint_off ALWCOMBORDER */
      w_valid_cnt     [i] = w_valid_next_cnt[i-1];
      w_valid_next_cnt[i] = w_valid_next_cnt[i-1] + 'h1;
    end else begin
      w_valid_cnt     [i] = w_valid_cnt[i-1];
      w_valid_next_cnt[i] = w_valid_next_cnt[i-1];
    end
    w_index_hit[i] = i_valids[i] && w_valid_cnt[i] == NUM[$clog2(DATA_WIDTH)-1:0];
  end // always_comb
end // block: bit_pick_loop
endgenerate

bit_oh_or #(.WORDS(SEL_WIDTH), .WIDTH(DATA_WIDTH)) u_select (.i_oh(w_index_hit), .i_data(i_data), .o_selected(o_data));
assign o_valid = |w_index_hit;
assign o_picked_pos = w_index_hit;

endmodule // bit_pick_1_index
