// `default_nettype none

module bit_oh_or
  #(
    parameter type T = logic[31: 0],
    parameter WORDS = 4
  )
(
  input logic [WORDS-1:0]  i_oh,
  input T                  i_data[WORDS],
  /* verilator lint_off UNOPTFLAT */
  output T                 o_selected
);
  // /* verilator lint_off UNOPTFLAT */
  // logic [$bits(T)-1: 0]    w_selected_array[WORDS];
  // assign w_selected_array[0] = {$bits(T){i_oh[0]}} & i_data[0];
  // generate for (genvar i = 1; i < WORDS; i++) begin : oh_loop
  //   assign w_selected_array[i] = w_selected_array[i-1] | {$bits(T){i_oh[i]}} & i_data[i];
  // end
  // endgenerate
logic [$clog2(WORDS)-1: 0] idx;
function automatic logic [$clog2(WORDS)-1: 0] encoder (logic [WORDS-1: 0] in);
  for (int i = 0; i < WORDS; i++) begin
    if (in[i]) return i;
  end
  return 0;
endfunction // encoder

assign o_selected = ~|i_oh ? 'h0 : i_data[encoder(i_oh)];

endmodule

// `default_nettype wire
