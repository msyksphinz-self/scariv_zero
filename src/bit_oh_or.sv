// `default_nettype none

module bit_oh_or
  #(
    parameter type T = logic[31: 0],
    parameter WORDS = 4
  )
(
  input logic [WORDS-1:0]  i_oh,
  input T                  i_data[WORDS],
  output T                 o_selected
);
  /* verilator lint_off UNOPTFLAT */
  T w_selected_array[WORDS];
  assign w_selected_array[0] = T'({$size(T){i_oh[0]}} & i_data[0]);
  generate for (genvar i = 1; i < WORDS; i++) begin : oh_loop
    assign w_selected_array[i] = w_selected_array[i-1] | T'({$size(T){i_oh[i]}} & i_data[i]);
  end
  endgenerate
  assign o_selected = w_selected_array[WORDS-1];

endmodule

// `default_nettype wire
