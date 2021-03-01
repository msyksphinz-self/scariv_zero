module bit_or
  #(
    parameter WIDTH = 32,
    parameter WORDS = 4
  )
(
  input logic [WIDTH-1:0]  i_data[WORDS],
  output logic [WIDTH-1:0] o_selected
);
  /* verilator lint_off UNOPTFLAT */
  logic [WIDTH-1:0] w_selected_array[WORDS];
  assign w_selected_array[0] = i_data[0];
  generate for (genvar i = 1; i < WORDS; i++) begin : loop
    assign w_selected_array[i] = w_selected_array[i-1] | i_data[i];
  end
  endgenerate
  assign o_selected = w_selected_array[WORDS-1];

endmodule
