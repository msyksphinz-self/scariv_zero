module bit_oh_or_packed
  #(
    parameter type T = logic[31: 0],
    parameter WORDS = 4
  )
(
  input logic [WORDS-1:0] i_oh,
  input T [WORDS-1:0]     i_data,
  output T                o_selected
);

T w_data[WORDS];
generate for (genvar i = 0; i < WORDS; i++) begin
  assign w_data[i] = i_data[i];
end
endgenerate

bit_oh_or #(.T(T), .WORDS(WORDS))
u_inst (.i_oh(i_oh), .i_data(w_data), .o_selected(o_selected));

endmodule
