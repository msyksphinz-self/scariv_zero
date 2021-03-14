module bit_oh_or_packed
  #(
    parameter WIDTH = 32,
    parameter WORDS = 4
  )
(
  input logic [WORDS-1:0]            i_oh,
  input logic [WORDS-1:0][WIDTH-1:0] i_data,
  output logic [WIDTH-1:0]           o_selected
);

logic [WIDTH-1:0]                    w_data[WORDS];
generate for (genvar i = 0; i < WORDS; i++) begin
  assign w_data[i] = i_data[i];
end
endgenerate

bit_oh_or #(.WIDTH(WIDTH), .WORDS(WORDS))
u_inst (.i_oh(i_oh), .i_data(w_data), .o_selected(o_selected));

endmodule
