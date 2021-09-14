module transpose_matrix
  #(
    parameter WIDTH = 3,
    parameter WORDS = 4
    )
(
 input logic [WIDTH-1 : 0]  in [WORDS]
 output logic [WORDS-1 : 0] out [WIDTH]
 );

generate for (genvar v_idx = 0; v_idx < WORDS; v_idx++) begin : vertical
  for (genvar h_idx = 0; h_idx < WIDTH; h_idx++) begin : horizontal
    assign out[h_idx][v_idx] = in[v_idx][h_idx];
  end
end
endgenerate

endmodule // transpose_matrix
