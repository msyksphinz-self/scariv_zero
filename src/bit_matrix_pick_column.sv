module bit_matrix_pick_column
  #(
    parameter WIDTH = 3,
    parameter WORDS = 4,
    parameter H_IDX = 2
    )
(
 input logic [WIDTH-1 : 0]  in [WORDS]
 output logic [WORDS-1 : 0] out
 );

generate for (genvar v_idx = 0; v_idx < WORDS; v_idx++) begin : vertical
  assign out[v_idx] = in[v_idx][H_IDX];
end
endgenerate

endmodule // bit_matrix_pick_column
