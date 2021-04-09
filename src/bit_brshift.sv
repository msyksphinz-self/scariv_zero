module bit_brshift
  #(
    parameter WIDTH = 4
    )
(
 input logic [WIDTH-1:0]  in,
 input logic [WIDTH-1:0]  i_sel,
 output logic [WIDTH-1:0] out
 );

genvar                    a, i, j;
logic [WIDTH-1:0] bus_array[WIDTH];

generate for(genvar i = 0; i < WIDTH; i++) begin : gen_outer
  for(genvar j = 0; j < WIDTH; j++) begin  : gen_inner
    assign bus_array[i][j] = in[((i+j)>=WIDTH) ? (i+j)-WIDTH : (i+j)];
  end
end
endgenerate

generate for(genvar a = 0; a < WIDTH; a++) begin : gen_bit_mux
  assign out[a] = |(bus_array[a] & i_sel);
end
endgenerate

endmodule // bit_brshift
