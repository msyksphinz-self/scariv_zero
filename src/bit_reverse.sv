module bit_reverse
  #(
    parameter WIDTH = 5
    )
(
 input logic [WIDTH-1:0]  in,
 output logic [WIDTH-1:0] out
 );

generate for(genvar a = 0; a < WIDTH; a=a+1) begin : gen_bus_swizzle
  assign out[a] = in[WIDTH-1-a];
end
endgenerate

endmodule // bit_reverse
