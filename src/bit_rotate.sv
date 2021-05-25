module bit_rotate_left
  #(
    parameter WIDTH = 32,
    parameter VAL = 3
    )
(
 input logic [WIDTH-1: 0] i_in,
 output logic [WIDTH-1: 0] o_out
 );

generate if (VAL == 0) begin
  assign o_out = i_in;
end else begin
  assign o_out = {i_in[WIDTH-VAL-1: 0], i_in[WIDTH-1: WIDTH-VAL]};
end
endgenerate

endmodule // bit_rotate_left
