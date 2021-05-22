module simple_arbiter
  #(
    parameter WIDTH = 4
    )
(
 input logic [WIDTH-1: 0]  i_valid,
 output logic [WIDTH-1: 0] o_accept
 );

bit_extract_lsb #(.WIDTH(WIDTH)) bit_arbiter (.in(i_valid), .out(o_accept));

endmodule // simple_arbiter
