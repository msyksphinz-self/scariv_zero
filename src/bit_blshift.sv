module bit_blshift
  #(
    parameter WIDTH = 4
    )
(
 input logic [WIDTH-1:0]  in,
 input logic [WIDTH-1:0]  i_sel,
 output logic [WIDTH-1:0] out
);


logic [WIDTH-1:0]         in_reversed;
logic [WIDTH-1:0]         rslt;

bit_reverse #(.WIDTH(WIDTH)) reverse_in  (.in(in), .out(in_reversed));
bit_brshift #(.WIDTH(WIDTH)) brshift_0   (.in(in_reversed), .i_sel(i_sel), .out(rslt));
bit_reverse #(.WIDTH(WIDTH)) reverse_rslt(.in(rslt), .out(out));

endmodule
