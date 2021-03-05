module bit_extract_lsb
  #(
    parameter WIDTH = 32
    )
(
 input logic [WIDTH-1:0]  in,
 output logic [WIDTH-1:0] out
 );

if (WIDTH == 1) begin
  assign out = in;
end else begin
  logic [WIDTH-1:0]         tree;
  bit_tree_lsb #(.WIDTH(WIDTH)) u_bit_tree (.in(in), .out(tree));
  assign out = tree ^ {tree[WIDTH-2:0], 1'b0};
end

endmodule // bit_extract_lsb
