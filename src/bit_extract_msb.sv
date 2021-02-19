module bit_extract_msb
  #(
    parameter WIDTH = 32
    )
(
 input logic [WIDTH-1:0]  in,
 output logic [WIDTH-1:0] out
 );

logic [WIDTH-1:0]         tree;
bit_tree_msb #(.WIDTH(WIDTH)) u_bit_tree (.in(in), .out(tree));

assign out = tree ^ {1'b0, tree[WIDTH-1:1]};

endmodule // bit_ff_lsb
