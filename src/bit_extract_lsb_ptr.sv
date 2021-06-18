module bit_extract_lsb_ptr
  #(
    parameter WIDTH = 32
    )
(
 input logic [WIDTH-1:0]          in,
 input logic [$clog2(WIDTH)-1: 0] i_ptr,
 output logic [WIDTH-1:0]         out
 );

logic [WIDTH-1: 0]                shifted_in;
logic [WIDTH-1: 0]                shifted_out;
/* verilator lint_off WIDTH */
assign shifted_in = ((in >> i_ptr) & ((1 << (WIDTH-i_ptr))-1)) | (in << (WIDTH-i_ptr));

if (WIDTH == 1) begin
  assign out = shifted_in;
end else begin
  logic [WIDTH-1:0]         tree;
  bit_tree_lsb #(.WIDTH(WIDTH)) u_bit_tree (.in(shifted_in), .out(tree));
  assign shifted_out = tree ^ {tree[WIDTH-2:0], 1'b0};
end

assign out = (shifted_out << i_ptr)  | (shifted_out >> (WIDTH-i_ptr));

endmodule // bit_extract_lsb
