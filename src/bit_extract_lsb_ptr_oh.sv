module bit_extract_lsb_ptr_oh
  #(
    parameter WIDTH = 32
    )
(
 input logic [WIDTH-1:0]  in,
 input logic [WIDTH-1:0]  i_ptr_oh,
 output logic [WIDTH-1:0] out
 );

logic [WIDTH-1: 0]        right_shift_mask;
logic [WIDTH-1: 0]        left_shift_mask;
/* verilator lint_off WIDTH */
assign right_shift_mask = (i_ptr_oh - 1)    & in;
assign left_shift_mask  = ~right_shift_mask & in;

if (WIDTH == 1) begin
  assign out = i_ptr_oh;
end else begin
  logic [WIDTH-1: 0]        right_shift_mask_oh;
  logic [WIDTH-1: 0]        left_shift_mask_oh;
  bit_extract_lsb #(.WIDTH(WIDTH)) u_bit_extract_lsb_left (.in(left_shift_mask ), .out(left_shift_mask_oh));
  bit_extract_lsb #(.WIDTH(WIDTH)) u_bit_extract_lsb_right(.in(right_shift_mask), .out(right_shift_mask_oh));

  assign out = |left_shift_mask ? left_shift_mask_oh : right_shift_mask_oh;
end

endmodule // bit_extract_lsb_ptr_oh
