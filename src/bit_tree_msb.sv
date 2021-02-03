module bit_tree_msb
  #(
    parameter WIDTH = 32
    )
(
 input logic [WIDTH-1:0]  in,
 output logic [WIDTH-1:0] out
 );

localparam red_loop = $clog2(WIDTH);

/* verilator lint_off UNOPTFLAT */
logic [WIDTH-1:0]           in_shift_array[red_loop];

assign in_shift_array[0] = in;
generate for (genvar i = 1; i < red_loop; i++) begin : bit_ff_loop
  assign in_shift_array[i] = in_shift_array[i-1] | in_shift_array[i-1] >> (i * 2);
end
endgenerate

assign out = in_shift_array[red_loop-1];

endmodule // bit_tree_msb
