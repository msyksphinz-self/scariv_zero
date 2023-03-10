// ------------------------------------------------------------------------
// NAME : bit_encoder.sv
// TYPE : module
// ------------------------------------------------------------------------
// Encoder:
// 001 -> 0
// 010 -> 1
// 100 -> 2
// ------------------------------------------------------------------------
//
// ------------------------------------------------------------------------


module bit_encoder
  #(
    parameter WIDTH = 16
    )
(
 input logic [WIDTH-1: 0] i_in,
 output logic [$clog2(WIDTH)-1: 0] o_out
 );

logic [$clog2(WIDTH)-1: 0]         w_const_array[WIDTH];

generate for (genvar w_idx = 0; w_idx < WIDTH; w_idx++) begin : const_loop
  assign w_const_array[w_idx] = w_idx;
end endgenerate

bit_oh_or #(.T(logic[$clog2(WIDTH)-1:0]), .WORDS(WIDTH)) bit_oh_select (.i_oh(i_in), .i_data(w_const_array), .o_selected(o_out));

endmodule // bit_encoder
