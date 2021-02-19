module encoder
  #(
    parameter SIZE = 32
    )
(
 input logic [SIZE-1: 0]  i_in,
 output logic [$clog2(SIZE)-1: 0] o_out
 );

function logic [$clog2(SIZE)-1: 0] encoder_func(logic [SIZE-1: 0] in);
  for (int i = 0; i < SIZE; i++) begin
    if (in[i]) return i[$clog2(SIZE)-1:0];
  end
  return 0;
endfunction // encoder_func

assign o_out = encoder_func(i_in);

endmodule // encoder
