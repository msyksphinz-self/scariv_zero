module bit_ff_lsb
  #(
    parameter WIDTH = 32
    )
(
 input [WIDTH-1:0]          in,
 output                     valid,
 output [$clog2(WIDTH)-1:0] out
 );

/* verilator lint_off UNOPTFLAT */
logic [WIDTH-1:0]           vld_array;
/* verilator lint_off UNOPTFLAT */
logic [$clog2(WIDTH)-1:0]   result_val[WIDTH];

assign vld_array[0]  = in[0];
assign result_val[0] = 'h0;

generate for (genvar i = 1; i < WIDTH; i++) begin : bit_ff_loop
  always_comb begin
    if (in[i]) begin
      if (vld_array[i-1]) begin
        vld_array[i]  = 1'b1;
        /* verilator lint_off ALWCOMBORDER */
        result_val[i] = result_val[i-1];
      end else begin
        vld_array[i]  = 1'b1;
        result_val[i] = i;
      end
    end else begin
      vld_array[i]  = vld_array[i-1];
      result_val[i] = result_val[i-1];
    end // else: !if(in[i])
  end // always_comb
end // block: bit_ff_loop
endgenerate


assign out = result_val[WIDTH-1];
assign valid = |in;

endmodule // bit_ff_lsb
