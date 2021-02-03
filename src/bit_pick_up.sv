module bit_pick_up
  #(
    parameter NUM = 5,
    parameter WIDTH = 32
    )
(
 input [WIDTH-1:0]  in,
 output [WIDTH-1:0] out
 );

/* verilator lint_off UNOPTFLAT */
logic [WIDTH-1:0]           pick_up_off;
/* verilator lint_off UNOPTFLAT */
logic [$clog2(WIDTH)-1:0]   pick_up_cnt[WIDTH];

assign pick_up_cnt[0] = in[0] ? 'h1 : 'h0;
assign pick_up_off[0] = pick_up_cnt[0] > NUM;
assign out[0] = in[0] & pick_up_cnt[0] <= NUM;

generate for (genvar i = 1; i < WIDTH; i++) begin : bit_pick_loop
  always_comb begin
    if (in[i] & !pick_up_off[i-1]) begin
      /* verilator lint_off ALWCOMBORDER */
      pick_up_cnt[i] = pick_up_cnt[i-1] + 'h1;
      out[i] = in[i];
    end else begin
      pick_up_cnt[i] = pick_up_cnt[i-1];
      out[i] = 1'b0;
    end
    pick_up_off[i] = pick_up_cnt[i] >= NUM;
  end // always_comb
end // block: bit_pick_loop
endgenerate

endmodule // bit_pick_up
