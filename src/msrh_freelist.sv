module msrh_freelist
  #(
    parameter SIZE = 32,
    parameter WIDTH = 5,
    parameter INIT = 0
    )
(
 input logic              i_clk,
 input logic              i_reset_n,

 input logic              i_push,
 input logic [WIDTH-1:0]  i_push_id,

 input logic              i_pop,
 output logic [WIDTH-1:0] o_pop_id
 );

logic [WIDTH-1:0]         r_freelist[SIZE];

logic [$clog2(SIZE)-1:0]  r_head_ptr;
logic [$clog2(SIZE)-1:0]  r_tail_ptr;

always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_head_ptr <= 'h0;
    r_tail_ptr <= 'h0;
    for (int i = 0; i < SIZE; i++) begin
      /* verilator lint_off WIDTH */
      r_freelist[i] <= INIT + i;
    end
  end else begin
    if (i_push) begin
      r_tail_ptr <= r_tail_ptr + 'h1;
      r_freelist[r_tail_ptr] <= i_push_id;
    end
    if (i_pop) begin
      r_head_ptr <= r_head_ptr + 'h1;
    end
  end
end

assign o_pop_id = r_freelist[r_head_ptr];

endmodule // msrh_freelist
