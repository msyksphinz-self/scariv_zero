// ------------------------------------------------------------------------
// NAME : scariv_freelist
// TYPE : module
// ------------------------------------------------------------------------
// Freelist for Physical ID
// ------------------------------------------------------------------------
// ------------------------------------------------------------------------

module scariv_freelist
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
 output logic [WIDTH-1:0] o_pop_id,

 output logic             o_is_empty
 );

logic [WIDTH-1:0]         r_freelist[SIZE];

logic [$clog2(SIZE)-1:0]  r_head_ptr;
logic [$clog2(SIZE)-1:0]  r_tail_ptr;

logic [SIZE-1:0]          r_active_bits;

always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_head_ptr <= 'h0;
    r_tail_ptr <= 'h0;
    r_active_bits <= {SIZE{1'b1}};
    for (int i = 0; i < SIZE; i++) begin
      /* verilator lint_off WIDTH */
      r_freelist[i] = INIT + i;
    end
  end else begin
    if (i_push) begin
      r_tail_ptr <= r_tail_ptr + 'h1;
      r_active_bits[r_tail_ptr] <= 1'b1;
      r_freelist[r_tail_ptr] <= i_push_id;
    end
    if (i_pop) begin
      r_head_ptr <= r_head_ptr + 'h1;
      r_active_bits[r_head_ptr] <= 1'b0;
`ifdef SIMULATION
      // delete poped ID for debug
      r_freelist[r_head_ptr] <= 'h0;
`endif // SIMULATION
    end
  end
end

assign o_pop_id = r_freelist[r_head_ptr];

assign o_is_empty = ~(|r_active_bits);

endmodule // scariv_freelist
