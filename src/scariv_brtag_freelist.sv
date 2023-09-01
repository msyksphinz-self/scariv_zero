// ------------------------------------------------------------------------
// NAME : scariv_brtag_freelist
// TYPE : module
// ------------------------------------------------------------------------
// Freelist for Physical ID supporting Multiple Ports
// ------------------------------------------------------------------------
// ------------------------------------------------------------------------

module scariv_brtag_freelist
  #(
    parameter SIZE = 32,
    parameter WIDTH = 5,
    parameter PORTS = 2
    )
(
 input logic              i_clk,
 input logic              i_reset_n,

 input logic              i_push,
 input logic [WIDTH-1:0]  i_push_id,

 input logic [PORTS-1: 0] i_pop,
 output logic [WIDTH-1:0] o_pop_id[PORTS],

 output logic             o_is_empty
 );

logic [WIDTH-1:0]         r_freelist[SIZE];
logic [SIZE-1: 0]         r_active_bits;

logic [$clog2(SIZE)-1:0]  r_head_ptr;
logic [$clog2(SIZE)-1:0]  r_tail_ptr;

logic [$clog2(SIZE)-1:0]  w_tail_ptr;
/* verilator lint_off UNOPTFLAT */
logic [$clog2(SIZE)-1:0]  w_head_ptr_offset[PORTS+1];

assign w_head_ptr_offset[0] = r_head_ptr;
generate for (genvar p_idx = 0; p_idx < PORTS; p_idx++) begin : ports_loop
  assign w_head_ptr_offset[p_idx + 1] = w_head_ptr_offset[p_idx] + (i_pop[p_idx] ? 'h1 : 'h0);
end endgenerate

assign w_tail_ptr = r_tail_ptr;

always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_head_ptr <= 'h0;
    r_tail_ptr <= 'h0;
    r_active_bits <= {SIZE{1'b1}};
    for (int i = 0; i < SIZE; i++) begin
      /* verilator lint_off WIDTH */
      r_freelist[i] = i;
    end
  end else begin
    if (i_push) begin
      r_tail_ptr <= w_tail_ptr + 1'b1;
      r_freelist[w_tail_ptr] <= i_push_id;
      r_active_bits[w_tail_ptr] <= 1'b1;
    end
    if (|i_pop) begin
      r_head_ptr <= r_head_ptr + $countones(i_pop);
    end

    for (int p_idx = 0; p_idx < PORTS; p_idx++) begin
      if (i_pop[p_idx]) begin
        r_active_bits[w_head_ptr_offset[p_idx]] <= 1'b0;
`ifdef SIMULATION
        // delete poped ID for debug
        r_freelist[w_head_ptr_offset[p_idx]] <= 'h0;
`endif // SIMULATION
      end
    end // for (int p_idx = 0; p_idx < PORTS; p_idx++)
  end // else: !if(!i_reset_n)
end // always_ff @ (posedge i_clk, negedge i_reset_n)


generate for (genvar p_idx = 0; p_idx < PORTS; p_idx++) begin : out_loop
  assign o_pop_id[p_idx] = r_freelist[w_head_ptr_offset[p_idx]];
end endgenerate

assign o_is_empty = ~(|r_active_bits);

endmodule // scariv_brtag_freelist
