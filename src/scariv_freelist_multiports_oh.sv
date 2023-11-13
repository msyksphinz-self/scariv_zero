// ------------------------------------------------------------------------
// NAME : scariv_freelist_multiports_oh.sv
// TYPE : module
// ------------------------------------------------------------------------
// Freelist for Physical ID supporting Multiple Ports
// ------------------------------------------------------------------------
// ------------------------------------------------------------------------

module scariv_freelist_multiports_oh
  #(
    parameter WIDTH = 8,
    parameter PORTS = 2
    )
(
 input logic              i_clk,
 input logic              i_reset_n,

 input logic [WIDTH-1:0]  i_push_id[PORTS],
 input logic [PORTS-1: 0] i_pop,
 output logic [WIDTH-1:0] o_pop_id[PORTS],

 output logic             o_is_empty,
 output logic             o_is_full
 );

logic [WIDTH-1: 0]        r_active_bits;
logic [WIDTH-1: 0]        w_active_bits_next;

/* verilator lint_off UNOPTFLAT */
logic [WIDTH-1: 0]        w_poped_bit[PORTS+1];
assign w_poped_bit[0] = r_active_bits;

always_comb begin
  w_active_bits_next = r_active_bits;
  for (int p_idx = 0; p_idx < PORTS; p_idx++) begin
    w_active_bits_next = w_active_bits_next | i_push_id[p_idx];
  end
  if (|i_pop) begin
    w_active_bits_next = r_active_bits ^ w_poped_bit[PORTS];
  end
end // always_comb

always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_active_bits <= {WIDTH{1'b1}};
  end else begin
    r_active_bits <= w_active_bits_next;
  end
end // always_ff @ (posedge i_clk, negedge i_reset_n)

generate for (genvar p_idx = 0; p_idx < PORTS; p_idx++) begin : out_loop
  logic [WIDTH-1: 0] w_pop_tmp;
  bit_extract_lsb u_extract_lsb (.in(w_poped_bit[p_idx]), .out(w_pop_tmp));
  assign o_pop_id   [p_idx  ] = i_pop[p_idx] ? w_pop_tmp : w_poped_bit[p_idx];
  assign w_poped_bit[p_idx+1] = w_poped_bit[p_idx] ^ o_pop_id[p_idx];
end endgenerate

assign o_is_empty = &r_active_bits;
assign o_is_full  = r_active_bits == 'h0;

endmodule // scariv_freelist_multiports_oh
