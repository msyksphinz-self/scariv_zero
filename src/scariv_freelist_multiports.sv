// ------------------------------------------------------------------------
// NAME : scariv_freelist_multiports.sv
// TYPE : module
// ------------------------------------------------------------------------
// Freelist for Physical ID supporting Multiple Ports
// ------------------------------------------------------------------------
// ------------------------------------------------------------------------

module scariv_freelist_multiports
  #(
    parameter SIZE = 32,
    parameter WIDTH = 5,
    parameter PORTS = 2
    )
(
 input logic              i_clk,
 input logic              i_reset_n,

 input logic [PORTS-1: 0] i_push,
 input logic [WIDTH-1:0]  i_push_id[PORTS],

 input logic [PORTS-1: 0] i_pop,
 output logic [WIDTH-1:0] o_pop_id[PORTS],

 output logic             o_is_empty
 );

logic [WIDTH-1:0]         r_freelist[SIZE];
logic [SIZE-1: 0]         r_active_bits;

logic [$clog2(SIZE)-1:0]  r_head_ptr;
logic [$clog2(SIZE)-1:0]  r_tail_ptr;
logic [$clog2(SIZE)-1:0]  w_head_ptr_next;
logic [$clog2(SIZE)-1:0]  w_tail_ptr_next;

logic [$clog2(SIZE)-1:0]  w_head_ptr[PORTS];
logic [$clog2(SIZE)-1:0]  w_tail_ptr[PORTS];

function automatic logic [$clog2(PORTS): 0] count_ones(logic [PORTS-1: 0] bits);
  logic [$clog2(PORTS): 0]  ret;
  ret = 0;
  for (int i = 0; i < PORTS; i++) ret = ret + bits[i];
  return ret;
endfunction // count_ones

generate if (SIZE == 1 << $clog2(SIZE)) begin : size_2pow
  for (genvar p_idx = 0; p_idx < PORTS; p_idx++) begin : ports_loop
    assign w_head_ptr[p_idx] = r_head_ptr + p_idx;
    assign w_tail_ptr[p_idx] = r_tail_ptr + p_idx;
  end
  assign w_head_ptr_next = r_head_ptr + count_ones(i_pop);
  assign w_tail_ptr_next = r_tail_ptr + count_ones(i_push);
end else if (PORTS == 1) begin : single_port
  for (genvar p_idx = 0; p_idx < PORTS; p_idx++) begin : ports_loop
    assign w_head_ptr[p_idx] = r_head_ptr;
    assign w_tail_ptr[p_idx] = r_tail_ptr;
  end
  assign w_head_ptr_next = r_head_ptr < SIZE-1 ? r_head_ptr + 1 : 'h0;
  assign w_tail_ptr_next = r_tail_ptr < SIZE-1 ? r_tail_ptr + 1 : 'h0;
end else begin : multi_port
  for (genvar p_idx = 0; p_idx < PORTS; p_idx++) begin : ports_loop
    assign w_head_ptr[p_idx] = r_head_ptr + p_idx < SIZE ? r_head_ptr + p_idx : r_head_ptr + p_idx - SIZE;
    assign w_tail_ptr[p_idx] = r_tail_ptr + p_idx < SIZE ? r_tail_ptr + p_idx : r_tail_ptr + p_idx - SIZE;
  end
  wire [$clog2(SIZE): 0] w_head_ptr_update = r_head_ptr + count_ones(i_pop);
  wire [$clog2(SIZE): 0] w_tail_ptr_update = r_tail_ptr + count_ones(i_push);

  assign w_head_ptr_next = w_head_ptr_update < SIZE-1 ? w_head_ptr_update : w_head_ptr_update - SIZE;
  assign w_tail_ptr_next = w_tail_ptr_update < SIZE-1 ? w_tail_ptr_update : w_tail_ptr_update - SIZE;
end endgenerate

always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_head_ptr <= 'h0;
    r_tail_ptr <= 'h0;
    r_active_bits <= {SIZE{1'b1}};
    for (int i = 0; i < SIZE; i++) begin
      /* verilator lint_off WIDTH */
      r_freelist[i] <= i;
    end
  end else begin
    if (|i_push) begin
      r_tail_ptr <= w_tail_ptr_next;
    end
    if (|i_pop) begin
      r_head_ptr <= w_head_ptr_next;
    end

    for (int p_idx = 0; p_idx < PORTS; p_idx++) begin
      if (i_push[p_idx]) begin
        r_freelist[w_tail_ptr[p_idx]] <= i_push_id[p_idx];
        r_active_bits[w_tail_ptr[p_idx]] <= 1'b1;
      end
      if (i_pop[p_idx]) begin
        r_active_bits[w_head_ptr[p_idx]] <= 1'b0;
`ifdef SIMULATION
        // delete poped ID for debug
        r_freelist[w_head_ptr[p_idx]] <= 'h0;
`endif // SIMULATION
      end
    end // for (int p_idx = 0; p_idx < PORTS; p_idx++)
  end // else: !if(!i_reset_n)
end // always_ff @ (posedge i_clk, negedge i_reset_n)


generate for (genvar p_idx = 0; p_idx < PORTS; p_idx++) begin : out_loop
  assign o_pop_id[p_idx] = r_freelist[w_head_ptr[p_idx]];
end
endgenerate

assign o_is_empty = ~(|r_active_bits);

endmodule // scariv_freelist
