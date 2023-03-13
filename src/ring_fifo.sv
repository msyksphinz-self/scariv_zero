// ------------------------------------------------------------------------
// NAME : Ring FIFO
// TYPE : module
// ------------------------------------------------------------------------
// Synchronized Ring FIFO
// ------------------------------------------------------------------------
//
// ------------------------------------------------------------------------

module ring_fifo
  #(
    parameter type T = logic[31: 0],
    parameter DEPTH = 4
  )
(
 input logic i_clk,
 input logic i_reset_n,

 input logic i_push,
 input T     i_data,

 output logic o_empty,
 output logic o_full,

 input logic i_pop,
 output T    o_data
 );

logic [$bits(T)-1: 0] r_fifo[DEPTH];

logic [$clog2(DEPTH)-1:0] r_inptr;
logic [$clog2(DEPTH)-1:0] r_outptr;
logic [$clog2(DEPTH)-1: 0] w_inptr_next;
logic [$clog2(DEPTH)-1: 0] w_outptr_next;


always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_inptr  <= 'h0;
    r_outptr <= 'h0;
  end else begin
    if (i_push & !o_full) begin
      r_inptr <= w_inptr_next;
    end
    if (i_pop & !o_empty) begin
      r_outptr <= w_outptr_next;
    end
  end // else: !if(!i_reset_n)
end // always_ff @ (posedge i_clk, negedge i_reset_n)


always_ff @ (posedge i_clk) begin
  if (i_push & !o_full) begin
    r_fifo[r_inptr] <= i_data;
  end
end

assign w_inptr_next  = r_inptr  + 'h1;
assign w_outptr_next = r_outptr + 'h1;

assign o_empty = r_inptr == r_outptr;
assign o_full  = w_inptr_next == r_outptr;

assign o_data = r_fifo[r_outptr];

endmodule // ring_fifo
