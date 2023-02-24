// ------------------------------------------------------------------------
// NAME : Ring FIFO 2-ptr
// TYPE : module
// ------------------------------------------------------------------------
// Synchronized Ring FIFO with 2-pointer, pointing 1st and 2nd entry
// ------------------------------------------------------------------------
//
// ------------------------------------------------------------------------

module ring_fifo_2ptr
  #(
    parameter type T = logic[31: 0],
    parameter DEPTH = 4
  )
(
 input logic  i_clk,
 input logic  i_reset_n,

 input logic  i_clear,

 input logic  i_push,
 input        T i_data,

 output logic o_empty,
 output logic o_full,

 input logic  i_pop,

 output logic o_valid0,
 output T     o_data0,

 output logic o_valid1,
 output T     o_data1
 );

logic [$bits(T)-1: 0] r_fifo[DEPTH];
logic [DEPTH-1: 0]    r_valids;

logic [$clog2(DEPTH)-1:0] r_inptr;
logic [$clog2(DEPTH)-1:0] r_outptr;
logic [$clog2(DEPTH)-1: 0] w_inptr_next;
logic [$clog2(DEPTH)-1: 0] w_outptr_next;


always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_inptr  <= 'h0;
    r_outptr <= 'h0;
    r_valids <= 'h0;
  end else begin
    if (i_clear) begin
      r_outptr <= 'h0;
      r_inptr  <= 'h0;
      r_valids <= 'h0;
    end else begin
      if (i_pop & !o_empty) begin
        r_outptr <= w_outptr_next;
        r_valids[r_outptr] <= 1'b0;
      end
      if (i_push & !o_full) begin
        r_inptr <= w_inptr_next;
        r_valids[r_inptr] <= 1'b1;
      end
    end // else: !if(i_clear)
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

assign o_valid0 = r_valids[r_outptr];
assign o_data0  = r_fifo  [r_outptr];

assign o_valid1 = r_valids[w_outptr_next];
assign o_data1  = r_fifo  [w_outptr_next];

endmodule // ring_fifo_2ptr
