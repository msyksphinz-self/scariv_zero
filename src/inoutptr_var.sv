module inoutptr_var
  #(
    parameter SIZE = 32
    )
(
 input logic                     i_clk,
 input logic                     i_reset_n,

 input logic                     i_rollback,

 input logic                     i_in_vld,
 input logic [$clog2(SIZE)-1:0]  i_in_val,
 output logic [$clog2(SIZE)-1:0] o_in_ptr,
 input logic                     i_out_vld,
 input logic [$clog2(SIZE)-1:0]  i_out_val,
 output logic [$clog2(SIZE)-1:0] o_out_ptr
 );

logic [$clog2(SIZE)-1:0] r_inptr;
logic [$clog2(SIZE)-1:0] r_outptr;

logic [$clog2(SIZE)-1:0] w_inptr_next;
logic [$clog2(SIZE)-1:0] w_outptr_next;

assign w_inptr_next  = i_rollback ? w_outptr_next :
                       i_in_vld   ? r_inptr + i_in_val  :
                       r_inptr;
assign w_outptr_next = i_out_vld  ? r_outptr + i_out_val :
                       r_outptr;


always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_inptr  <= 'h0;
    r_outptr <= 'h0;
  end else begin
    r_inptr  <= w_inptr_next;
    r_outptr <= w_outptr_next;
  end
end

assign o_in_ptr  = r_inptr;
assign o_out_ptr = r_outptr;

endmodule // inoutptr
