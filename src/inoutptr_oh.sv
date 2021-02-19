module inoutptr_oh
  #(
    parameter SIZE = 32
    )
(
 input logic             i_clk,
 input logic             i_reset_n,

 input logic             i_in_vld,
 output logic [SIZE-1:0] o_in_ptr,
 input logic             i_out_vld,
 output logic [SIZE-1:0] o_out_ptr
 );

logic [SIZE-1:0] r_inptr;
logic [SIZE-1:0] r_outptr;

always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_inptr  <= {{(SIZE-1){1'b0}}, 1'b1};
    r_outptr <= {{(SIZE-1){1'b0}}, 1'b1};
  end else begin
    r_inptr  <= i_in_vld  ? {r_inptr [SIZE-2:1], r_inptr [SIZE-1]} : r_inptr;
    r_outptr <= i_out_vld ? {r_outptr[SIZE-2:1], r_outptr[SIZE-1]} : r_outptr;
  end
end

assign o_in_ptr  = r_inptr;
assign o_out_ptr = r_outptr;

endmodule // inoutptr_oh
