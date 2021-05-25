module inoutptr_var_oh
  #(
    parameter SIZE = 32
    )
(
 input logic                    i_clk,
 input logic                    i_reset_n,

 input logic                    i_rollback,

 input logic                    i_in_valid,
 input logic [$clog2(SIZE)-1:0] i_in_val,
 output logic [SIZE-1:0]        o_in_ptr_oh,
 input logic                    i_out_valid,
 input logic [$clog2(SIZE)-1:0] i_out_val,
 output logic [SIZE-1:0]        o_out_ptr_oh
 );

logic [SIZE-1:0] r_inptr_oh;
logic [SIZE-1:0] r_outptr_oh;

logic [SIZE*2-1:0] w_inptr_2x_oh_next;
logic [SIZE*2-1:0] w_outptr_2x_oh_next;

logic [SIZE-1:0] w_inptr_oh_next;
logic [SIZE-1:0] w_outptr_oh_next;

assign w_inptr_2x_oh_next  = {{SIZE{1'b0}}, r_inptr_oh} << (i_in_valid ? i_in_val : 'h0);
assign w_outptr_2x_oh_next = i_rollback  ? w_inptr_2x_oh_next :
                             {{SIZE{1'b0}}, r_outptr_oh} << (i_out_valid ? i_out_val : 'h0);

assign w_inptr_oh_next = w_inptr_2x_oh_next[SIZE +: SIZE] |
                         w_inptr_2x_oh_next[0    +: SIZE];
assign w_outptr_oh_next = w_outptr_2x_oh_next[SIZE +: SIZE] |
                          w_outptr_2x_oh_next[0    +: SIZE];

always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_inptr_oh  <= {{(SIZE-1){1'b0}}, 1'b1};
    r_outptr_oh <= {{(SIZE-1){1'b0}}, 1'b1};
  end else begin
    r_inptr_oh  <= w_inptr_oh_next;
    r_outptr_oh <= w_outptr_oh_next;
  end
end


assign o_in_ptr_oh  = r_inptr_oh;
assign o_out_ptr_oh = r_outptr_oh;

endmodule // inoutptr_var_oh
