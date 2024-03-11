module inoutptr_oh
  #(
    parameter SIZE = 32
    )
(
 input logic             i_clk,
 input logic             i_reset_n,

 input logic             i_rollback,
 input logic             i_clear,

 input logic             i_in_valid,
 output logic [SIZE-1:0] o_in_ptr,
 input logic             i_out_valid,
 output logic [SIZE-1:0] o_out_ptr
 );

generate if (SIZE == 1) begin : size_eq_1
  assign o_in_ptr  = 1'b1;
  assign o_out_ptr = 1'b1;
end else begin: size_gt_1
  logic [SIZE-1:0] r_inptr;
  logic [SIZE-1:0] r_outptr;

  logic [SIZE-1:0] w_inptr_next;
  logic [SIZE-1:0] w_outptr_next;

  always_comb begin
    w_inptr_next = r_inptr;
    w_outptr_next = r_outptr;
    if (i_rollback) begin
      w_inptr_next  = r_outptr;
      w_outptr_next = r_outptr;
    end
    if (i_clear) begin
      w_inptr_next  = {{(SIZE-1){1'b0}}, 1'b1};
      w_outptr_next = {{(SIZE-1){1'b0}}, 1'b1};
    end
    if (i_in_valid) begin
      w_inptr_next = {w_inptr_next [SIZE-2:0], w_inptr_next [SIZE-1]};
    end
    if (i_out_valid) begin
      w_outptr_next = {w_outptr_next[SIZE-2:0], w_outptr_next[SIZE-1]};
    end
  end

  always_ff @ (posedge i_clk, negedge i_reset_n) begin
    if (!i_reset_n) begin
      r_inptr  <= {{(SIZE-1){1'b0}}, 1'b1};
      r_outptr <= {{(SIZE-1){1'b0}}, 1'b1};
    end else begin
      r_inptr  <= w_inptr_next;
      r_outptr <= w_outptr_next;
    end
  end

  assign o_in_ptr  = r_inptr;
  assign o_out_ptr = r_outptr;
end endgenerate

endmodule // inoutptr_oh
