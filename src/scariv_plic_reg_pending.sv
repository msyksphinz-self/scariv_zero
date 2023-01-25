module scariv_plic_reg_pending
  #(
    parameter NUM_PENDING = 8
    )
(
 input logic          i_clk,
 input logic          i_reset_n,

 input logic          i_wr,
 input logic          i_wr_byte_en,
 input logic [ 7: 0]  i_wr_data,

 output logic [ 7: 0] o_data
 );

logic [NUM_PENDING-1: 0] r_data;


always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_data <= 'h0;
  end else begin
    if (i_wr & i_wr_byte_en) begin
      r_data[EFFICTIVE_BITS-1: 0] <= i_wr_data[EFECTIVE_BITS-1: 0];
    end
  end
end
endgenerate

assign o_data = r_data;

initial begin
  $assert(NUM_PENDING <= 8);
end

endmodule // scariv_plic_reg_pending
