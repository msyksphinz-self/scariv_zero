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

 input logic [ 7: 0]  i_update_valid,
 input logic [ 7: 0]  i_update_value,

 output logic [ 7: 0] o_data
 );

logic [ 7: 0] r_data;


generate for (genvar s_idx = 0; s_idx < 8; s_idx++) begin : source_loops
  always_ff @ (posedge i_clk, negedge i_reset_n) begin
    if (!i_reset_n) begin
      r_data[s_idx] <= 'h0;
    end else begin
      if (i_update_valid[s_idx]) begin
        r_data[s_idx] <= i_update_value[s_idx];
      end else if (i_wr & i_wr_byte_en) begin
        r_data[s_idx] <= i_wr_data[s_idx];
      end
    end
  end // always_ff @ (posedge i_clk, negedge i_reset_n)
end endgenerate // block: always_ff


assign o_data = r_data;

initial begin
  assert(NUM_PENDING <= 8);
end

endmodule // scariv_plic_reg_pending
