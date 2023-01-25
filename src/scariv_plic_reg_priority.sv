module scariv_plic_reg_priority
  #(
    parameter NUM_PRIORITY = 8
    )
(
 input logic          i_clk,
 input logic          i_reset_n,

 input logic          i_wr,
 input logic [ 3: 0]  i_wr_byte_en,
 input logic [31: 0]  i_wr_data,

 output logic [31: 0] o_data
 );

logic [$clog2(NUM_PRIORITY)-1: 0] r_data;


generate for (genvar b_idx = 0; b_idx < 4; b_idx++) begin
  if (b_idx * 8 < $clog2(NUM_PRIORITY)) begin
    localparam EFFICTIVE_BITS = ($clog2(NUM_PRIORITY) - b_idx * 8) % 8;
    always_ff @ (posedge i_clk, negedge i_reset_n) begin
      if (!i_reset_n) begin
        r_data[b_idx*8 +: EFFICTIVE_BITS] <= 'h0;
      end else begin
        if (i_wr & i_wr_byte_en[b_idx]) begin
          r_data[b_idx*8 +: EFFICTIVE_BITS] <= i_wr_data[b_idx * 8 +: EFECTIVE_BITS];
        end
      end
    end
  end
end
endgenerate

assign o_data = r_data;

endmodule // scariv_plic_reg_priority
