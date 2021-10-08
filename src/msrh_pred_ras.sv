module msrh_pred_ras
  (
   input logic                                              i_clk,
   input logic                                              i_reset_n,

   input logic                                              i_wr_valid[msrh_conf_pkg::BRU_DISP_SIZE],
   input logic [$clog2(msrh_conf_pkg::RAS_ENTRY_SIZE)-1:0]  i_wr_index[msrh_conf_pkg::BRU_DISP_SIZE],
   input logic [riscv_pkg::PADDR_W-1: 0]                    i_wr_pa   [msrh_conf_pkg::BRU_DISP_SIZE],

   output logic                                             i_rd_valid,
   output logic [$clog2(msrh_conf_pkg::RAS_ENTRY_SIZE)-1:0] i_rd_index,
   output logic [riscv_pkg::PADDR_W-1: 0]                   o_rd_pa
   );

logic [riscv_pkg::PADDR_W-1: 0] r_ras_array[msrh_conf_pkg::RAS_ENTRY_SIZE];

always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    for (int i = 0; i < msrh_conf_pkg::RAS_ENTRY_SIZE; i++) begin
      r_ras_array[i] <= 'h0;
    end
  end else begin
    for (int d_idx = 0; d_idx < msrh_conf_pkg::BRU_DISP_SIZE; d_idx++) begin
      if (i_wr_valid[d_idx]) begin
        r_ras_array[i_wr_index[d_idx]] <= i_wr_pa[d_idx];
      end
    end
  end
end

assign o_rd_pa = i_rd_valid ? r_ras_array[i_rd_index] : 'h0;

endmodule // msrh_ras
