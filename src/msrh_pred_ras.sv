module msrh_pred_ras
  (
   input logic                                              i_clk,
   input logic                                              i_reset_n,

   input logic                                              i_wr_valid,
   input logic [$clog2(msrh_conf_pkg::RAS_ENTRY_SIZE)-1:0]  i_wr_index,
   input logic [riscv_pkg::VADDR_W-1: 1]                    i_wr_pa ,

   output logic                                             i_rd_valid,
   output logic [$clog2(msrh_conf_pkg::RAS_ENTRY_SIZE)-1:0] i_rd_index,
   output logic [riscv_pkg::VADDR_W-1: 1]                   o_rd_pa,

   input logic                                              i_br_call_cmt_valid,
   input logic [$clog2(msrh_conf_pkg::RAS_ENTRY_SIZE)-1:0]  i_br_call_cmt_ras_index,
   input logic                                              i_br_call_recover_valid,
   input logic [$clog2(msrh_conf_pkg::RAS_ENTRY_SIZE)-1:0]  i_br_call_recover_ras_index
   );

logic [riscv_pkg::VADDR_W-1: 1] r_ras_array[msrh_conf_pkg::RAS_ENTRY_SIZE];
logic [riscv_pkg::VADDR_W-1: 1] r_ras_cmt_array[msrh_conf_pkg::RAS_ENTRY_SIZE];

always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    for (int i = 0; i < msrh_conf_pkg::RAS_ENTRY_SIZE; i++) begin
      r_ras_array[i] <= 'h0;
      r_ras_cmt_array[i] <= 'h0;
    end
  end else begin
    if (i_wr_valid) begin
      r_ras_array[i_wr_index] <= i_wr_pa;
    end else if (i_br_call_recover_valid) begin
      r_ras_array[i_br_call_recover_ras_index] <= r_ras_cmt_array[i_br_call_recover_ras_index];
    end
    if (i_br_call_cmt_valid) begin
      r_ras_cmt_array[i_br_call_cmt_ras_index] <= r_ras_array[i_br_call_cmt_ras_index];
    end
  end
end

assign o_rd_pa = i_rd_valid ? r_ras_array[i_rd_index] : 'h0;

endmodule // msrh_ras
