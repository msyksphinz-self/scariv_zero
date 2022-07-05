module msrh_pred_ras
  (
   input logic                                              i_clk,
   input logic                                              i_reset_n,

   input logic                                              i_wr_valid,
   input logic [$clog2(msrh_conf_pkg::RAS_ENTRY_SIZE)-1:0]  i_wr_index,
   input logic [riscv_pkg::VADDR_W-1: 1]                    i_wr_pa ,

   input  logic                                             i_s2_rd_valid,
   input  logic [$clog2(msrh_conf_pkg::RAS_ENTRY_SIZE)-1:0] i_s2_rd_index,
   output logic [riscv_pkg::VADDR_W-1: 1]                   o_s2_rd_pa,

   input logic                                              i_br_call_cmt_valid,
   input logic [$clog2(msrh_conf_pkg::RAS_ENTRY_SIZE)-1:0]  i_br_call_cmt_ras_index,
   input logic [riscv_pkg::VADDR_W-1: 1]                    i_br_call_cmt_wr_vpc
   );

logic [riscv_pkg::VADDR_W-1: 1] r_ras_array[msrh_conf_pkg::RAS_ENTRY_SIZE];

always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    for (int i = 0; i < msrh_conf_pkg::RAS_ENTRY_SIZE; i++) begin
      r_ras_array[i] <= 'h0;
    end
  end else begin
    if (i_wr_valid) begin
      r_ras_array[i_wr_index] <= i_wr_pa;
    end
    if (i_br_call_cmt_valid) begin
      r_ras_array[i_br_call_cmt_ras_index] <= i_br_call_cmt_wr_vpc;
    end
  end
end

assign o_s2_rd_pa = i_s2_rd_valid ? r_ras_array[i_s2_rd_index] : 'h0;

endmodule // msrh_ras
