module msrh_pred_ras
  import msrh_predict_pkg::*;
  import msrh_ic_pkg::*;
  (
   input logic i_clk,
   input logic i_reset_n,

   input logic        i_wr_valid,
   input ras_idx_t    i_wr_index,
   input ic_vaddr_h_t i_wr_pa ,

   input  logic        i_s2_rd_valid,
   input  ras_idx_t    i_s2_rd_index,
   output ic_vaddr_h_t o_s2_rd_pa,

   input logic        i_br_call_cmt_valid,
   input ras_idx_t    i_br_call_cmt_ras_index,
   input ic_vaddr_h_t i_br_call_cmt_wr_vpc
   );

ic_vaddr_h_t r_ras_array[msrh_conf_pkg::RAS_ENTRY_SIZE-1: 0];

always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    for (int i = 0; i < msrh_conf_pkg::RAS_ENTRY_SIZE; i++) begin
      r_ras_array[i] <= 'h0;
    end
  end else begin
    if (i_wr_valid) begin
      r_ras_array[i_wr_index] <= i_wr_pa;
    end
    // if (i_br_call_cmt_valid) begin
    //   r_ras_array[i_br_call_cmt_ras_index] <= i_br_call_cmt_wr_vpc;
    // end
  end
end

assign o_s2_rd_pa = i_s2_rd_valid ? r_ras_array[i_s2_rd_index] : 'h0;

endmodule // msrh_ras
