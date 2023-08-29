// ------------------------------------------------------------------------
// NAME : scariv_pred_ras
// TYPE : module
// ------------------------------------------------------------------------
// Return Address Stack Predictor
// ------------------------------------------------------------------------
// ------------------------------------------------------------------------

module scariv_pred_ras
  import scariv_predict_pkg::*;
  import scariv_ic_pkg::*;
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

ic_vaddr_h_t r_ras_array[scariv_conf_pkg::RAS_ENTRY_SIZE-1: 0];

always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    for (int i = 0; i < scariv_conf_pkg::RAS_ENTRY_SIZE; i++) begin
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

`ifdef SIMULATION
logic [riscv_pkg::VADDR_W-1: 0]  sim_ras_array_debug[scariv_conf_pkg::RAS_ENTRY_SIZE-1: 0];
generate for (genvar idx = 0; idx < scariv_conf_pkg::RAS_ENTRY_SIZE; idx++) begin
  assign sim_ras_array_debug[idx] = {r_ras_array[idx], 1'b0};
end endgenerate
`endif // SIMULATION

endmodule // scariv_ras
