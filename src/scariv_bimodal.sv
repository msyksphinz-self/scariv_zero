// ------------------------------------------------------------------------
// NAME : scariv_bim
// TYPE : module
// ------------------------------------------------------------------------
// Branch Predictor, Bimodal
// ------------------------------------------------------------------------
//
// ------------------------------------------------------------------------

module scariv_bim
  import scariv_predict_pkg::*;
(
 input logic  i_clk,
 input logic  i_reset_n,

 bim_update_if.slave update_bim_if,
 bim_search_if.slave search_bim_if,
 input logic [scariv_lsu_pkg::ICACHE_DATA_B_W/2-1: 0] i_f1_btb_hit_oh
 );

logic [ 1: 0] w_update_counter;
logic [ 1: 0] w_f1_counter[scariv_lsu_pkg::ICACHE_DATA_B_W/2];

logic [riscv_pkg::VADDR_W-1: 1]              w_update_pc_vaddr;
assign w_update_pc_vaddr = update_bim_if.pc_vaddr[riscv_pkg::VADDR_W-1:1] + (update_bim_if.is_rvc ? 'h0 : 'h1);

generate for (genvar b_idx = 0; b_idx < scariv_lsu_pkg::ICACHE_DATA_B_W/2; b_idx++) begin : btb_loop

  logic bim_update_hit;
  assign bim_update_hit = update_bim_if.valid & (w_update_pc_vaddr[BTB_ENTRY_FIELD_MSB:1] == b_idx);

  logic [scariv_conf_pkg::BTB_ENTRY_SIZE-1: 0] r_bim_valids;
  logic                       r_f1_bim_valids;
  logic [ 1: 0]               w_f1_counter_tmp;

  data_array_2p
    #(
      .WIDTH (2),
      .ADDR_W ($clog2(scariv_conf_pkg::BTB_ENTRY_SIZE))
      )
  bim_array
    (
     .i_clk (i_clk),
     .i_reset_n (i_reset_n),

     .i_wr   (bim_update_hit),
     .i_wr_addr (w_update_pc_vaddr[BTB_ENTRY_BIT_MSB:BTB_ENTRY_BIT_LSB]),
     .i_wr_data (w_update_counter),

     .i_rd_addr (search_bim_if.f0_pc_vaddr[BTB_ENTRY_BIT_MSB:BTB_ENTRY_BIT_LSB]),
     .o_rd_data (w_f1_counter_tmp)
     );

  always_ff @ (posedge i_clk, negedge i_reset_n) begin
    if (!i_reset_n) begin
      r_bim_valids <= {scariv_conf_pkg::BTB_ENTRY_SIZE{1'b0}};
      r_f1_bim_valids <= 1'b0;
    end else begin
      if (bim_update_hit) begin
        r_bim_valids[w_update_pc_vaddr[BTB_ENTRY_BIT_MSB:BTB_ENTRY_BIT_LSB]] <= 1'b1;
      end
      r_f1_bim_valids <= r_bim_valids[search_bim_if.f0_pc_vaddr[BTB_ENTRY_BIT_MSB:BTB_ENTRY_BIT_LSB]];
    end
  end

  assign search_bim_if.f1_bim_value [b_idx] = w_f1_counter[b_idx];
  assign search_bim_if.f1_pred_taken[b_idx] = w_f1_counter[b_idx][1];

  assign w_f1_counter[b_idx] = r_f1_bim_valids ? w_f1_counter_tmp : 2'b01;  // by default, weakly untaken

  always_ff @ (posedge i_clk, negedge i_reset_n) begin
    if (!i_reset_n) begin
      search_bim_if.f2_bim_value [b_idx] <= 'h0;
      search_bim_if.f2_pred_taken[b_idx] <= 1'b0;
    end else begin
      search_bim_if.f2_bim_value [b_idx] <= search_bim_if.f1_bim_value [b_idx];
      search_bim_if.f2_pred_taken[b_idx] <= search_bim_if.f1_pred_taken[b_idx];
    end
  end

end // block: btb_loop
endgenerate

assign w_update_counter =  (&update_bim_if.bim_value & update_bim_if.hit |
                            ~|update_bim_if.bim_value & update_bim_if.hit) ? update_bim_if.bim_value :
                           update_bim_if.taken ? update_bim_if.bim_value + 2'b01 :
                           update_bim_if.bim_value - 2'b01;

endmodule // scariv_bim
