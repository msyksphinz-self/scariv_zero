// ------------------------------------------------------------------------
// NAME : MSRH Branch Target Buffer(BTB)
// TYPE : module
// ------------------------------------------------------------------------
// Branch Target Buffer, mainly composed with SRAM
// ------------------------------------------------------------------------
//
// ------------------------------------------------------------------------

module msrh_btb
  import msrh_predict_pkg::*;
(
   input logic  i_clk,
   input logic  i_reset_n,

   btb_update_if.slave update_btb_if,
   btb_search_if.slave search_btb_if,

   output logic [msrh_lsu_pkg::ICACHE_DATA_B_W/2-1: 0] o_s1_btb_hit_oh
 );

logic           r_s1_search_valid;
logic [riscv_pkg::VADDR_W-1: BTB_ENTRY_BIT_MSB+1] r_s1_pc_tag;

logic [msrh_lsu_pkg::ICACHE_DATA_B_W/2-1: 0] search_btb_s1_hit;
logic [msrh_lsu_pkg::ICACHE_DATA_B_W/2-1: 0] r_s1_btb_bank_mask;

generate for (genvar b_idx = 0; b_idx < msrh_lsu_pkg::ICACHE_DATA_B_W/2; b_idx++) begin : btb_loop
  btb_entry_t update_entry;
  btb_entry_t search_entry;

  logic btb_update_hit;
  assign btb_update_hit = update_btb_if.valid & (update_btb_if.pc_vaddr[BTB_ENTRY_FIELD_MSB:1] == b_idx);

  assign update_entry.valid        = btb_update_hit;
  assign update_entry.pc_tag       = update_btb_if.pc_vaddr[riscv_pkg::VADDR_W-1:BTB_ENTRY_BIT_MSB+1];
  assign update_entry.target_vaddr = update_btb_if.target_vaddr;

  data_array_2p
    #(
      .WIDTH ($bits(btb_entry_t)),
      .ADDR_W ($clog2(BTB_ENTRY_SIZE))
      )
  btb_array
    (
     .i_clk (i_clk),
     .i_reset_n (i_reset_n),

     .i_wr      (btb_update_hit),
     .i_wr_addr (update_btb_if.pc_vaddr[BTB_ENTRY_BIT_MSB:BTB_ENTRY_BIT_LSB]),
     .i_wr_data (update_entry),

     .i_rd_addr (search_btb_if.s0_pc_vaddr[BTB_ENTRY_BIT_MSB:BTB_ENTRY_BIT_LSB]),
     .o_rd_data (search_entry)
   );

  logic   r_s1_btb_valid;
  logic [BTB_ENTRY_SIZE-1: 0] r_btb_valids;

  assign search_btb_s1_hit[b_idx] = r_s1_search_valid &
                                    search_entry.valid &
                                    r_s1_btb_valid &
                                    (search_entry.pc_tag == r_s1_pc_tag);


  always_ff @ (posedge i_clk, negedge i_reset_n) begin
    if (!i_reset_n) begin
      r_btb_valids <= {BTB_ENTRY_SIZE{1'b0}};
      r_s1_btb_valid <= 1'b0;
    end else begin
      if (btb_update_hit) begin
        r_btb_valids[update_btb_if.pc_vaddr[BTB_ENTRY_BIT_MSB:BTB_ENTRY_BIT_LSB]] <= 1'b1;
      end
      r_s1_btb_valid <= r_btb_valids[search_btb_if.s0_pc_vaddr[BTB_ENTRY_BIT_MSB:BTB_ENTRY_BIT_LSB]];
    end
  end

  always_ff @ (posedge i_clk, negedge i_reset_n) begin
    if (!i_reset_n) begin
      search_btb_if.s2_target_vaddr[b_idx] <= 1'b0;
      search_btb_if.s2_valid       [b_idx] <= 'h0;
    end else begin
      search_btb_if.s2_target_vaddr[b_idx] <= search_btb_s1_hit ? search_entry.target_vaddr : 'h0;
      search_btb_if.s2_valid       [b_idx] <= search_btb_s1_hit[b_idx] & r_s1_btb_bank_mask[b_idx];
    end
  end
end
endgenerate

always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_s1_search_valid <= 1'b0;
    r_s1_pc_tag <= 'h0;
    r_s1_btb_bank_mask <= 'h0;
  end else begin
    r_s1_search_valid <= search_btb_if.s0_valid;
    r_s1_pc_tag <= search_btb_if.s0_pc_vaddr[riscv_pkg::VADDR_W-1: BTB_ENTRY_BIT_MSB+1];
    r_s1_btb_bank_mask <= ~((1 << search_btb_if.s0_pc_vaddr[BTB_ENTRY_FIELD_MSB:1]) - 1);
  end
end


endmodule // msrh_btb
