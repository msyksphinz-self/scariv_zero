// ------------------------------------------------------------------------
// NAME : scariv_btb
// TYPE : module
// ------------------------------------------------------------------------
// Branch Target Buffer, mainly composed with SRAM
// ------------------------------------------------------------------------
//
// ------------------------------------------------------------------------

module scariv_btb
  import scariv_predict_pkg::*;
(
   input logic  i_clk,
   input logic  i_reset_n,

   btb_update_if.slave update_btb_if,
   btb_search_if.slave search_btb_if
 );

logic           r_f1_search_valid;
logic [riscv_pkg::VADDR_W-1: BTB_ENTRY_BIT_MSB+1] r_f1_pc_tag;

logic [scariv_lsu_pkg::ICACHE_DATA_B_W/2-1: 0] search_btb_f1_hit;
logic [scariv_lsu_pkg::ICACHE_DATA_B_W/2-1: 0] r_f1_btb_bank_mask;

logic [riscv_pkg::VADDR_W-1: 1]              w_update_pc_vaddr;
// Memo: Why update PC_VADDR + 2 ?
//       Because when Branch instruction cross cacheline,
//       needs to fetch both lower line and upper line. So BTB needs to upper-side of cache line.
assign w_update_pc_vaddr = update_btb_if.pc_vaddr[riscv_pkg::VADDR_W-1:1] + (update_btb_if.is_rvc ? 'h0 : 'h1);

generate for (genvar b_idx = 0; b_idx < scariv_lsu_pkg::ICACHE_DATA_B_W/2; b_idx++) begin : btb_loop
  btb_target_va_t update_entry;
  btb_target_va_t w_f1_search_entry;

  logic va_target_wr_valid;
  assign va_target_wr_valid = update_btb_if.valid &
                              /* update_btb_if.taken & */
                              /*(update_btb_if.mispredict | update_btb_if.is_call | update_btb_if.is_ret) & */
                              (w_update_pc_vaddr[BTB_ENTRY_FIELD_MSB:1] == b_idx);

  assign update_entry.target_vaddr = update_btb_if.target_vaddr;

  logic   info_update_valid;
  assign info_update_valid = update_btb_if.valid &
                             (w_update_pc_vaddr[BTB_ENTRY_FIELD_MSB:1] == b_idx);
  btb_inst_info_t update_info_entry;
  btb_inst_info_t w_f1_info_entry;
  assign update_info_entry.valid       = info_update_valid;
  assign update_info_entry.is_cond     = update_btb_if.is_cond;
  assign update_info_entry.is_call     = update_btb_if.is_call;
  assign update_info_entry.is_ret      = update_btb_if.is_ret;
  assign update_info_entry.is_noncond  = !update_btb_if.is_cond & !update_btb_if.is_call & !update_btb_if.is_ret;
  assign update_info_entry.pc_tag      = w_update_pc_vaddr[riscv_pkg::VADDR_W-1:BTB_ENTRY_BIT_MSB+1];

  data_array_2p
    #(
      .WIDTH ($bits(btb_inst_info_t)),
      .ADDR_W ($clog2(scariv_conf_pkg::BTB_ENTRY_SIZE))
      )
  btb_info_array
    (
     .i_clk (i_clk),
     .i_reset_n (i_reset_n),

     .i_wr      (info_update_valid),
     .i_wr_addr (w_update_pc_vaddr[BTB_ENTRY_BIT_MSB:BTB_ENTRY_BIT_LSB]),
     .i_wr_data (update_info_entry),

     .i_rd_addr (search_btb_if.f0_pc_vaddr[BTB_ENTRY_BIT_MSB:BTB_ENTRY_BIT_LSB]),
     .o_rd_data (w_f1_info_entry)
   );

  data_array_2p
    #(
      .WIDTH ($bits(btb_target_va_t)),
      .ADDR_W ($clog2(scariv_conf_pkg::BTB_ENTRY_SIZE))
      )
  btb_target_va_array
    (
     .i_clk (i_clk),
     .i_reset_n (i_reset_n),

     .i_wr      (va_target_wr_valid),
     .i_wr_addr (w_update_pc_vaddr[BTB_ENTRY_BIT_MSB:BTB_ENTRY_BIT_LSB]),
     .i_wr_data (update_entry),

     .i_rd_addr (search_btb_if.f0_pc_vaddr[BTB_ENTRY_BIT_MSB:BTB_ENTRY_BIT_LSB]),
     .o_rd_data (w_f1_search_entry)
   );

  logic   r_f1_btb_valid;
  logic [scariv_conf_pkg::BTB_ENTRY_SIZE-1: 0] r_btb_valids;

  assign search_btb_f1_hit[b_idx] = r_f1_search_valid &
                                    w_f1_info_entry.valid &
                                    r_f1_btb_valid &
                                    (w_f1_info_entry.pc_tag == r_f1_pc_tag);


  always_ff @ (posedge i_clk, negedge i_reset_n) begin
    if (!i_reset_n) begin
      r_btb_valids <= {scariv_conf_pkg::BTB_ENTRY_SIZE{1'b0}};
      r_f1_btb_valid <= 1'b0;
    end else begin
      if (info_update_valid) begin
        r_btb_valids[w_update_pc_vaddr[BTB_ENTRY_BIT_MSB:BTB_ENTRY_BIT_LSB]] <= 1'b1;
      end
      r_f1_btb_valid <= r_btb_valids[search_btb_if.f0_pc_vaddr[BTB_ENTRY_BIT_MSB:BTB_ENTRY_BIT_LSB]];
    end
  end

  assign search_btb_if.f1_target_vaddr[b_idx] = w_f1_search_entry.target_vaddr;
  assign search_btb_if.f1_hit         [b_idx] = r_f1_btb_valid & search_btb_f1_hit[b_idx] & r_f1_btb_bank_mask[b_idx];
  assign search_btb_if.f1_is_cond     [b_idx] = r_f1_btb_valid & w_f1_info_entry.is_cond;
  assign search_btb_if.f1_is_call     [b_idx] = r_f1_btb_valid & w_f1_info_entry.is_call;
  assign search_btb_if.f1_is_ret      [b_idx] = r_f1_btb_valid & w_f1_info_entry.is_ret;
  assign search_btb_if.f1_is_noncond  [b_idx] = r_f1_btb_valid & w_f1_info_entry.is_noncond;

  always_ff @ (posedge i_clk, negedge i_reset_n) begin
    if (!i_reset_n) begin
      search_btb_if.f2_target_vaddr[b_idx] <= 'h0;
      search_btb_if.f2_hit         [b_idx] <= 1'b0;
      search_btb_if.f2_is_cond     [b_idx] <= 1'b0;
      search_btb_if.f2_is_call     [b_idx] <= 1'b0;
      search_btb_if.f2_is_ret      [b_idx] <= 1'b0;
      search_btb_if.f2_is_noncond  [b_idx] <= 1'b0;
    end else begin
      search_btb_if.f2_target_vaddr[b_idx] <= search_btb_if.f1_target_vaddr[b_idx];
      search_btb_if.f2_hit         [b_idx] <= search_btb_if.f1_hit         [b_idx];
      search_btb_if.f2_is_cond     [b_idx] <= search_btb_if.f1_is_cond     [b_idx];
      search_btb_if.f2_is_call     [b_idx] <= search_btb_if.f1_is_call     [b_idx];
      search_btb_if.f2_is_ret      [b_idx] <= search_btb_if.f1_is_ret      [b_idx];
      search_btb_if.f2_is_noncond  [b_idx] <= search_btb_if.f1_is_noncond  [b_idx];
    end // else: !if(!i_reset_n)
  end // always_ff @ (posedge i_clk, negedge i_reset_n)

end
endgenerate

always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_f1_search_valid <= 1'b0;
    r_f1_pc_tag <= 'h0;
    r_f1_btb_bank_mask <= 'h0;
  end else begin
    r_f1_search_valid <= search_btb_if.f0_valid;
    r_f1_pc_tag <= search_btb_if.f0_pc_vaddr[riscv_pkg::VADDR_W-1: BTB_ENTRY_BIT_MSB+1];
    r_f1_btb_bank_mask <= ~((1 << search_btb_if.f0_pc_vaddr[BTB_ENTRY_FIELD_MSB:1]) - 1);
  end
end


endmodule // scariv_btb
