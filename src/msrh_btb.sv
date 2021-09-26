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
   btb_search_if.slave search_btb_if
   );

btb_entry_t update_entry;
btb_entry_t search_entry;

assign update_entry.valid        = update_btb_if.valid;
assign update_entry.pc_tag       = update_btb_if.pc_vaddr[riscv_pkg::VADDR_W-1: $clog2(BTB_ENTRY_SIZE)];
assign update_entry.target_vaddr = update_btb_if.target_vaddr;

logic [BTB_ENTRY_SIZE-1: 0] r_btb_valids;
logic                       r_s1_btb_valids;

always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_btb_valids <= {BTB_ENTRY_SIZE{1'b0}};
    r_s1_btb_valids <= 1'b0;
  end else begin
    if (update_btb_if.valid) begin
      r_btb_valids[update_btb_if.pc_vaddr[$clog2(BTB_ENTRY_SIZE): 1]] <= 1'b1;
    end
    r_s1_btb_valids <= r_btb_valids[search_btb_if.s0_pc_vaddr[$clog2(BTB_ENTRY_SIZE): 1]];
  end
end

logic           r_s1_search_valid;
logic [riscv_pkg::VADDR_W-1: $clog2(BTB_ENTRY_SIZE)] r_s1_pc_tag;

data_array_2p
  #(
    .WIDTH ($bits(btb_entry_t)),
    .ADDR_W ($clog2(BTB_ENTRY_SIZE))
    )
btb_array
  (
   .i_clk (i_clk),
   .i_reset_n (i_reset_n),

   .i_wr      (update_btb_if.valid),
   .i_wr_addr (update_btb_if.pc_vaddr[$clog2(BTB_ENTRY_SIZE): 1]),
   .i_wr_data (update_entry),

   .i_rd_addr (search_btb_if.s0_pc_vaddr[$clog2(BTB_ENTRY_SIZE): 1]),
   .o_rd_data (search_entry)
 );

always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_s1_search_valid <= 1'b0;
    r_s1_pc_tag <= 'h0;
  end else begin
    r_s1_search_valid <= search_btb_if.s0_valid;
    r_s1_pc_tag       <= search_btb_if.s0_pc_vaddr[riscv_pkg::VADDR_W-1: $clog2(BTB_ENTRY_SIZE)];
  end
end


assign search_btb_if.s1_hit = r_s1_search_valid &
                              search_entry.valid &
                              r_s1_btb_valids &
                              (search_entry.pc_tag == r_s1_pc_tag);
assign search_btb_if.s1_target_vaddr = search_entry.target_vaddr;

endmodule // msrh_btb
