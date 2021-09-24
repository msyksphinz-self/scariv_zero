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

assign update_entry.valid       = update_btb_if.valid;
assign update_entry.pc_tag      = update_btb_if.pc_vaddr[riscv_pkg::VADDR_W-1: $clog2(BTB_ENTRY_SIZE)];
assign update_entry.target_addr = update_btb_if.target_vaddr;

logic           r_s1_search_valid;
logic [riscv_pkg::VADDR_W-1: $clog2(BTB_ENTRY_SIZE)] r_s1_pc_tag;

localparam SRAM_WIDTH = $bits(btb_entry_t) * 8 / 8;

data_array
  #(
    .WIDTH (SRAM_WIDTH),
    .ADDR_W (BTB_ENTRY_SIZE)
    )
btb_array
  (
   .i_clk (i_clk),
   .i_reset_n (i_reset_n),

   .i_wr   (update_btb_if.valid),
   .i_addr (update_btb_if.pc_vaddr[$clog2(BTB_ENTRY_SIZE)-1: 2]),
   .o_data (search_entry),
   .i_be   ({(SRAM_WIDTH/8){1'b1}}),
   .i_data (update_entry)
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
                              (search_entry.pc_tag == r_s1_pc_tag);
assign search_btb_if.s1_target_addr = search_entry.target_vaddr;

endmodule // msrh_btb
