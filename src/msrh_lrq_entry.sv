module msrh_lrq_entry
  (
   input logic i_clk,
   input logic i_reset_n,

   input logic i_load,
   input       msrh_lsu_pkg::lrq_entry_t i_load_entry,

   input logic i_clear,

   input msrh_lsu_pkg::evict_merge_t i_evict_merge,

   input logic i_sent,
   input logic i_evict_sent,

   output      msrh_lsu_pkg::lrq_entry_t o_entry
   );

msrh_lsu_pkg::lrq_entry_t r_entry;
msrh_lsu_pkg::lrq_entry_t w_entry_next;

always_comb begin
  w_entry_next = r_entry;

  if (i_clear) begin
    w_entry_next.valid = 1'b0;
  end else if (i_load) begin
    w_entry_next = i_load_entry;
  end

  if (i_sent) begin
    w_entry_next.sent = 1'b1;
  end
  if (i_evict_sent) begin
    w_entry_next.evict_sent = 1'b1;
  end

  if (i_evict_merge.valid) begin
    for (int b = 0; b < msrh_lsu_pkg::DCACHE_DATA_B_W; b++) begin : evict_byte_loop
      if (i_evict_merge.be[b]) begin
        w_entry_next.evict.data[b +: 8] = i_evict_merge.data[b % riscv_pkg::XLEN_W/8 +: 8];
      end
    end
  end

end // always_comb


always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_entry <= 'h0;
  end else begin
    r_entry <= w_entry_next;
`ifdef SIMULATION
    if (r_entry.valid & i_load) begin
      $fatal(0, "During LRQ entry valid, i_load must not be come\n");
    end
`endif // SIMULATION
  end
end

assign o_entry = r_entry;

endmodule // msrh_lrq_entry
