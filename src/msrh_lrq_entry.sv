module msrh_lrq_entry
  (
   input logic i_clk,
   input logic i_reset_n,

   input logic i_load,
   input       msrh_lsu_pkg::lrq_entry_t i_load_entry,

   input logic i_clear,

   input logic i_sent,
   output      msrh_lsu_pkg::lrq_entry_t o_entry
   );

msrh_lsu_pkg::lrq_entry_t r_entry;

always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_entry <= 'h0;
  end else begin
    if (i_clear) begin
      r_entry.valid <= 1'b0;
    end else if (i_load) begin
      r_entry <= i_load_entry;
`ifdef SIMULATION
      if (r_entry.valid & i_load) begin
        $fatal(0, "During LRQ entry valid, i_loud must not be come\n");
      end
`endif // SIMULATION
    end else if (i_sent) begin
      r_entry.sent <= 1'b1;
    end
  end
end

assign o_entry = r_entry;

endmodule // msrh_lrq_entry
