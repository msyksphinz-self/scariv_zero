module msrh_lrq_entry
  (
   input logic i_clk,
   input logic i_reset_n,

   input logic i_load,
   input       msrh_lsu_pkg::lrq_entry_t i_load_entry,

   input logic i_ext_load_fin,

   input       msrh_lsu_pkg::evict_merge_t i_evict_merge,

   input logic i_sent,
   input logic i_evict_sent,

   output      msrh_lsu_pkg::lrq_entry_t o_entry,
   output logic o_evict_ready,
   output logic o_entry_clear
   );

typedef enum logic [1:0] {
  INIT = 0,
  READY_REQ = 1,
  WAIT_RESP = 2 /*,
  READY_EVICT = 3 */
} state_t;


msrh_lsu_pkg::lrq_entry_t r_entry;
msrh_lsu_pkg::lrq_entry_t w_entry_next;

state_t r_state;
state_t w_state_next;


always_comb begin
  w_entry_next = r_entry;
  w_state_next = r_state;
  o_entry_clear = 1'b0;

  case (r_state)
    INIT : begin
      if (i_load) begin
        w_entry_next = i_load_entry;
        w_state_next = READY_REQ;
      end
    end
    READY_REQ : begin
      if (i_sent) begin
        w_entry_next.sent = 1'b1;
        w_state_next = WAIT_RESP;
      end
    end
    WAIT_RESP : begin
      if (i_ext_load_fin) begin
        // if (r_entry.evict_valid) begin
        //   w_state_next = READY_EVICT;
        // end else begin
        w_state_next = INIT;
        w_entry_next = 'h0;
        o_entry_clear = 1'b1;
        // end
      end
    end
    // READY_EVICT : begin
    //   if (i_evict_sent) begin
    //     w_state_next = INIT;
    //     w_entry_next = 'h0;
    //     o_entry_clear = 1'b1;
    //   end
    // end
    default : begin end
  endcase // case (r_state)

  if (o_evict_ready & i_evict_sent) begin
    w_entry_next.evict_sent = 1'b1;
  end

  // if (i_evict_merge.valid) begin
  //   for (int b = 0; b < msrh_lsu_pkg::DCACHE_DATA_B_W; b++) begin : evict_byte_loop
  //     if (i_evict_merge.be[b]) begin
  //       w_entry_next.evict.data[b*8 +: 8] = i_evict_merge.data[(b * 8) % riscv_pkg::XLEN_W +: 8];
  //     end
  //   end
  // end

end // always_comb

assign o_evict_ready = r_entry.valid & r_entry.evict_valid & ~r_entry.evict_sent;


always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_entry <= 'h0;
    r_state <= INIT;
  end else begin
    r_entry <= w_entry_next;
    r_state <= w_state_next;
`ifdef SIMULATION
    if (r_entry.valid & i_load) begin
      $fatal(0, "During LRQ entry valid, i_load must not be come\n");
    end
`endif // SIMULATION
  end
end

assign o_entry = r_entry;

endmodule // msrh_lrq_entry
