module msrh_lrq_entry
  (
   input logic i_clk,
   input logic i_reset_n,

   input logic i_load,
   input       msrh_lsu_pkg::lrq_entry_t i_load_entry,

   input logic i_resp,
   input logic i_sent,
   input logic i_clear,

   output logic o_evict_ready,
   input logic [msrh_conf_pkg::DCACHE_DATA_W-1: 0] i_evict_data,
   input logic i_evict_sent,

   output logic o_clear_ready,
   output      msrh_lsu_pkg::lrq_entry_t o_entry
   );

msrh_lsu_pkg::lrq_entry_t r_entry;
msrh_lsu_pkg::lrq_entry_t w_entry_next;

typedef enum logic [2:0] {
  IDLE = 0,
  SENT_READY = 1,
  RESP_WAIT = 2,
  EVICT = 3,
  READY_CLEAR = 4
} lrq_state_t;


lrq_state_t r_state, w_state_next;

always_comb begin
  w_entry_next = r_entry;
  w_state_next = r_state;

  case (r_state)
    IDLE : begin
      if (i_load) begin
        w_entry_next = i_load_entry;
        w_state_next = SENT_READY;
      end
    end
    SENT_READY : begin
      if (i_sent) begin
        w_entry_next.sent = 1'b1;
        w_state_next = RESP_WAIT;
      end
    end
    RESP_WAIT : begin
      if (i_resp) begin
        if (r_entry.evict_valid) begin
          w_state_next = EVICT;
          w_entry_next.evict_ready = 1'b1;
          w_entry_next.evict.data = i_evict_data;
        end else begin
          w_state_next = READY_CLEAR;
        end
      end
    end
    EVICT : begin
      if (i_evict_sent) begin
        w_state_next = READY_CLEAR;
        w_entry_next.evict_ready = 1'b0;
        w_entry_next.evict_sent  = 1'b1;
      end
    end
    READY_CLEAR : begin
      if (i_clear) begin
        w_state_next = IDLE;
        w_entry_next.valid = 1'b0;
        w_entry_next.sent  = 1'b0;
        w_entry_next.evict_sent  = 1'b0;
        w_entry_next.evict_ready = 1'b0;
      end
    end
    default : begin
      $fatal(0, "This state must not to come\n");
    end
  endcase // case (r_state)

end // always_comb


assign o_evict_ready = r_entry.evict_ready;
assign o_clear_ready = (r_state == READY_CLEAR);


always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_entry <= 'h0;
    r_state <= IDLE;
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
