module msrh_miss_entry
  (
   input logic i_clk,
   input logic i_reset_n,

   input logic i_load,
   input msrh_lsu_pkg::miss_entry_t i_load_entry,

   input logic                   i_ext_load_fin,
   input msrh_lsu_pkg::l2_resp_t l2_resp,  // Response from L2

   input logic i_sent,
   input logic i_evict_sent,

   output logic o_wr_req_valid,
   input logic i_wr_accepted,
   input logic i_wr_conflicted,
   input msrh_lsu_pkg::s2_l1d_wr_resp_t s2_l1d_wr_resp_payload,

   output msrh_lsu_pkg::miss_entry_t o_entry,
   output logic o_evict_ready,
   output logic o_entry_finish
   );

typedef enum logic [2:0] {
  INIT            = 0,
  READY_REQ       = 1,
  WAIT_RESP       = 2,
  WRITE_L1D       = 3,
  WRITE_L1D_TEMP  = 4,
  WRITE_L1D_TEMP2 = 5,
  EVICT_REQ       = 6,
  WAIT_FINISH     = 7
} state_t;


msrh_lsu_pkg::miss_entry_t r_entry;
msrh_lsu_pkg::miss_entry_t w_entry_next;

state_t r_state;
state_t w_state_next;

logic [ 1: 0] r_count_fin;
logic [ 1: 0] w_count_fin_next;

always_comb begin
  w_entry_next = r_entry;
  w_state_next = r_state;

  w_count_fin_next = r_count_fin;
  o_entry_finish = 'b0;

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
        w_entry_next.data = l2_resp.data;
        w_state_next = WRITE_L1D;
        w_count_fin_next = 'h0;
      end
    end
    WRITE_L1D : begin
      if (i_wr_accepted) begin
        w_state_next = WRITE_L1D_TEMP;
      end
    end
    WRITE_L1D_TEMP : begin
      if (i_wr_conflicted) begin
        w_state_next = WRITE_L1D;
      end
    end
    WRITE_L1D_TEMP2 : begin
      // if (s2_l1d_wr_resp_payload.s2_done) begin
      if (s2_l1d_wr_resp_payload.s2_evicted_valid) begin
        w_state_next = EVICT_REQ;
      end else begin
        w_state_next = WAIT_FINISH;
      end
      // end
    end
    EVICT_REQ : begin
    end
    WAIT_FINISH : begin
      if (r_count_fin == 'h1) begin
        w_state_next = INIT;
        w_entry_next = 'h0;
        o_entry_finish = 'b1;
      end else begin
        w_count_fin_next = r_count_fin + 'h1;
      end
    end
    default : begin end
  endcase // case (r_state)

  // if (o_evict_ready & i_evict_sent) begin
  //   w_entry_next.evict_sent = 1'b1;
  // end

end // always_comb

assign o_wr_req_valid = r_state == WRITE_L1D;
assign o_evict_ready = r_entry.valid & r_entry.evict_valid & ~r_entry.evict_sent;


always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_entry <= 'h0;
    r_state <= INIT;

    r_count_fin <= 'h0;
  end else begin
    r_entry <= w_entry_next;
    r_state <= w_state_next;

    r_count_fin <= w_count_fin_next;
`ifdef SIMULATION
    if (r_entry.valid & i_load) begin
      $fatal(0, "During LRQ entry valid, i_load must not be come\n");
    end
`endif // SIMULATION
  end
end

assign o_entry = r_entry;

endmodule // msrh_miss_entry
