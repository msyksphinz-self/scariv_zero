// ------------------------------------------------------------------------
// NAME : scariv_l1d_mshr_entry
// TYPE : module
// ------------------------------------------------------------------------
// SCARIV MSHR Entry
// ------------------------------------------------------------------------
// ------------------------------------------------------------------------

module scariv_l1d_mshr_entry
  (
   input logic i_clk,
   input logic i_reset_n,

   input logic i_load,
   input scariv_lsu_pkg::mshr_entry_t i_load_entry,

   input logic                   i_ext_load_fin,
   input scariv_lsu_pkg::l2_resp_t l2_resp,  // Response from L2

   input logic i_sent,
   input logic i_evict_sent,

   output logic o_ext_req_ready,

   output logic o_wr_req_valid,
   input logic i_wr_accepted,
   input logic i_wr_conflicted,
   input scariv_lsu_pkg::s2_l1d_wr_resp_t s2_l1d_wr_resp_payload,

   // Store Requestor Monitor
   st_req_info_if.monitor st_req_info_if,

   // UC forward hit
   input logic i_uc_fwd_hit,

   input logic i_busy_by_snoop,

   output scariv_lsu_pkg::mshr_entry_t o_entry,
   output logic o_evict_ready,

   input  logic i_out_ptr_valid,
   output logic o_entry_finish
   );

typedef enum logic [3:0] {
  INIT             = 0,
  READY_REQ        = 1,
  WAIT_RESP        = 2,
  WRITE_L1D        = 3,
  WRITE_L1D_TEMP   = 4,
  WRITE_L1D_TEMP2  = 5,
  EVICT_REQ        = 6,
  WAIT_FINISH      = 7,
  WAIT_GET_UC_DATA = 8
} state_t;


scariv_lsu_pkg::mshr_entry_t r_entry;
scariv_lsu_pkg::mshr_entry_t w_entry_next;

state_t r_state;
state_t w_state_next;

logic [ 1: 0] r_count_fin;
logic [ 1: 0] w_count_fin_next;

logic         w_hit_st_requestor_busy;
assign w_hit_st_requestor_busy = r_entry.valid &
                                 st_req_info_if.busy &
                                 (r_entry.paddr[$clog2(scariv_conf_pkg::DCACHE_DATA_W)-1: 0] ==
                                  st_req_info_if.paddr[$clog2(scariv_conf_pkg::DCACHE_DATA_W)-1: 0]);

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
      if (!w_hit_st_requestor_busy & i_sent) begin
        w_entry_next.sent = 1'b1;
        w_state_next = WAIT_RESP;
      end
    end
    WAIT_RESP : begin
      if (i_ext_load_fin) begin
        w_entry_next.data = l2_resp.data;
        w_entry_next.get_data = 1'b1;
        w_count_fin_next = 'h0;
        if (!r_entry.is_uc) begin
          if (!i_busy_by_snoop) begin
            w_state_next = WRITE_L1D;
          end
        end else begin
          w_state_next = WAIT_GET_UC_DATA;
        end
      end else if (r_entry.get_data & !i_busy_by_snoop) begin // if (i_ext_load_fin)
        w_state_next = WRITE_L1D;
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
      end else begin
        w_state_next = WRITE_L1D_TEMP2;
      end
    end
    WRITE_L1D_TEMP2 : begin
      // Prevent forwarding after this stage
      w_entry_next.get_data = 1'b0;
      if (s2_l1d_wr_resp_payload.s2_evicted_valid) begin
        w_state_next = EVICT_REQ;
        w_entry_next.paddr = s2_l1d_wr_resp_payload.s2_evicted_paddr;
        w_entry_next.data  = s2_l1d_wr_resp_payload.s2_evicted_data;
      end else begin
        w_state_next = WAIT_FINISH;
      end
      // end
    end
    EVICT_REQ : begin
      if (i_evict_sent) begin
        w_state_next = WAIT_FINISH;
      end
    end
    WAIT_GET_UC_DATA : begin
      if (i_uc_fwd_hit) begin
        w_state_next = WAIT_FINISH;
      end
    end
    WAIT_FINISH : begin
      if ((r_count_fin == 'h1) && i_out_ptr_valid) begin
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

assign o_ext_req_ready = (r_state == READY_REQ) & !w_hit_st_requestor_busy;
assign o_wr_req_valid = r_state == WRITE_L1D;
assign o_evict_ready  = r_state == EVICT_REQ;


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

endmodule // scariv_miss_entry
