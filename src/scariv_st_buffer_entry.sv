// ------------------------------------------------------------------------
// NAME : SCARIV Store Buffer Entry
// TYPE : module
// ------------------------------------------------------------------------
// Request Control Entry and State Machine of Store Buffer
// ------------------------------------------------------------------------
//
// ------------------------------------------------------------------------

module scariv_st_buffer_entry
  import scariv_lsu_pkg::*;
(
 input logic  i_clk,
 input logic  i_reset_n,

 input logic  i_load,
 input        st_buffer_entry_t i_entry,
 input logic  i_merge_accept,

 output logic o_l1d_rd_req, // Read Request of L1D
 input logic  i_l1d_rd_accepted,

 output logic o_missu_req, // Refill request to MISSU
 input logic  i_missu_accepted,

 input logic [scariv_conf_pkg::MISSU_ENTRY_SIZE-1: 0] i_missu_search_update_hit,
 input logic [scariv_conf_pkg::MISSU_ENTRY_SIZE-1: 0] i_missu_search_hit,
 input logic [scariv_conf_pkg::MISSU_ENTRY_SIZE-1: 0] i_missu_evict_search_hit,
 input logic [scariv_conf_pkg::MISSU_ENTRY_SIZE-1: 0] i_missu_evict_sent,

 // Forward check interface from LSU Pipeline
 fwd_check_if.slave stbuf_fwd_check_if[scariv_conf_pkg::LSU_INST_NUM],
 output logic [scariv_conf_pkg::LSU_INST_NUM-1: 0] o_fwd_lsu_hit,

 input logic                                           i_l1d_rd_s1_conflict,
 input logic                                           i_l1d_rd_s1_miss,
 input logic [$clog2(scariv_conf_pkg::DCACHE_WAYS)-1: 0] i_l1d_s1_way,
 input logic [scariv_conf_pkg::DCACHE_DATA_W-1:0]        i_l1d_s1_data,

 output logic    o_l1d_wr_req,
 input logic     i_l1d_wr_accepted,
 input logic     i_l1d_wr_s1_resp_hit,
 input logic     i_l1d_wr_s1_resp_conflict,

 input logic           i_snoop_busy,
 input missu_resp_t    i_st_missu_resp,
 input missu_resolve_t i_missu_resolve,

 l1d_wr_if.watch     l1d_mshr_wr_if,

 output logic             o_ready_to_merge,
 input  logic             i_mshr_l1d_wr_merged,
 output st_buffer_entry_t o_entry,
 output st_buffer_state_t o_state,
 output logic             o_entry_finish,
 input logic              i_finish_accepted
 );

st_buffer_entry_t w_entry_next;
st_buffer_entry_t r_entry;

st_buffer_state_t r_state;
st_buffer_state_t w_state_next;

logic         w_l1d_rd_req_next;

logic [scariv_conf_pkg::LSU_INST_NUM-1: 0] w_fwd_lsu_hit;

logic                                      w_missu_resolve_vld;
assign w_missu_resolve_vld = |(~i_missu_resolve.missu_entry_valids & r_entry.missu_index_oh);

always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_entry <= 'h0;
  end else begin
    r_entry <= w_entry_next;
  end
end

always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_state <= ST_BUF_INIT;
  end else begin
    r_state <= w_state_next;
  end
end

logic [$clog2(scariv_conf_pkg::DCACHE_DATA_W)-1: 0] paddr_partial;
assign paddr_partial = {r_entry.paddr[$clog2(scariv_lsu_pkg::DCACHE_DATA_B_W)-1: 0], 3'b000};

always_comb begin
  w_entry_next = r_entry;

  w_state_next = r_state;
  w_l1d_rd_req_next = 1'b0;
  o_entry_finish = 1'b0;

  if (r_entry.valid & i_merge_accept) begin
    for (int b_idx = 0; b_idx < ST_BUF_WIDTH / 8; b_idx++) begin
      w_entry_next.strb[b_idx]        = r_entry.strb[b_idx] | i_entry.strb[b_idx];
      w_entry_next.data[b_idx*8 +: 8] = i_entry.strb[b_idx] ? i_entry.data[b_idx*8 +: 8] : r_entry.data[b_idx*8 +: 8];
    end
  end

  case (r_state)
    ST_BUF_INIT: begin
      if (i_load) begin
        w_state_next = ST_BUF_RD_L1D;
        w_l1d_rd_req_next = 1'b1;
        w_entry_next = i_entry;

        if (i_snoop_busy) begin
          w_state_next = ST_BUF_WAIT_SNOOP;
        end
      end
    end
    ST_BUF_RD_L1D: begin
      if (i_snoop_busy) begin
        w_state_next = ST_BUF_WAIT_SNOOP;
      end else if (i_l1d_rd_accepted) begin
        w_state_next = ST_BUF_RESP_L1D;
      end
    end
    ST_BUF_RESP_L1D: begin
      if (i_snoop_busy) begin
        w_state_next = ST_BUF_WAIT_SNOOP;
      end else if (i_missu_search_update_hit != 'h0) begin
        w_state_next = ST_BUF_RD_L1D;
      end else if (i_missu_search_hit != 'h0) begin
        if (i_missu_resolve.valid &
            (i_missu_resolve.resolve_index_oh == i_missu_search_hit)) begin
          // MISSU hit and resolve immediately : replay again
          w_state_next = ST_BUF_RD_L1D;
        end else begin
          w_state_next = ST_BUF_WAIT_REFILL; // Replay
          w_entry_next.missu_index_oh = i_missu_search_hit;
        end
      end else if (i_missu_evict_search_hit != 0) begin
        if (|(i_missu_evict_search_hit & i_missu_evict_sent)) begin
          // Already evicted
          w_state_next = ST_BUF_MISSU_REFILL;
        end else begin
          w_state_next = ST_BUF_WAIT_REFILL; // Todo: Should be merge
          w_entry_next.missu_index_oh = i_missu_search_hit;
        end
      end else if (i_l1d_rd_s1_conflict) begin
        w_entry_next.l1d_high_priority = 1'b1;
        w_state_next = ST_BUF_RD_L1D;
      end else if (i_l1d_rd_s1_miss) begin
        w_state_next = ST_BUF_MISSU_REFILL;
        w_entry_next.l1d_way = i_l1d_s1_way;
      end else begin
        w_entry_next.l1d_way = i_l1d_s1_way;
        w_state_next = ST_BUF_L1D_UPDATE;
      end
    end
    ST_BUF_L1D_UPDATE: begin
      if (i_l1d_wr_accepted) begin
        w_state_next = ST_BUF_L1D_UPD_RESP;
      end
    end
    ST_BUF_L1D_UPD_RESP : begin
      if (i_l1d_wr_s1_resp_conflict) begin
        w_state_next = ST_BUF_L1D_UPDATE;
      end else if (!i_l1d_wr_s1_resp_hit) begin
        w_state_next = ST_BUF_RD_L1D;
      end else begin
        w_state_next = ST_BUF_WAIT_FINISH;
      end
    end
    ST_BUF_MISSU_REFILL: begin
      if (i_missu_accepted) begin
        if (i_st_missu_resp.evict_conflict) begin
          w_state_next = ST_BUF_WAIT_EVICT;
          w_entry_next.missu_index_oh = i_st_missu_resp.missu_index_oh;
        end else if (i_st_missu_resp.missu_index_oh != 'h0) begin
          w_state_next = ST_BUF_WAIT_REFILL; // Replay
          w_entry_next.missu_index_oh = i_st_missu_resp.missu_index_oh;
        end else if (i_st_missu_resp.full) begin
          w_state_next = ST_BUF_WAIT_FULL;
        end else begin
          // if index_oh is zero, it means MISSU is correctly allocated,
          // so move to STQ_COMMIT and rerun, and set index_oh conflict bit set again.
          w_state_next = ST_BUF_RD_L1D; // Replay
        end
      end
    end // case: ST_BUF_MISSU_REFILL
    ST_BUF_WAIT_EVICT : begin
      if (w_missu_resolve_vld) begin
        w_state_next = ST_BUF_RD_L1D; // Replay
      end
    end
    ST_BUF_WAIT_REFILL: begin
      if (i_mshr_l1d_wr_merged) begin
        w_state_next = ST_BUF_L1D_MERGE;
      end else if (w_missu_resolve_vld) begin
        w_state_next = ST_BUF_RD_L1D;
      end
    end
    ST_BUF_WAIT_SNOOP : begin
      if (!i_snoop_busy) begin
        w_state_next = ST_BUF_RD_L1D;
      end
    end
    ST_BUF_WAIT_FULL: begin
      if (!i_st_missu_resp.full) begin
        w_state_next = ST_BUF_RD_L1D; // Replay
      end
    end
    ST_BUF_L1D_MERGE : begin
      // ST_BUF_L1D_MERGE and ST_BUF_L1D_MERGE2 are needed to
      // Keep lifetime for fowarding during L1D update
      if (!i_snoop_busy) begin
        w_state_next = ST_BUF_RD_L1D;
      end else if (!l1d_mshr_wr_if.s1_wr_resp.s1_conflict) begin
        w_state_next = ST_BUF_L1D_MERGE2;
      end
    end
    ST_BUF_L1D_MERGE2 : begin
      if (!i_snoop_busy) begin
        w_state_next = ST_BUF_RD_L1D;
      end else begin
        w_state_next = ST_BUF_WAIT_FINISH;
      end
    end
    ST_BUF_WAIT_FINISH : begin
      o_entry_finish = 1'b1;
      if (i_finish_accepted) begin
        w_state_next = ST_BUF_INIT;
        w_entry_next.valid = 1'b0;
      end
    end
    default : begin
    end
  endcase // case (r_state)
end // always_comb

assign o_entry = r_entry;
assign o_state = r_state;
assign o_ready_to_merge = r_entry.valid &
                          (r_state != ST_BUF_L1D_UPDATE) &
                          (r_state != ST_BUF_L1D_UPD_RESP) &
                          (r_state != ST_BUF_L1D_MERGE) &
                          (r_state != ST_BUF_L1D_MERGE2) &
                          (r_state != ST_BUF_WAIT_FINISH);
assign o_l1d_rd_req = r_entry.valid & (r_state == ST_BUF_RD_L1D);
assign o_missu_req    = r_entry.valid & (r_state == ST_BUF_MISSU_REFILL);
assign o_l1d_wr_req = r_entry.valid & (r_state == ST_BUF_L1D_UPDATE);

// -----------------------------------
// Forwarding check from LSU Pipeline
// -----------------------------------
generate for (genvar p_idx = 0; p_idx < scariv_conf_pkg::LSU_INST_NUM; p_idx++) begin : lsu_fwd_loop
  assign o_fwd_lsu_hit[p_idx] = r_entry.valid & stbuf_fwd_check_if[p_idx].valid &
                                (r_entry.paddr                  [riscv_pkg::PADDR_W-1:$clog2(ST_BUF_WIDTH/8)] ==
                                 stbuf_fwd_check_if[p_idx].paddr[riscv_pkg::PADDR_W-1:$clog2(ST_BUF_WIDTH/8)]);
end
endgenerate


`ifdef SIMULATION
final begin
  if (r_state != ST_BUF_INIT) begin
    $display("%m\nCaution: ST-Buffer doesn't go back to Initial state");
  end
end
`endif // SIMULATION

endmodule // scariv_st_buffer_entry
