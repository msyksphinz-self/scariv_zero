// ------------------------------------------------------------------------
// NAME : MSRH Store Buffer Entry
// TYPE : module
// ------------------------------------------------------------------------
// Request Control Entry and State Machine of Store Buffer
// ------------------------------------------------------------------------
//
// ------------------------------------------------------------------------

module msrh_st_buffer_entry
  import msrh_lsu_pkg::*;
(
 input logic  i_clk,
 input logic  i_reset_n,

 input logic  i_load,
 input        st_buffer_entry_t i_entry,
 input logic  i_merge_accept,

 output logic o_l1d_rd_req, // Read Request of L1D
 input logic  i_l1d_rd_accepted,

 output logic o_lrq_req, // Refill request to LRQ
 input logic  i_lrq_accepted,

 input logic [msrh_pkg::LRQ_ENTRY_SIZE-1: 0] i_lrq_search_hit,
 input logic [msrh_pkg::LRQ_ENTRY_SIZE-1: 0] i_lrq_evict_search_hit,
 input logic [msrh_pkg::LRQ_ENTRY_SIZE-1: 0] i_lrq_evict_sent,

 // Forward check interface from LSU Pipeline
 fwd_check_if.slave stbuf_fwd_check_if[msrh_conf_pkg::LSU_INST_NUM],
 output logic [msrh_conf_pkg::LSU_INST_NUM-1: 0] o_fwd_lsu_hit,

 input logic  i_l1d_rd_miss,
 input logic  i_l1d_rd_conflict,

 output logic o_l1d_wr_req,
 input logic  i_l1d_wr_conflict,

 input lrq_resp_t    i_st_lrq_resp,
 input lrq_resolve_t i_lrq_resolve,

 output logic             o_ready_to_merge,
 output logic             o_l1d_merge_req,
 output st_buffer_entry_t o_entry,
 output logic             o_entry_finish,
 input logic              i_finish_accepted
 );

st_buffer_entry_t w_entry_next;
st_buffer_entry_t r_entry;

st_buffer_state_t r_state;
st_buffer_state_t w_state_next;

logic         w_l1d_rd_req_next;

logic [msrh_conf_pkg::LSU_INST_NUM-1: 0] w_fwd_lsu_hit;

logic                                    w_lrq_resolve_vld;
assign w_lrq_resolve_vld = i_lrq_resolve.valid &
                           (i_lrq_resolve.resolve_index_oh == r_entry.lrq_index_oh);

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
      end
    end
    ST_BUF_RD_L1D: begin
      if (i_l1d_rd_accepted) begin
        w_state_next = ST_BUF_RESP_L1D;
      end
    end
    ST_BUF_RESP_L1D: begin
      if (i_lrq_search_hit != 'h0) begin
        if (i_lrq_resolve.valid &
            (i_lrq_resolve.resolve_index_oh == i_lrq_search_hit)) begin
          // LRQ hit and resolve immediately : replay again
          w_state_next = ST_BUF_RD_L1D;
        end else begin
          w_state_next = ST_BUF_WAIT_REFILL; // Replay
          w_entry_next.lrq_index_oh = i_lrq_search_hit;
        end
      end else if (i_lrq_evict_search_hit != 0) begin
        if (|(i_lrq_evict_search_hit & i_lrq_evict_sent)) begin
          // Already evicted
          w_state_next = ST_BUF_LRQ_REFILL;
        end else begin
          w_state_next = ST_BUF_WAIT_REFILL; // Todo: Should be merge
          w_entry_next.lrq_index_oh = i_lrq_search_hit;
        end
      end else if (i_l1d_rd_miss) begin
        w_state_next = ST_BUF_LRQ_REFILL;
      end else if (i_l1d_rd_conflict) begin
        w_state_next = ST_BUF_RD_L1D;
      end else begin
        w_state_next = ST_BUF_L1D_UPDATE;
      end
    end
    ST_BUF_L1D_UPDATE: begin
      if (i_l1d_wr_conflict) begin
        w_state_next = ST_BUF_RD_L1D;
      end else begin
        w_state_next = ST_BUF_WAIT_FINISH;
      end
    end
    ST_BUF_LRQ_REFILL: begin
      if (i_lrq_accepted) begin
        if (i_st_lrq_resp.evict_conflict) begin
          w_state_next = ST_BUF_WAIT_EVICT;
          w_entry_next.lrq_index_oh = i_st_lrq_resp.lrq_index_oh;
        end else if (i_st_lrq_resp.lrq_index_oh != 'h0) begin
          w_state_next = ST_BUF_WAIT_REFILL; // Replay
          w_entry_next.lrq_index_oh = i_st_lrq_resp.lrq_index_oh;
        end else if (i_st_lrq_resp.full) begin
          w_state_next = ST_BUF_WAIT_FULL;
        end else begin
          // if index_oh is zero, it means LRQ is correctly allocated,
          // so move to STQ_COMMIT and rerun, and set index_oh conflict bit set again.
          w_state_next = ST_BUF_RD_L1D; // Replay
        end
      end
    end // case: ST_BUF_LRQ_REFILL
    ST_BUF_WAIT_EVICT : begin
      if (w_lrq_resolve_vld | |(~i_lrq_resolve.lrq_entry_valids & r_entry.lrq_index_oh)) begin
        w_state_next = ST_BUF_RD_L1D; // Replay
      end
    end
    ST_BUF_WAIT_REFILL: begin
      if (w_lrq_resolve_vld) begin
          w_state_next = ST_BUF_L1D_MERGE;
      end else if (~|(i_lrq_resolve.lrq_entry_valids & r_entry.lrq_index_oh)) begin
        // cleared dependent entry
        w_state_next = ST_BUF_RD_L1D;
      end
    end
    ST_BUF_WAIT_FULL: begin
      if (!i_st_lrq_resp.full) begin
        w_state_next = ST_BUF_RD_L1D; // Replay
      end
    end
    ST_BUF_L1D_MERGE : begin
      w_state_next = ST_BUF_WAIT_FINISH;
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
assign o_ready_to_merge = r_entry.valid & (r_state != ST_BUF_L1D_UPDATE) &
                          (r_state != ST_BUF_L1D_MERGE) &
                          (r_state != ST_BUF_WAIT_FINISH);
assign o_l1d_rd_req = r_entry.valid & (r_state == ST_BUF_RD_L1D);
assign o_lrq_req    = r_entry.valid & (r_state == ST_BUF_LRQ_REFILL);
assign o_l1d_wr_req = r_entry.valid & (r_state == ST_BUF_L1D_UPDATE);
assign o_l1d_merge_req = r_entry.valid & (r_state == ST_BUF_L1D_MERGE);

// -----------------------------------
// Forwarding check from LSU Pipeline
// -----------------------------------
generate for (genvar p_idx = 0; p_idx < msrh_conf_pkg::LSU_INST_NUM; p_idx++) begin : lsu_fwd_loop
  assign o_fwd_lsu_hit[p_idx] = r_entry.valid & stbuf_fwd_check_if[p_idx].valid &
                                (r_entry.paddr[riscv_pkg::PADDR_W-1:$clog2(ST_BUF_WIDTH/8)] ==
                                 stbuf_fwd_check_if[p_idx].paddr[riscv_pkg::PADDR_W-1:$clog2(ST_BUF_WIDTH/8)]);
end
endgenerate

endmodule // msrh_st_buffer_entry
