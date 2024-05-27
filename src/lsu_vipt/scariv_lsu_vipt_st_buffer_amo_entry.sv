// ------------------------------------------------------------------------
// NAME : SCARIV Store Buffer Entry
// TYPE : module
// ------------------------------------------------------------------------
// Request Control Entry and State Machine of Store Buffer
// ------------------------------------------------------------------------
//
// ------------------------------------------------------------------------

module scariv_lsu_vipt_st_buffer_amo_entry
  import scariv_lsu_pkg::*;
(
 input logic  i_clk,
 input logic  i_reset_n,

 input logic  i_load,
 input        st_buffer_entry_t i_entry,
 input logic  i_merge_accept,

 output logic o_l1d_rd_req, // Read Request of L1D
 input logic  i_l1d_rd_accepted,

 output logic o_mshr_req, // Refill request to MSHR
 input logic  i_mshr_accepted,

 input logic [scariv_conf_pkg::MSHR_ENTRY_SIZE-1: 0] i_mshr_search_update_hit,
 input logic [scariv_conf_pkg::MSHR_ENTRY_SIZE-1: 0] i_mshr_search_hit,
 input logic [scariv_conf_pkg::MSHR_ENTRY_SIZE-1: 0] i_mshr_evict_search_hit,
 input logic [scariv_conf_pkg::MSHR_ENTRY_SIZE-1: 0] i_mshr_evict_sent,

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
 input mshr_resp_t    i_st_mshr_resp,
 input mshr_resolve_t i_mshr_resolve,

 // Atomic Operation
 amo_op_if.master amo_op_if,

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

logic                     is_entry_rmw;
logic                     is_entry_amo;

logic         w_l1d_rd_req_next;

logic [scariv_conf_pkg::LSU_INST_NUM-1: 0] w_fwd_lsu_hit;

logic                                      w_mshr_resolve_vld;
assign w_mshr_resolve_vld = |(~i_mshr_resolve.mshr_entry_valids & r_entry.mshr_index_oh);

riscv_pkg::xlen_t w_amo_op_result;
riscv_pkg::xlen_t r_amo_l1d_data;
riscv_pkg::xlen_t w_amo_l1d_data_next;

assign is_entry_rmw = r_entry.rmwop != decoder_lsu_ctrl_pkg::RMWOP__;
assign is_entry_amo = (r_entry.rmwop != decoder_lsu_ctrl_pkg::RMWOP__) &
                      (r_entry.rmwop != decoder_lsu_ctrl_pkg::RMWOP_LR) &
                      (r_entry.rmwop != decoder_lsu_ctrl_pkg::RMWOP_SC);


always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_entry <= 'h0;

    r_amo_l1d_data <= 'h0;
  end else begin
    r_entry <= w_entry_next;

    r_amo_l1d_data <= w_amo_l1d_data_next;
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
  w_amo_l1d_data_next = r_amo_l1d_data;

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
      end else if (i_mshr_search_update_hit != 'h0) begin
        w_state_next = ST_BUF_RD_L1D;
      end else if (i_mshr_search_hit != 'h0) begin
        if (i_mshr_resolve.valid &
            (i_mshr_resolve.resolve_index_oh == i_mshr_search_hit)) begin
          // MSHR hit and resolve immediately : replay again
          w_state_next = ST_BUF_RD_L1D;
        end else begin
          w_state_next = ST_BUF_WAIT_REFILL; // Replay
          w_entry_next.mshr_index_oh = i_mshr_search_hit;
        end
      end else if (i_mshr_evict_search_hit != 0) begin
        if (|(i_mshr_evict_search_hit & i_mshr_evict_sent)) begin
          // Already evicted
          w_state_next = ST_BUF_MSHR_REFILL;
        end else begin
          w_state_next = ST_BUF_WAIT_REFILL; // Todo: Should be merge
          w_entry_next.mshr_index_oh = i_mshr_search_hit;
        end
      end else if (i_l1d_rd_s1_conflict) begin
        w_entry_next.l1d_high_priority = 1'b1;
        w_state_next = ST_BUF_RD_L1D;
      end else if (i_l1d_rd_s1_miss) begin
        w_state_next = ST_BUF_MSHR_REFILL;
        w_entry_next.l1d_way = i_l1d_s1_way;
      end else begin
        if (is_entry_amo & !r_entry.amo_op_done) begin
          w_state_next = ST_BUF_AMO_OPERATION;

          w_entry_next.l1d_way = i_l1d_s1_way;
          /* verilator lint_off SELRANGE */
          w_amo_l1d_data_next = i_l1d_s1_data[paddr_partial +: riscv_pkg::XLEN_W];
        end else begin
          w_entry_next.l1d_way = i_l1d_s1_way;
          w_state_next = ST_BUF_L1D_UPDATE;
        end
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
    ST_BUF_MSHR_REFILL: begin
      if (i_mshr_accepted) begin
        if (i_st_mshr_resp.evict_conflict) begin
          w_state_next = ST_BUF_WAIT_EVICT;
          w_entry_next.mshr_index_oh = i_st_mshr_resp.mshr_index_oh;
        end else if (i_st_mshr_resp.mshr_index_oh != 'h0) begin
          w_state_next = ST_BUF_WAIT_REFILL; // Replay
          w_entry_next.mshr_index_oh = i_st_mshr_resp.mshr_index_oh;
        end else if (i_st_mshr_resp.full) begin
          w_state_next = ST_BUF_WAIT_FULL;
        end else begin
          // if index_oh is zero, it means MSHR is correctly allocated,
          // so move to STQ_COMMIT and rerun, and set index_oh conflict bit set again.
          w_state_next = ST_BUF_RD_L1D; // Replay
        end
      end
    end // case: ST_BUF_MSHR_REFILL
    ST_BUF_WAIT_EVICT : begin
      if (w_mshr_resolve_vld) begin
        w_state_next = ST_BUF_RD_L1D; // Replay
      end
    end
    ST_BUF_WAIT_REFILL: begin
      if (is_entry_rmw) begin
        if (w_mshr_resolve_vld) begin
          // Finish MSHR L1D update
          w_state_next = ST_BUF_RD_L1D;
        end
      end else begin
        if (i_mshr_l1d_wr_merged) begin
          w_state_next = ST_BUF_L1D_MERGE;
        end else if (w_mshr_resolve_vld) begin
          w_state_next = ST_BUF_RD_L1D;
        end
      end // else: !if(is_entry_rmw)
    end
    ST_BUF_WAIT_SNOOP : begin
      if (!i_snoop_busy) begin
        w_state_next = ST_BUF_RD_L1D;
      end
    end
    ST_BUF_WAIT_FULL: begin
      if (!i_st_mshr_resp.full) begin
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
    ST_BUF_AMO_OPERATION : begin
      w_state_next = ST_BUF_L1D_UPDATE;
      w_entry_next.amo_op_done = 1'b1;

      for (integer idx = 0; idx < riscv_pkg::XLEN_W; idx+=8) begin
        if (paddr_partial[$clog2(ST_BUF_WIDTH)-1: 0] + idx < ST_BUF_WIDTH) begin
          w_entry_next.data[(paddr_partial[$clog2(ST_BUF_WIDTH)-1: 0] + idx) +: 8] = amo_op_if.result[idx +: 8];
        end
      end
    end
    default : begin
    end
  endcase // case (r_state)
end // always_comb

assign o_entry = r_entry;
assign o_state = r_state;
assign o_ready_to_merge = r_entry.valid &
                          !is_entry_rmw &
                          (r_state != ST_BUF_L1D_UPDATE) &
                          (r_state != ST_BUF_L1D_UPD_RESP) &
                          (r_state != ST_BUF_L1D_MERGE) &
                          (r_state != ST_BUF_L1D_MERGE2) &
                          (r_state != ST_BUF_WAIT_FINISH);
assign o_l1d_rd_req = r_entry.valid & (r_state == ST_BUF_RD_L1D);
assign o_mshr_req    = r_entry.valid & (r_state == ST_BUF_MSHR_REFILL);
assign o_l1d_wr_req = r_entry.valid & (r_state == ST_BUF_L1D_UPDATE);

// ------------------
// Atomic Operations
// ------------------
assign amo_op_if.valid = r_state == ST_BUF_AMO_OPERATION;
assign amo_op_if.rmwop = r_entry.rmwop;
assign amo_op_if.size  = r_entry.size;
assign amo_op_if.data0 = r_entry.data[paddr_partial +: riscv_pkg::XLEN_W];
assign amo_op_if.data1 = r_amo_l1d_data;


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

endmodule // scariv_lsu_vipt_st_buffer_amo_entry
