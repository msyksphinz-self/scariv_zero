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

 output logic o_l1d_rd_req, // Read Request of L1D

 input logic  i_l1d_rd_accepted,
 input logic  i_l1d_rd_miss,
 input logic  i_l1d_rd_conflict,
 input logic  i_evict_merged,
 input logic  i_l1d_wr_conflict,

 input logic i_lrq_full,
 input logic i_lrq_conflict,
 input logic [msrh_pkg::LRQ_ENTRY_SIZE-1:0] i_lrq_index_oh,
 input lrq_resolve_t i_lrq_resolve,

 output logic             o_ready_to_merge,
 output st_buffer_entry_t o_entry,
 output logic             o_entry_finish
 );

st_buffer_entry_t w_entry_next;
st_buffer_entry_t r_entry;

st_buffer_state_t r_state;
st_buffer_state_t w_state_next;

logic         w_l1d_rd_req_next;

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
      if (i_l1d_rd_miss) begin
        w_state_next = ST_BUF_LRQ_REFILL;
      end else if (i_l1d_rd_conflict) begin
        w_state_next = ST_BUF_RD_L1D;
      end else if (i_evict_merged) begin
        w_state_next = ST_BUF_INIT;
        o_entry_finish = 1'b1;
      end else begin
        w_state_next = ST_BUF_L1D_UPDATE;
      end
    end
    ST_BUF_L1D_UPDATE: begin
      if (i_l1d_wr_conflict) begin
        w_state_next = ST_BUF_RD_L1D;
      end else begin
        w_state_next = ST_BUF_INIT;
        o_entry_finish = 1'b1;
      end
    end
    ST_BUF_LRQ_REFILL: begin
      if (i_lrq_index_oh == 'h0) begin
        // if index_oh is zero, it means LRQ is correctly allocated,
        // so move to STQ_COMMIT and rerun, and set index_oh conflict bit set again.
        w_state_next = ST_BUF_RD_L1D; // Replay
      end else if (i_lrq_resolve.valid &&
                   i_lrq_resolve.resolve_index_oh == r_entry.lrq_index_oh) begin
        w_state_next = ST_BUF_RD_L1D; // Replay
      end
    end
    default : begin
    end
  endcase // case (r_state)
end // always_comb

assign o_entry = r_entry;
assign o_ready_to_merge = r_entry.valid & (r_state != ST_BUF_L1D_UPDATE);

endmodule // msrh_st_buffer_entry
