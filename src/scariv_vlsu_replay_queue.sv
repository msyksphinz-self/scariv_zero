// ------------------------------------------------------------------------
// NAME : scariv_vlsu_replay_queue
// TYPE : module
// ------------------------------------------------------------------------
// LSU Replay Queue
// ------------------------------------------------------------------------
//
// ------------------------------------------------------------------------

module scariv_vlsu_replay_queue
  import scariv_lsu_pkg::*;
#(
  )
(
    input logic i_clk,
    input logic i_reset_n,

    output logic o_full,

    commit_if.monitor commit_if,
    br_upd_if.slave                br_upd_if,

    // ROB notification interface
    rob_info_if.slave      rob_info_if,

    lsu_pipe_haz_if.slave  lsu_pipe_haz_if,

    input missu_resolve_t  i_missu_resolve,
    input logic            i_missu_is_full,
    input logic            i_missu_is_empty,

    input logic            i_st_buffer_empty,
    input stq_resolve_t    i_stq_rs2_resolve,

    // Request from Replay Queue
    lsu_pipe_req_if.master lsu_pipe_req_if
);

localparam REPLAY_QUEUE_SIZE = scariv_conf_pkg::RV_VLSU_ENTRY_SIZE;
localparam REPLAY_QUEUE_W = $clog2(REPLAY_QUEUE_SIZE);

logic [REPLAY_QUEUE_W-1: 0] r_diff_counter;

logic w_head_is_oldest;

typedef struct packed {
  scariv_vec_pkg::vlsu_replay_queue_t info;
  logic [REPLAY_QUEUE_W-1: 0] diff_counter;
} queue_t;
typedef struct packed {
  logic                          valid;
  logic                          dead;
  scariv_pkg::cmt_id_t           cmt_id;
  scariv_pkg::grp_id_t           grp_id;
  scariv_lsu_pkg::ex2_haz_t      hazard_typ;
  logic [HAZARD_INDEX_SIZE-1: 0] hazard_index;
  logic                          resolved;
} replay_additional_queue_t;

queue_t w_new_replay_queue_info;
queue_t w_rd_replay_queue_info;
replay_additional_queue_t r_replay_additional_queue[REPLAY_QUEUE_SIZE];
replay_additional_queue_t w_replay_additional_queue_tail;

logic w_lsu_replay_valid;

logic w_empty;
logic w_full;
logic w_queue_push;
logic w_queue_pop;

assign lsu_pipe_haz_if.full = w_full;
assign w_queue_push = lsu_pipe_haz_if.valid & !lsu_pipe_haz_if.full;
assign w_queue_pop  = w_lsu_replay_valid & (lsu_pipe_req_if.ready | w_replay_additional_queue_tail.dead);

always_comb begin
  w_new_replay_queue_info.info         = lsu_pipe_haz_if.payload;
  w_new_replay_queue_info.diff_counter = w_empty ? 'h0 : r_diff_counter;
end

// Diff counter from previous Queue inesrtion
always_ff @ (posedge i_clk, negedge i_reset_n) begin
    if (!i_reset_n) begin
        r_diff_counter <= 'h0;
    end else begin
        if (w_empty) begin
          r_diff_counter <= 'h1;
        end else if (w_queue_push) begin
            r_diff_counter <= 'h1;
        end else begin
            r_diff_counter <= r_diff_counter + 'h1;
        end
    end
end
logic [REPLAY_QUEUE_W-1: 0] r_replay_queue_head_ptr;
logic [REPLAY_QUEUE_W-1: 0] r_replay_queue_tail_ptr;
generate for (genvar idx = 0; idx < REPLAY_QUEUE_SIZE; idx++) begin : replay_additional_loop

    logic w_commit_flush;
    logic w_br_flush;
    logic w_entry_flush;
    assign w_commit_flush = commit_if.is_flushed_commit() & r_replay_additional_queue[idx].valid;
    assign w_br_flush     = scariv_pkg::is_br_flush_target(r_replay_additional_queue[idx].cmt_id, r_replay_additional_queue[idx].grp_id, br_upd_if.cmt_id, br_upd_if.grp_id,
                                                           br_upd_if.dead, br_upd_if.mispredict) & br_upd_if.update & r_replay_additional_queue[idx].valid;
    assign w_entry_flush  = w_commit_flush | w_br_flush;


  always_ff @ (posedge i_clk, negedge i_reset_n) begin
    if (!i_reset_n) begin
      r_replay_additional_queue[idx].valid <= 1'b0;
    end else begin
      if (w_queue_push &
          (idx == r_replay_queue_head_ptr)) begin
        r_replay_additional_queue[idx].valid        <= 1'b1;
        r_replay_additional_queue[idx].dead         <= 1'b0;
        r_replay_additional_queue[idx].cmt_id       <= lsu_pipe_haz_if.cmt_id;
        r_replay_additional_queue[idx].grp_id       <= lsu_pipe_haz_if.grp_id;
        r_replay_additional_queue[idx].hazard_typ   <= lsu_pipe_haz_if.payload.hazard_typ;
        r_replay_additional_queue[idx].hazard_index <= lsu_pipe_haz_if.payload.hazard_index;
        r_replay_additional_queue[idx].resolved     <= 1'b0;
      end else if (w_queue_pop &
                   (idx == r_replay_queue_tail_ptr)) begin
        r_replay_additional_queue[idx].valid  <= 1'b0;
      end else if (r_replay_additional_queue[idx].valid) begin
        if (w_entry_flush) begin
          r_replay_additional_queue[idx].dead <= 1'b1;
        end else begin
          case (r_replay_additional_queue[idx].hazard_typ)
            EX2_HAZ_STQ_NONFWD_HAZ : r_replay_additional_queue[idx].resolved = (r_replay_additional_queue[idx].hazard_index & ~i_stq_rs2_resolve.index) == 'h0;
            EX2_HAZ_RMW_ORDER_HAZ  : r_replay_additional_queue[idx].resolved = w_head_is_oldest & i_st_buffer_empty & i_missu_is_empty;
            EX2_HAZ_L1D_CONFLICT   : r_replay_additional_queue[idx].resolved = 1'b1; // Replay immediately
            EX2_HAZ_MISSU_FULL     : r_replay_additional_queue[idx].resolved = !i_missu_is_full;
            EX2_HAZ_MISSU_ASSIGNED : r_replay_additional_queue[idx].resolved = i_missu_resolve.valid & (i_missu_resolve.resolve_index_oh == r_replay_additional_queue[idx].hazard_index) |
                                                                               ((r_replay_additional_queue[idx].hazard_index & i_missu_resolve.missu_entry_valids) == 'h0);
            EX2_HAZ_VSTQ_HAZ       : r_replay_additional_queue[idx].resolved = w_head_is_oldest;
            EX2_HAZ_VSTQ_FULL_WAIT : r_replay_additional_queue[idx].resolved = w_head_is_oldest;
            default : begin
              r_replay_additional_queue[idx].resolved = 1'b0;
              // $fatal(0, "Must not come here. hazard_typ = %d", w_rd_replay_queue_info.info.hazard_typ);
            end
          endcase // case (r_replay_additional_queue[idx].hazard_typ)
        end // else: !if(w_entry_flush)
      end // if (r_replay_additional_queue[idx].valid)
    end // else: !if(!i_reset_n)
  end // always_ff @ (posedge i_clk, negedge i_reset_n)
end endgenerate

always_ff @ (posedge i_clk, negedge i_reset_n) begin
    if (!i_reset_n) begin
        r_replay_queue_head_ptr <= 'h0;
        r_replay_queue_tail_ptr <= 'h0;
    end else begin
        if (w_queue_push) begin
            r_replay_queue_head_ptr <= r_replay_queue_head_ptr == REPLAY_QUEUE_SIZE - 1 ? 'h0 :
                                       r_replay_queue_head_ptr + 'h1;
        end
        if (w_queue_pop) begin
            r_replay_queue_tail_ptr <= r_replay_queue_tail_ptr == REPLAY_QUEUE_SIZE - 1 ? 'h0 :
                                       r_replay_queue_tail_ptr + 'h1;
        end
    end
end

ring_fifo
#(
    .T     (queue_t),
    .DEPTH (REPLAY_QUEUE_SIZE)
)
u_replay_queue
(
    .i_clk     (i_clk    ),
    .i_reset_n (i_reset_n),

    .i_push (w_queue_push  ),
    .i_data (w_new_replay_queue_info),

    .o_empty(w_empty),
    .o_full (w_full ),

    .i_pop  (w_queue_pop),
    .o_data (w_rd_replay_queue_info)
);

logic [REPLAY_QUEUE_W-1: 0] r_prev_diff_counter;

always_ff @ (posedge i_clk, negedge i_reset_n) begin
    if (!i_reset_n) begin
        r_prev_diff_counter <= 'h0;
    end else begin
        if (w_queue_pop) begin
            r_prev_diff_counter <= 'h1;
        end else begin
            r_prev_diff_counter <= r_prev_diff_counter + 'h1;
        end
    end
end

assign w_head_is_oldest = (rob_info_if.cmt_id == w_replay_additional_queue_tail.cmt_id) &
                          ((rob_info_if.done_grp_id & w_replay_additional_queue_tail.grp_id-1) == w_replay_additional_queue_tail.grp_id-1);
assign w_replay_additional_queue_tail = r_replay_additional_queue[r_replay_queue_tail_ptr];

always_comb begin
  if (!w_empty) begin
    if (w_replay_additional_queue_tail.dead) begin
      w_lsu_replay_valid = 1'b1;  // immediately remove from queue
    end else if (w_replay_additional_queue_tail.valid) begin
      if (w_replay_additional_queue_tail.resolved |
          (w_rd_replay_queue_info.diff_counter != 'h0 &&
           r_prev_diff_counter == w_rd_replay_queue_info.diff_counter ||
           w_rd_replay_queue_info.diff_counter == 'h0 && (&r_prev_diff_counter) /* Timeout */)) begin
        w_lsu_replay_valid = 1'b1;
      end else begin
        w_lsu_replay_valid = 1'b0;
      end
    end else begin
      w_lsu_replay_valid = 1'b0;
    end
  end else begin
    w_lsu_replay_valid = 1'b0;
  end

  lsu_pipe_req_if.cmt_id  = w_replay_additional_queue_tail.cmt_id;
  lsu_pipe_req_if.grp_id  = w_replay_additional_queue_tail.grp_id;
  lsu_pipe_req_if.payload = w_rd_replay_queue_info.info          ;
end // always_comb

assign lsu_pipe_req_if.valid = w_lsu_replay_valid & ~w_replay_additional_queue_tail.dead;

assign o_full = w_full;

`ifdef SIMULATION
always_ff @ (negedge i_clk, negedge i_reset_n) begin
    if (i_reset_n) begin
        if (!w_empty) begin
            case (w_rd_replay_queue_info.info.hazard_typ)
                EX2_HAZ_STQ_NONFWD_HAZ : begin end
                EX2_HAZ_RMW_ORDER_HAZ  : begin end
                EX2_HAZ_L1D_CONFLICT   : begin end
                EX2_HAZ_MISSU_FULL     : begin end
                EX2_HAZ_MISSU_ASSIGNED : begin end
                EX2_HAZ_VSTQ_HAZ       : begin end
                EX2_HAZ_VSTQ_FULL_WAIT : begin end
                default : begin
                    $fatal(0, "Must not come here. hazard_typ = %d", w_rd_replay_queue_info.info.hazard_typ);
                end
            endcase
        end // if (!w_empty)
      if (o_full & lsu_pipe_haz_if.valid) begin
        $fatal(0, "During Replay Queue full, hazard request come");
      end
    end
end
`endif // SIMULATION


endmodule
