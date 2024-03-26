// ------------------------------------------------------------------------
// NAME : scariv_lsu_replay_queue
// TYPE : module
// ------------------------------------------------------------------------
// LSU Replay Queue
// ------------------------------------------------------------------------
//
// ------------------------------------------------------------------------

module scariv_lsu_fast_replay_queue
  import scariv_lsu_pkg::*;
(
    input logic i_clk,
    input logic i_reset_n,

    output logic o_full,
    output logic o_almost_full,

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

// localparam REPLAY_QUEUE_SIZE = (scariv_conf_pkg::LDQ_SIZE + scariv_conf_pkg::STQ_SIZE) / scariv_conf_pkg::LSU_INST_NUM + 1;
localparam REPLAY_QUEUE_SIZE = scariv_conf_pkg::RV_LSU_ENTRY_SIZE / scariv_conf_pkg::LSU_INST_NUM;
localparam REPLAY_QUEUE_W = $clog2(REPLAY_QUEUE_SIZE);

typedef struct packed {
  logic                          valid;
  logic                          dead;
  scariv_pkg::cmt_id_t           cmt_id;
  scariv_pkg::grp_id_t           grp_id;
  scariv_lsu_pkg::ex2_haz_t      hazard_typ;
  logic [HAZARD_INDEX_SIZE-1: 0] hazard_index;
} replay_queue_t;

typedef struct packed {
    logic [31: 0]                    inst;
    decoder_inst_cat_pkg::inst_cat_t cat;
    logic                            oldest_valid;
    scariv_pkg::reg_rd_issue_t       rd_reg;
    scariv_pkg::reg_wr_issue_t       wr_reg;
    scariv_pkg::paddr_t              paddr;
    logic                            is_uc;
} replay_payload_t;

(* mark_debug="true" *) replay_queue_t   r_replay_queue  [REPLAY_QUEUE_SIZE];
replay_payload_t w_replay_payload;

logic [REPLAY_QUEUE_W-1: 0]          w_pop_freelist_id;
logic [REPLAY_QUEUE_SIZE-1: 0]       w_resolved_list;
logic [REPLAY_QUEUE_SIZE-1: 0]       w_resolved_list_oh;
logic [REPLAY_QUEUE_W-1: 0]          w_resolved_index;

/*-----------
 * Freelist
 *-----------*/
logic                                w_freelist_push;
logic                                w_freelist_pop;
assign w_freelist_push = lsu_pipe_req_if.valid & lsu_pipe_req_if.ready | r_replay_queue[w_resolved_index].valid & r_replay_queue[w_resolved_index].dead;
assign w_freelist_pop  = lsu_pipe_haz_if.valid;

scariv_freelist
  #(.SIZE(REPLAY_QUEUE_SIZE),
    .WIDTH(REPLAY_QUEUE_W),
    .INIT(0)
    )
u_freelist
  (
   .i_clk    (i_clk),
   .i_reset_n(i_reset_n),

   .i_push   (w_freelist_push),
   .i_push_id(w_resolved_index),

   .i_pop   (w_freelist_pop),
   .o_pop_id(w_pop_freelist_id),

   .o_is_empty ()
   );

logic [$clog2(REPLAY_QUEUE_SIZE)-1: 0] r_fifo_counter;
always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_fifo_counter <= 'h0;
  end else begin
    case ({w_freelist_push, w_freelist_pop})
      2'b01   : r_fifo_counter <= r_fifo_counter + 'h1;
      2'b10   : r_fifo_counter <= r_fifo_counter - 'h1;
      default : begin end
    endcase // case ({w_queue_pop, w_queue_push})
  end
end

assign o_almost_full = r_fifo_counter >= REPLAY_QUEUE_SIZE - 4; // 4(=four stage)

generate for (genvar q_idx = 0; q_idx < REPLAY_QUEUE_SIZE; q_idx++) begin : queue_loop
  logic w_commit_flush;
  logic w_br_flush;
  logic w_entry_flush;
  logic w_is_oldest;
  assign w_commit_flush = scariv_pkg::is_flushed_commit(commit_if.commit_valid, commit_if.payload) & r_replay_queue[q_idx].valid;
  assign w_br_flush     = scariv_pkg::is_br_flush_target(r_replay_queue[q_idx].cmt_id, r_replay_queue[q_idx].grp_id, br_upd_if.cmt_id, br_upd_if.grp_id,
                                                         br_upd_if.dead, br_upd_if.mispredict) & br_upd_if.update & r_replay_queue[q_idx].valid;
  assign w_entry_flush  = w_commit_flush | w_br_flush;

  assign w_is_oldest = (rob_info_if.cmt_id == r_replay_queue[q_idx].cmt_id) &
                       ((rob_info_if.done_grp_id & r_replay_queue[q_idx].grp_id-1) == r_replay_queue[q_idx].grp_id-1);


  always_ff @ (posedge i_clk, negedge i_reset_n) begin
    if (!i_reset_n) begin
      r_replay_queue[q_idx].valid <= 1'b0;
    end else begin
      if (lsu_pipe_haz_if.valid &
          (w_pop_freelist_id == q_idx)) begin
        r_replay_queue[q_idx].valid        <= 1'b1;
        r_replay_queue[q_idx].dead         <= 1'b0;
        r_replay_queue[q_idx].cmt_id       <= lsu_pipe_haz_if.payload.cmt_id;
        r_replay_queue[q_idx].grp_id       <= lsu_pipe_haz_if.payload.grp_id;
        r_replay_queue[q_idx].hazard_typ   <= lsu_pipe_haz_if.payload.hazard_typ;
        r_replay_queue[q_idx].hazard_index <= lsu_pipe_haz_if.payload.hazard_index;
      end else if (w_freelist_push &
                   (w_resolved_list_oh[q_idx])) begin
        r_replay_queue[q_idx].valid  <= 1'b0;
      end else if (r_replay_queue[q_idx].valid &
                   w_entry_flush) begin
        r_replay_queue[q_idx].dead <= 1'b1;
      end else begin
        case (r_replay_queue[q_idx].hazard_typ)
          EX2_HAZ_STQ_NONFWD_HAZ : r_replay_queue[q_idx].hazard_index <= r_replay_queue[q_idx].hazard_index & ~i_stq_rs2_resolve.index;
          EX2_HAZ_STQ_FWD_MISS   : r_replay_queue[q_idx].hazard_index <= r_replay_queue[q_idx].hazard_index & ~i_stq_rs2_resolve.index;
          EX2_HAZ_RMW_ORDER_HAZ  : r_replay_queue[q_idx].hazard_index <= w_is_oldest & i_st_buffer_empty & i_missu_is_empty ? 'h0 : 1'b1;
          EX2_HAZ_L1D_CONFLICT   : r_replay_queue[q_idx].hazard_index <= 'h0; // Replay immediately
          EX2_HAZ_MISSU_FULL     : r_replay_queue[q_idx].hazard_index <= !i_missu_is_full ? 'h0 : r_replay_queue[q_idx].hazard_index;
          EX2_HAZ_MISSU_ASSIGNED : r_replay_queue[q_idx].hazard_index <= r_replay_queue[q_idx].hazard_index &
                                                                         (i_missu_resolve.valid ? ~i_missu_resolve.resolve_index_oh : i_missu_resolve.missu_entry_valids);
          default : begin
            r_replay_queue[q_idx].hazard_index <= 'h0;
          end
        endcase // case (r_replay_queue[q_idx].hazard_typ)
      end // else: !if(r_replay_queue[q_idx].valid &...
    end // else: !if(!i_reset_n)
  end // always_ff @ (posedge i_clk, negedge i_reset_n)

  assign w_resolved_list[q_idx] = r_replay_queue[q_idx].valid &
                                  ((r_replay_queue[q_idx].hazard_index == 'h0) | r_replay_queue[q_idx].dead);

end endgenerate // block: queue_loop

replay_payload_t new_replay_payload;
assign new_replay_payload.inst         = lsu_pipe_haz_if.payload.inst        ;
assign new_replay_payload.cat          = lsu_pipe_haz_if.payload.cat         ;
assign new_replay_payload.oldest_valid = lsu_pipe_haz_if.payload.oldest_valid;
assign new_replay_payload.rd_reg       = lsu_pipe_haz_if.payload.rd_reg      ;
assign new_replay_payload.wr_reg       = lsu_pipe_haz_if.payload.wr_reg      ;
assign new_replay_payload.paddr        = lsu_pipe_haz_if.payload.paddr       ;
assign new_replay_payload.is_uc        = lsu_pipe_haz_if.payload.is_uc       ;

distributed_ram
  #(.WIDTH($bits(replay_payload_t)),
    .WORDS(REPLAY_QUEUE_SIZE)
    )
u_payload_info_ram
  (
   .i_clk     (i_clk    ),
   .i_reset_n (i_reset_n),

   .i_wr      (lsu_pipe_haz_if.valid),
   .i_wr_addr (w_pop_freelist_id    ),
   .i_wr_data (new_replay_payload   ),

   .i_rd_addr (w_resolved_index),
   .o_rd_data (w_replay_payload)
   );


// always_ff @ (posedge i_clk) begin
//   if (lsu_pipe_haz_if.valid) begin
//     r_replay_payload[w_pop_freelist_id] <= new_replay_payload;
//   end
// end

bit_extract_lsb_ptr #(.WIDTH(REPLAY_QUEUE_SIZE)) u_resolved_oh    (.in(w_resolved_list), .i_ptr(w_pop_freelist_id), .out(w_resolved_list_oh));
bit_encoder         #(.WIDTH(REPLAY_QUEUE_SIZE)) u_resolved_index (.i_in(w_resolved_list_oh), .o_out(w_resolved_index));

// -------------
// Replay Issue
// -------------

assign lsu_pipe_req_if.valid                  = |w_resolved_list & ~r_replay_queue[w_resolved_index].dead;
assign lsu_pipe_req_if.payload.cmt_id         = r_replay_queue  [w_resolved_index].cmt_id       ;
assign lsu_pipe_req_if.payload.grp_id         = r_replay_queue  [w_resolved_index].grp_id       ;
assign lsu_pipe_req_if.payload.inst           = w_replay_payload.inst         ;
assign lsu_pipe_req_if.payload.cat            = w_replay_payload.cat          ;
assign lsu_pipe_req_if.payload.oldest_valid   = w_replay_payload.oldest_valid ;
assign lsu_pipe_req_if.payload.rd_reg         = w_replay_payload.rd_reg       ;
assign lsu_pipe_req_if.payload.wr_reg         = w_replay_payload.wr_reg       ;
assign lsu_pipe_req_if.payload.paddr          = w_replay_payload.paddr        ;
assign lsu_pipe_req_if.payload.is_uc          = w_replay_payload.is_uc        ;
assign lsu_pipe_req_if.payload.hazard_typ     = r_replay_queue  [w_resolved_index].hazard_typ   ;
assign lsu_pipe_req_if.payload.hazard_index   = r_replay_queue  [w_resolved_index].hazard_index ;

`ifdef SIMULATION
logic [63: 0] sim_replay_stq_nofwd_cnt;
logic [63: 0] sim_replay_stq_fwdmiss_cnt;
logic [63: 0] sim_replay_rmw_order_cnt;
logic [63: 0] sim_replay_l1d_confict_cnt;
logic [63: 0] sim_replay_missu_cnt;
logic [63: 0] sim_replay_missu_assigned_cnt;

always_ff @ (negedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    sim_replay_stq_nofwd_cnt      <= 'h0;
    sim_replay_stq_fwdmiss_cnt    <= 'h0;
    sim_replay_rmw_order_cnt      <= 'h0;
    sim_replay_l1d_confict_cnt    <= 'h0;
    sim_replay_missu_cnt          <= 'h0;
    sim_replay_missu_assigned_cnt <= 'h0;
  end else begin
    if (lsu_pipe_req_if.valid & lsu_pipe_req_if.ready) begin
      case (lsu_pipe_req_if.payload.hazard_typ)
        EX2_HAZ_STQ_NONFWD_HAZ : sim_replay_stq_nofwd_cnt      <= sim_replay_stq_nofwd_cnt      + 'h1;
        EX2_HAZ_STQ_FWD_MISS   : sim_replay_stq_fwdmiss_cnt    <= sim_replay_stq_fwdmiss_cnt    + 'h1;
        EX2_HAZ_RMW_ORDER_HAZ  : sim_replay_rmw_order_cnt      <= sim_replay_rmw_order_cnt      + 'h1;
        EX2_HAZ_L1D_CONFLICT   : sim_replay_l1d_confict_cnt    <= sim_replay_l1d_confict_cnt    + 'h1;
        EX2_HAZ_MISSU_FULL     : sim_replay_missu_cnt          <= sim_replay_missu_cnt          + 'h1;
        EX2_HAZ_MISSU_ASSIGNED : sim_replay_missu_assigned_cnt <= sim_replay_missu_assigned_cnt + 'h1;
        default : begin end
      endcase // case (lsu_pipe_req_if.valid.hazard_typ)
    end
  end // else: !if(!i_reset_n)
end // always_ff @ (negedge i_clk, negedge i_reset_n)

final begin
  $write ("==========================================\n");
  $write ("Replay Hazard Count\n\n");
  $write ("EX2_HAZ_STQ_NONFWD_HAZ : %d\n", sim_replay_stq_nofwd_cnt);
  $write ("EX2_HAZ_STQ_FWD_MISS   : %d\n", sim_replay_stq_fwdmiss_cnt);
  $write ("EX2_HAZ_RMW_ORDER_HAZ  : %d\n", sim_replay_rmw_order_cnt);
  $write ("EX2_HAZ_L1D_CONFLICT   : %d\n", sim_replay_l1d_confict_cnt);
  $write ("EX2_HAZ_MISSU_FULL     : %d\n", sim_replay_missu_cnt);
  $write ("EX2_HAZ_MISSU_ASSIGNED : %d\n", sim_replay_missu_assigned_cnt);
  $write ("==========================================\n");
end

`endif // SIMULATION


endmodule // scariv_lsu_fast_replay_queue
