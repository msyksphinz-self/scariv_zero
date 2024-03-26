// ------------------------------------------------------------------------
// NAME : scariv_vlsu_stq
// TYPE : module
// ------------------------------------------------------------------------
// Vector LSU Store Queue
// Dynamically Allocation
// ------------------------------------------------------------------------
//
// ------------------------------------------------------------------------

module scariv_vlsu_stq
  import scariv_vec_pkg::*;
(
 input logic i_clk,
 input logic i_reset_n,

 vlsu_lsq_req_if.slave          vlsu_stq_req_if,
 // ROB notification interface
 rob_info_if.slave              rob_info_if,
 // Commit notification
 commit_if.monitor              commit_if,
 // Branch Flush Notification
 br_upd_if.slave                br_upd_if,
 // vs3 read port Interface
 vec_regread_if.master          vec_vs3_rd_if,
 // Store Buffer Interface
 st_buffer_if.master            st_buffer_if,
 vstq_haz_check_if.slave        vstq_haz_check_if[scariv_conf_pkg::LSU_INST_NUM]     // VSTQ Hazard Check
 );

typedef logic [riscv_pkg::PADDR_W-1: $clog2(riscv_vec_conf_pkg::DLEN_W/8) + $clog2(VLSU_STQ_BANK_SIZE)] vstq_paddr_t;
function automatic vstq_paddr_t to_vstq_paddr (scariv_pkg::paddr_t paddr);
  return paddr[riscv_pkg::PADDR_W-1: $clog2(riscv_vec_conf_pkg::DLEN_W/8) + $clog2(VLSU_STQ_BANK_SIZE)];
endfunction // vstq_paddr
function automatic scariv_pkg::paddr_t to_paddr (logic [$clog2(VLSU_LDQ_BANK_SIZE)-1: 0] bank_idx, vstq_paddr_t paddr);
  return {paddr, bank_idx, {$clog2(riscv_vec_conf_pkg::DLEN_W/8){1'b0}}};
endfunction // to_paddr

typedef struct packed {
  logic                valid;
  logic                ready_to_mv_stbuf;
  scariv_pkg::cmt_id_t cmt_id;
  scariv_pkg::grp_id_t grp_id;
  scariv_pkg::rnid_t   vs3_phy_idx;
  vec_pos_t            vs3_pos;
  dlenb_t              strb;
  vstq_paddr_t         paddr;
  logic                is_committed;
`ifdef SIMULATION
  scariv_pkg::paddr_t sim_paddr;
`endif // SIMULATION
} vlsu_stq_entry_t;

typedef enum logic [ 2: 0] {
  INIT            = 0,
  WAIT_COMMIT     = 1,
  READ_VS3        = 2,
  GET_VS3         = 3,
  COMMIT_MV_STBUF = 4,
  FINISH          = 5
} state_t;
state_t r_state[VLSU_STQ_BANK_SIZE][VLSU_STQ_SIZE];


vlsu_stq_entry_t r_vlsu_stq_entries[VLSU_STQ_BANK_SIZE][VLSU_STQ_SIZE];
logic [VLSU_STQ_BANK_SIZE-1:0]                    w_vs3_regread_req;
vlsu_stq_entry_t                                  w_vlsu_stq_vs3_entry_bank[VLSU_STQ_BANK_SIZE];
logic [$clog2(VLSU_STQ_BANK_SIZE)-1: 0]           w_vlsu_stq_bank_idx;
vlsu_stq_entry_t                                  w_vlsu_stq_vs3_entry;
logic [VLSU_STQ_BANK_SIZE-1:0][VLSU_STQ_SIZE-1:0] w_stbuf_req_valid;
logic                                             w_commit_flush;

logic [$clog2(VLSU_STQ_BANK_SIZE)-1: 0] w_vs3_regread_bank_accepted_index;
logic [$clog2(VLSU_STQ_BANK_SIZE)-1: 0] r_vs3_regread_bank_accepted_index_d1;
logic [VLSU_STQ_BANK_SIZE-1: 0]         w_vs3_regread_bank_accepted;

logic                                   st_buffer_ex0_proceed_valid;
logic                                   st_buffer_ex1_proceed_valid;

logic                                   r_ex1_st_buffer_valid;
scariv_pkg::paddr_t                     r_ex1_st_buffer_paddr;
dlenb_t                                 r_ex1_st_buffer_strb;
logic                                   r_ex1_st_buffer_skid_valid;
dlen_t                                  r_ex1_st_buffer_skid_data;

logic [scariv_conf_pkg::LSU_INST_NUM-1: 0] w_vlsu_haz_check_hit[VLSU_STQ_BANK_SIZE][VLSU_STQ_SIZE];

assign st_buffer_ex0_proceed_valid = ~r_ex1_st_buffer_valid | st_buffer_ex1_proceed_valid;
assign st_buffer_ex1_proceed_valid = !st_buffer_if.valid | (st_buffer_if.resp != scariv_lsu_pkg::ST_BUF_FULL);

assign w_commit_flush = scariv_pkg::is_flushed_commit(commit_if.commit_valid, commit_if.payload);

logic [VLSU_STQ_BANK_SIZE-1: 0]            w_vlsu_stq_freelist_full;
logic [VLSU_STQ_BANK_SIZE-1: 0]            w_vlsu_stq_all_entry_younger_or_equal_than_load;
logic [$clog2(VLSU_STQ_BANK_SIZE)-1: 0]    w_vlsu_alloc_bank_index;
assign w_vlsu_alloc_bank_index = vlsu_stq_req_if.paddr[$clog2(riscv_vec_conf_pkg::DLEN_W/8) +: $clog2(VLSU_STQ_BANK_SIZE)];

assign vlsu_stq_req_if.resp = w_vlsu_stq_all_entry_younger_or_equal_than_load[w_vlsu_alloc_bank_index] ? scariv_vec_pkg::VSTQ_RESP_FULL_FLUSH :
                              w_vlsu_stq_freelist_full[w_vlsu_alloc_bank_index]               ? scariv_vec_pkg::VSTQ_RESP_FULL_WAIT :
                              scariv_vec_pkg::VSTQ_RESP_ACCEPTED;

generate for (genvar bank_idx = 0; bank_idx < VLSU_STQ_BANK_SIZE; bank_idx++) begin : bank_loop

  logic [VLSU_STQ_SIZE-1: 0] w_entry_load_index  [1];
  logic [VLSU_STQ_SIZE-1: 0] w_entry_finish_index[1];
  logic [VLSU_STQ_SIZE-1: 0] w_vs3_regread_req_bank;
  logic                      w_freelist_pop_valid;
  assign w_freelist_pop_valid = vlsu_stq_req_if.valid &
                                w_vlsu_alloc_bank_index == bank_idx[$clog2(VLSU_STQ_BANK_SIZE)-1: 0] &
                                ~w_vlsu_stq_freelist_full[bank_idx];
  logic [VLSU_STQ_SIZE-1: 0] w_entry_is_younger_or_eq_than_load;

  assign w_vlsu_stq_all_entry_younger_or_equal_than_load[bank_idx] = &w_entry_is_younger_or_eq_than_load;

  scariv_freelist_multiports_oh
    #(.WIDTH (VLSU_STQ_SIZE),
      .PORTS (1)
      )
  u_entry_freelist
    (
     .i_clk     (i_clk    ),
     .i_reset_n (i_reset_n),

     .i_push_id (w_entry_finish_index),
     .i_pop     (w_freelist_pop_valid),
     .o_pop_id  (w_entry_load_index  ),

     .o_is_empty (),
     .o_is_full  (w_vlsu_stq_freelist_full[bank_idx])
     );

  function automatic logic [$clog2(VLSU_STQ_SIZE)-1:0] rr (logic [VLSU_STQ_SIZE-1:0] req, logic [VLSU_STQ_SIZE-1:0] curr);
    logic [$clog2(VLSU_STQ_SIZE)-1:0] index;

    for (int i = 1; i <= VLSU_STQ_SIZE; i++) begin
      index = (curr + i) % VLSU_STQ_SIZE;
      if (req[index]) begin
        return index;
      end
    end
    return 0;
  endfunction // rr

  logic [$clog2(VLSU_STQ_SIZE)-1: 0] r_regread_req_index_d1;
  logic [$clog2(VLSU_STQ_SIZE)-1: 0] w_vs3_regread_accepted_index;
  logic [VLSU_STQ_SIZE-1: 0]         w_vs3_regread_accepted;

  for (genvar stq_idx = 0; stq_idx < VLSU_STQ_SIZE; stq_idx++) begin : stq_loop

    logic w_entry_is_older_than_load;
    assign w_entry_is_older_than_load = scariv_pkg::id0_is_older_than_id1 (r_vlsu_stq_entries[bank_idx][stq_idx].cmt_id,
                                                                           r_vlsu_stq_entries[bank_idx][stq_idx].grp_id,
                                                                           vlsu_stq_req_if.cmt_id,
                                                                           vlsu_stq_req_if.grp_id
                                                                           );
    assign w_entry_is_younger_or_eq_than_load[stq_idx] = r_vlsu_stq_entries[bank_idx][stq_idx].valid & !w_entry_is_older_than_load;

    logic w_br_flush;
    assign w_br_flush     = scariv_pkg::is_br_flush_target(r_vlsu_stq_entries[bank_idx][stq_idx].cmt_id,
                                                           r_vlsu_stq_entries[bank_idx][stq_idx].grp_id,
                                                           br_upd_if.cmt_id, br_upd_if.grp_id,
                                                           br_upd_if.dead, br_upd_if.mispredict) & br_upd_if.update & r_vlsu_stq_entries[bank_idx][stq_idx].valid;
    vlsu_stq_entry_t w_vlsu_stq_entry_next;
    state_t          w_state_next;

    logic  w_ready_to_mv_stbuf;
    scariv_pkg::grp_id_t w_prev_grp_id_mask;
    assign w_prev_grp_id_mask = r_vlsu_stq_entries[bank_idx][stq_idx].grp_id-1;
    assign w_ready_to_mv_stbuf = (rob_info_if.cmt_id == r_vlsu_stq_entries[bank_idx][stq_idx].cmt_id) &
                                 |(rob_info_if.done_grp_id & ~rob_info_if.except_valid & r_vlsu_stq_entries[bank_idx][stq_idx].grp_id) &
                                 ((w_prev_grp_id_mask & rob_info_if.done_grp_id) == w_prev_grp_id_mask);


    always_comb begin
      w_vlsu_stq_entry_next = r_vlsu_stq_entries[bank_idx][stq_idx];
      w_state_next = r_state[bank_idx][stq_idx];

      case (r_state[bank_idx][stq_idx])
        INIT : begin
          if (w_freelist_pop_valid & w_entry_load_index[0][stq_idx]) begin
            w_vlsu_stq_entry_next.valid        = 1'b1;
            w_vlsu_stq_entry_next.ready_to_mv_stbuf = 1'b0;
            w_vlsu_stq_entry_next.cmt_id       = vlsu_stq_req_if.cmt_id;
            w_vlsu_stq_entry_next.grp_id       = vlsu_stq_req_if.grp_id;
            w_vlsu_stq_entry_next.vs3_phy_idx  = vlsu_stq_req_if.vs3_phy_idx;
            w_vlsu_stq_entry_next.vs3_pos      = vlsu_stq_req_if.vs3_pos;
            w_vlsu_stq_entry_next.strb         = vlsu_stq_req_if.strb;
            w_vlsu_stq_entry_next.paddr        = to_vstq_paddr(vlsu_stq_req_if.paddr);
            w_vlsu_stq_entry_next.is_committed = 1'b0;

            if (w_commit_flush) begin
              w_state_next = FINISH;
            end else begin
              w_state_next = WAIT_COMMIT;
            end

`ifdef SIMULATION
            w_vlsu_stq_entry_next.sim_paddr    = vlsu_stq_req_if.paddr;
`endif // SIMULATION
          end
        end
        WAIT_COMMIT : begin
          w_vlsu_stq_entry_next.ready_to_mv_stbuf = r_vlsu_stq_entries[bank_idx][stq_idx].ready_to_mv_stbuf | w_ready_to_mv_stbuf;
          if (commit_if.is_commit_flush_target(r_vlsu_stq_entries[bank_idx][stq_idx].cmt_id,
                                               r_vlsu_stq_entries[bank_idx][stq_idx].grp_id) |
              w_br_flush) begin
            w_state_next = FINISH;
          end else if ((w_ready_to_mv_stbuf | r_vlsu_stq_entries[bank_idx][stq_idx].ready_to_mv_stbuf) & st_buffer_ex0_proceed_valid) begin
            w_state_next = READ_VS3;
          end
          w_vlsu_stq_entry_next.is_committed = r_vlsu_stq_entries[bank_idx][stq_idx].is_committed | w_ready_to_mv_stbuf;
        end
        READ_VS3 : begin
          if (st_buffer_ex1_proceed_valid & w_vs3_regread_accepted[stq_idx] & w_vs3_regread_bank_accepted[bank_idx]) begin
            w_state_next = GET_VS3;
          end
        end
        GET_VS3 : begin
          if (~st_buffer_if.valid | st_buffer_if.resp != scariv_lsu_pkg::ST_BUF_FULL) begin
            w_state_next = COMMIT_MV_STBUF;
          end
        end
        COMMIT_MV_STBUF : begin
          if (st_buffer_if.resp != scariv_lsu_pkg::ST_BUF_FULL) begin
            w_state_next = FINISH;
          end
        end
        FINISH : begin
          w_vlsu_stq_entry_next.valid = 1'b0;
          w_state_next = INIT;
        end
        default : begin
        end
      endcase // case (r_state[bank_idx][stq_idx])
    end // always_comb

    assign w_vs3_regread_req_bank          [stq_idx] = r_state[bank_idx][stq_idx] == READ_VS3;
    assign w_stbuf_req_valid     [bank_idx][stq_idx] = r_state[bank_idx][stq_idx] == COMMIT_MV_STBUF;
    assign w_entry_finish_index  [0]       [stq_idx] = r_state[bank_idx][stq_idx] == FINISH;

    // Scalar Load to VSTQ hazard check
    for (genvar spipe_idx = 0; spipe_idx < scariv_conf_pkg::LSU_INST_NUM; spipe_idx++) begin : sload_vstq_haz_loop
      logic  vstq_is_older_than_sload;
      assign vstq_is_older_than_sload = scariv_pkg::id0_is_older_than_id1 (r_vlsu_stq_entries[bank_idx][stq_idx].cmt_id,
                                                                           r_vlsu_stq_entries[bank_idx][stq_idx].grp_id,
                                                                           vstq_haz_check_if[spipe_idx].ex2_cmt_id,
                                                                           vstq_haz_check_if[spipe_idx].ex2_grp_id);
      assign w_vlsu_haz_check_hit[bank_idx][stq_idx][spipe_idx] = (vstq_is_older_than_sload | r_vlsu_stq_entries[bank_idx][stq_idx].is_committed) &
                                                                  r_vlsu_stq_entries[bank_idx][stq_idx].valid &
                                                                  (vstq_haz_check_if[spipe_idx].ex2_paddr[riscv_pkg::PADDR_W-1: $clog2(scariv_vec_pkg::DLENB)] ==
                                                                   {r_vlsu_stq_entries[bank_idx][stq_idx].paddr, bank_idx[$clog2(VLSU_STQ_BANK_SIZE)-1: 0]});
    end

    always_ff @ (posedge i_clk, negedge i_reset_n) begin
      if (!i_reset_n) begin
        r_vlsu_stq_entries[bank_idx][stq_idx].valid <= 1'b0;
        r_state           [bank_idx][stq_idx] <= INIT;
      end else begin
        r_vlsu_stq_entries[bank_idx][stq_idx] <= w_vlsu_stq_entry_next;
        r_state           [bank_idx][stq_idx] <= w_state_next;
      end // else: !if(!i_reset_n)
    end
  end // block: stq_loop

  assign w_vs3_regread_req [bank_idx] = |(w_vs3_regread_req_bank);

  always_ff @ (posedge i_clk, posedge i_reset_n) begin
    if (!i_reset_n) begin
      r_regread_req_index_d1 <= VLSU_STQ_SIZE-1;
    end else if (|(w_vs3_regread_req_bank)) begin
      r_regread_req_index_d1 <= w_vs3_regread_accepted_index;
    end
  end

  assign w_vs3_regread_accepted_index = rr(w_vs3_regread_req_bank, r_regread_req_index_d1);
  assign w_vs3_regread_accepted = 1 << w_vs3_regread_accepted_index;

  bit_oh_or
    #(
      .T(vlsu_stq_entry_t),
      .WORDS(VLSU_STQ_SIZE)
      )
  bit_oh_entry
    (
     .i_oh      (w_vs3_regread_accepted             ),
     .i_data    (r_vlsu_stq_entries       [bank_idx]),
     .o_selected(w_vlsu_stq_vs3_entry_bank[bank_idx])
     );
end endgenerate

function automatic logic [$clog2(VLSU_STQ_BANK_SIZE)-1:0] rr (logic [VLSU_STQ_BANK_SIZE-1:0] req, logic [VLSU_STQ_BANK_SIZE-1:0] curr);
  logic [$clog2(VLSU_STQ_BANK_SIZE)-1:0] index;

  for (int i = 1; i <= VLSU_STQ_BANK_SIZE; i++) begin
    index = (curr + i) % VLSU_STQ_BANK_SIZE;
    if (req[index]) begin
      return index;
    end
  end
  return 0;
endfunction // rr

assign w_vs3_regread_bank_accepted_index = rr(w_vs3_regread_req, r_vs3_regread_bank_accepted_index_d1);
assign w_vs3_regread_bank_accepted = 1 << w_vs3_regread_bank_accepted_index;

always_ff @ (posedge i_clk, posedge i_reset_n) begin
  if (!i_reset_n) begin
    r_vs3_regread_bank_accepted_index_d1 <= VLSU_STQ_BANK_SIZE-1;
  end else if (|(w_vs3_regread_req)) begin
    r_vs3_regread_bank_accepted_index_d1 <= w_vs3_regread_bank_accepted_index;
  end
end

bit_oh_or #(.T(vlsu_stq_entry_t), .WORDS(VLSU_STQ_BANK_SIZE)) bit_oh_vs3 (.i_oh(w_vs3_regread_bank_accepted), .i_data(w_vlsu_stq_vs3_entry_bank), .o_selected(w_vlsu_stq_vs3_entry));
bit_encoder #(.WIDTH(VLSU_STQ_BANK_SIZE)) bit_oh_bank (.i_in(w_vs3_regread_bank_accepted), .o_out(w_vlsu_stq_bank_idx));

assign vec_vs3_rd_if.valid = |w_vs3_regread_req;
assign vec_vs3_rd_if.rnid  = w_vlsu_stq_vs3_entry.vs3_phy_idx;
assign vec_vs3_rd_if.pos   = w_vlsu_stq_vs3_entry.vs3_pos;

always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    st_buffer_if.valid <= 1'b0;
    r_ex1_st_buffer_skid_valid <= 1'b0;
  end else begin
    if (st_buffer_ex1_proceed_valid) begin
      r_ex1_st_buffer_valid <= vec_vs3_rd_if.valid;
      r_ex1_st_buffer_paddr <= to_paddr(w_vlsu_stq_bank_idx, w_vlsu_stq_vs3_entry.paddr);
      r_ex1_st_buffer_strb  <= w_vlsu_stq_vs3_entry.strb;
    end

    if (r_ex1_st_buffer_valid & ~st_buffer_ex1_proceed_valid) begin
      if (~r_ex1_st_buffer_skid_valid) begin
        r_ex1_st_buffer_skid_data <= vec_vs3_rd_if.data;
        r_ex1_st_buffer_skid_valid <= 1'b1;
      end
    end else begin
      r_ex1_st_buffer_skid_valid <= 1'b0;
    end

    if (st_buffer_ex1_proceed_valid) begin
      st_buffer_if.valid <= r_ex1_st_buffer_valid;
      st_buffer_if.paddr <= r_ex1_st_buffer_paddr;
      st_buffer_if.strb  <= r_ex1_st_buffer_strb;
      st_buffer_if.data  <= r_ex1_st_buffer_skid_valid ? r_ex1_st_buffer_skid_data : vec_vs3_rd_if.data;
    end
  end
end


// Scalar Load to VSTQ Hazard Check
generate for (genvar spipe_idx = 0; spipe_idx < scariv_conf_pkg::LSU_INST_NUM; spipe_idx++) begin : sload_vstq_haz_loop
  logic [VLSU_STQ_BANK_SIZE-1: 0] w_bank_vlsu_haz_check_hit;
  for (genvar bank_idx = 0; bank_idx < VLSU_STQ_BANK_SIZE; bank_idx++) begin : bank_loop
    logic [VLSU_STQ_SIZE-1: 0] w_spipe_vlsu_haz_check_hit;
    for (genvar stq_idx = 0; stq_idx < VLSU_STQ_SIZE; stq_idx++) begin : stq_loop;
      assign w_spipe_vlsu_haz_check_hit[stq_idx] = w_vlsu_haz_check_hit[bank_idx][stq_idx][spipe_idx];
    end
    assign w_bank_vlsu_haz_check_hit[bank_idx] = |w_spipe_vlsu_haz_check_hit;
  end

  logic  w_vstq_loading_is_older_than_sload;
  logic  w_vstq_loading_sload_haz_check_hit;
  assign w_vstq_loading_is_older_than_sload = scariv_pkg::id0_is_older_than_id1 (vlsu_stq_req_if.cmt_id,
                                                                                 vlsu_stq_req_if.grp_id,
                                                                                 vstq_haz_check_if[spipe_idx].ex2_cmt_id,
                                                                                 vstq_haz_check_if[spipe_idx].ex2_grp_id);
  assign w_vstq_loading_sload_haz_check_hit = w_vstq_loading_is_older_than_sload &
                                              vlsu_stq_req_if.valid &
                                              (vstq_haz_check_if[spipe_idx].ex2_paddr[riscv_pkg::PADDR_W-1: $clog2(scariv_vec_pkg::DLENB)] ==
                                               vlsu_stq_req_if.paddr                 [riscv_pkg::PADDR_W-1: $clog2(scariv_vec_pkg::DLENB)]);

  assign vstq_haz_check_if[spipe_idx].ex2_haz_valid = vstq_haz_check_if[spipe_idx].ex2_valid & ((|w_bank_vlsu_haz_check_hit) |
                                                                                                w_vstq_loading_sload_haz_check_hit);
end endgenerate // block: sload_vstq_haz_loop

endmodule // scariv_vlsu_stq
