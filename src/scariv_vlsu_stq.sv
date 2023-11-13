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
 input scariv_pkg::commit_blk_t i_commit,
 // Branch Flush Notification
 br_upd_if.slave                br_upd_if,
 // vs3 read port Interface
 vec_regread_if.master          vec_vs3_rd_if,
 // Store Buffer Interface
 st_buffer_if.master            st_buffer_if
 );

typedef logic [scariv_pkg::PADDR_W-1: $clog2(riscv_vec_conf_pkg::DLEN_W/8) + $clog2(VLSU_STQ_BANK_SIZE)] vstq_paddr_t;
function automatic vstq_paddr_t to_vstq_paddr (scariv_pkg::paddr_t paddr);
  return paddr[scariv_pkg::PADDR_W-1: $clog2(riscv_vec_conf_pkg::DLEN_W/8) + $clog2(VLSU_STQ_BANK_SIZE)];
endfunction // vstq_paddr
function automatic scariv_pkg::paddr_t to_paddr (logic [$clog2(VLSU_LDQ_BANK_SIZE)-1: 0] bank_idx, vstq_paddr_t paddr);
  return {paddr, bank_idx, {$clog2(riscv_vec_conf_pkg::DLEN_W/8){1'b0}}};
endfunction // to_paddr

typedef struct packed {
  logic                valid;
  scariv_pkg::cmt_id_t cmt_id;
  scariv_pkg::grp_id_t grp_id;
  scariv_pkg::rnid_t   vs3_phy_idx;
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
  COMMIT_MV_STBUF = 3,
  FINISH          = 4
} state_t;
state_t r_state[VLSU_STQ_BANK_SIZE][VLSU_STQ_SIZE];


vlsu_stq_entry_t r_vlsu_stq_entries[VLSU_STQ_BANK_SIZE][VLSU_STQ_SIZE];
logic [VLSU_STQ_BANK_SIZE-1:0]                    w_vs3_regread_req;
vlsu_stq_entry_t                                  w_vlsu_stq_vs3_entry_bank[VLSU_STQ_BANK_SIZE];
logic [$clog2(VLSU_STQ_BANK_SIZE)-1: 0]           w_vlsu_stq_bank_idx;
vlsu_stq_entry_t                                  w_vlsu_stq_vs3_entry;
logic [VLSU_STQ_BANK_SIZE-1:0][VLSU_STQ_SIZE-1:0] w_stbuf_req_valid;
logic                                             w_commit_flush;

assign w_commit_flush = scariv_pkg::is_flushed_commit(i_commit);

generate for (genvar bank_idx = 0; bank_idx < VLSU_STQ_BANK_SIZE; bank_idx++) begin : bank_loop

  logic [VLSU_STQ_SIZE-1: 0] w_entry_load_index  [1];
  logic [VLSU_STQ_SIZE-1: 0] w_entry_finish_index[1];
  logic [VLSU_STQ_SIZE-1: 0] w_vs3_regread_req_bank;
  logic                      w_vlsu_stq_freelist_full;
  logic                      w_freelist_pop_valid;
  assign w_freelist_pop_valid = vlsu_stq_req_if.valid &
                                vlsu_stq_req_if.paddr[$clog2(riscv_vec_conf_pkg::DLEN_W/8) +: $clog2(VLSU_STQ_BANK_SIZE)] == bank_idx[$clog2(VLSU_STQ_BANK_SIZE)-1: 0] &
                                ~w_vlsu_stq_freelist_full;

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
     .o_is_full  (w_vlsu_stq_freelist_full)
     );


  for (genvar stq_idx = 0; stq_idx < VLSU_STQ_SIZE; stq_idx++) begin : stq_loop

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
            w_vlsu_stq_entry_next.cmt_id       = vlsu_stq_req_if.cmt_id;
            w_vlsu_stq_entry_next.grp_id       = vlsu_stq_req_if.grp_id;
            w_vlsu_stq_entry_next.vs3_phy_idx  = vlsu_stq_req_if.vs3_phy_idx;
            w_vlsu_stq_entry_next.paddr        = to_vstq_paddr(vlsu_stq_req_if.paddr);
            w_vlsu_stq_entry_next.is_committed = 1'b0;

            w_state_next = WAIT_COMMIT;
          end
        end
        WAIT_COMMIT : begin
          if (w_commit_flush | w_br_flush) begin
            w_state_next = FINISH;
          end else if (w_ready_to_mv_stbuf) begin
            w_state_next = READ_VS3;
          end
        end
        READ_VS3 : begin
          w_state_next = COMMIT_MV_STBUF;
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
  bit_oh_or
    #(
      .T(vlsu_stq_entry_t),
      .WORDS(VLSU_STQ_SIZE)
      )
  bit_oh_entry
    (
     .i_oh      (w_vs3_regread_req_bank             ),
     .i_data    (r_vlsu_stq_entries       [bank_idx]),
     .o_selected(w_vlsu_stq_vs3_entry_bank[bank_idx])
     );
end endgenerate

bit_oh_or #(.T(vlsu_stq_entry_t), .WORDS(VLSU_STQ_BANK_SIZE)) bit_oh_vs3 (.i_oh(w_vs3_regread_req), .i_data(w_vlsu_stq_vs3_entry_bank), .o_selected(w_vlsu_stq_vs3_entry));
bit_encoder #(.WIDTH(VLSU_STQ_BANK_SIZE)) bit_oh_bank (.i_in(w_vs3_regread_req), .o_out(w_vlsu_stq_bank_idx));

assign vec_vs3_rd_if.valid = |w_vs3_regread_req;
assign vec_vs3_rd_if.rnid  = w_vlsu_stq_vs3_entry.vs3_phy_idx;

always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    st_buffer_if.valid <= 1'b0;
  end else begin
    st_buffer_if.valid <= vec_vs3_rd_if.valid;
    st_buffer_if.paddr <= to_paddr(w_vlsu_stq_bank_idx, w_vlsu_stq_vs3_entry.paddr);
    st_buffer_if.strb  <= {(riscv_vec_conf_pkg::DLEN_W/8){1'b1}};
    st_buffer_if.data  <= vec_vs3_rd_if.data;
  end
end


endmodule // scariv_vlsu_stq
