module msrh_stq_entry
  import msrh_lsu_pkg::*;
(
   input logic                                i_clk,
   input logic                                i_reset_n,

   input logic                                i_disp_load,
   input logic [msrh_pkg::CMT_ID_W-1:0]      i_disp_cmt_id,
   input logic [msrh_conf_pkg::DISP_SIZE-1:0] i_disp_grp_id,
   input msrh_pkg::disp_t                     i_disp,

   /* Forwarding path */
   input msrh_pkg::early_wr_t                 i_early_wr[msrh_pkg::REL_BUS_SIZE],

   // Updates from LSU Pipeline EX1 stage
   input logic                                i_ex1_q_valid,
   input ex1_q_update_t                       i_ex1_q_updates,
   // Updates from LSU Pipeline EX2 stage
   input logic [msrh_conf_pkg::LSU_INST_NUM-1: 0]  i_tlb_resolve,
   input logic                                i_ex2_q_valid,
   input ex2_q_update_t                       i_ex2_q_updates,

   output stq_entry_t                         o_entry,

   input logic                                i_rerun_accept,

   input logic                                i_stq_entry_done,
   // Commit notification
   input msrh_pkg::commit_blk_t               i_commit,
   input logic                                i_sq_op_accept,
   input logic                                i_sq_l1d_rd_miss,
   input logic                                i_sq_l1d_rd_conflict,
   input logic                                i_sq_lrq_full,
   input logic                                i_sq_lrq_conflict,
   input logic [msrh_pkg::LRQ_ENTRY_SIZE-1: 0] i_sq_lrq_index_oh,

   input lrq_resolve_t                        i_lrq_resolve,

   input logic                                i_sq_l1d_wr_conflict,

   input logic [msrh_conf_pkg::LSU_INST_NUM-1: 0]  i_ex3_done,
   output logic                                    o_entry_dead_done,
   output logic                                    o_stq_entry_st_finish
   );

stq_entry_t                          r_entry;
logic                                              w_entry_flush;
logic                                              w_dead_state_clear;
logic                                              w_cmt_id_match;

logic [msrh_pkg::RNID_W-1:0] w_rs2_rnid;
msrh_pkg::reg_t              w_rs2_type;
logic                        w_rs2_entry_hit;
logic                        w_rs2_may_mispred;
logic                        w_entry_rs2_ready_next;

assign o_entry = r_entry;

assign w_rs2_rnid = i_disp_load ? i_disp.rs2_rnid : r_entry.inst.rs2_rnid;
assign w_rs2_type = msrh_pkg::GPR;

select_early_wr_bus rs2_rel_select
(
 .i_entry_rnid (w_rs2_rnid),
 .i_entry_type (w_rs2_type),
 .i_early_wr   (i_early_wr),

 .o_valid      (w_rs2_entry_hit),
 .o_may_mispred(w_rs2_may_mispred)
 );

assign w_entry_flush = i_commit.commit &
                       i_commit.flush_valid &
                       !i_commit.all_dead &
                       r_entry.is_valid;
assign w_dead_state_clear = i_commit.commit &
                            i_commit.all_dead &
                            (i_commit.cmt_id == r_entry.cmt_id);

assign w_entry_rs2_ready_next = r_entry.inst.rs2_ready |
                                w_rs2_entry_hit |
                                i_ex1_q_valid & i_ex1_q_updates.inst.rs2_ready;

assign w_cmt_id_match = (i_commit.cmt_id == r_entry.cmt_id) &
                        ((i_commit.grp_id & r_entry.grp_id) != 'h0);

assign o_entry_dead_done     = (r_entry.state == STQ_DEAD) & w_dead_state_clear;
assign o_stq_entry_st_finish = (r_entry.state == STQ_L1D_UPDATE) & !i_sq_l1d_wr_conflict;

always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_entry.is_valid <= 1'b0;
    r_entry.state <= STQ_INIT;
  end else begin
    r_entry.inst.rs2_ready <= w_entry_rs2_ready_next;
    // if (w_entry_flush &
    //     !((r_entry.state == STQ_DONE ||
    //        r_entry.state == STQ_ ||
    //        r_entry.state == STQ_COMMIT ||
    //        r_entry.state == STQ_WAIT_LRQ_REFILL ||
    //        r_entry.state == STQ_COMMIT_L1D_CHECK ||
    //        r_entry.state == STQ_L1D_UPDATE))) begin
    //   r_entry.state    <= STQ_DEAD;
    //   r_entry.is_valid <= 1'b0;
    //   // prevent all updates from Pipeline
    //   // r_entry.cmt_id <= 'h0;
    //   // r_entry.grp_id <= 'h0;
    // end else begin
`ifdef SIMULATION
    if (i_disp_load && r_entry.state != STQ_INIT) begin
      $fatal(0, "When STQ is worked, it shouldn't come to i_disp_load");
    end
`endif // SIMULATION
    case (r_entry.state)
      STQ_INIT :
        if (w_entry_flush & r_entry.is_valid) begin
          r_entry.state <= STQ_DEAD;
          // r_entry.is_valid <= 1'b0;
          // r_entry.cmt_id <= 'h0;
          // r_entry.grp_id <= 'h0;
        end else if (i_disp_load) begin
          r_entry <= assign_stq_disp(i_disp, i_disp_cmt_id, i_disp_grp_id);
        end else if (r_entry.is_valid & i_ex1_q_valid) begin
          r_entry.state           <= i_ex1_q_updates.hazard_valid ? STQ_TLB_HAZ :
                                     !i_ex1_q_updates.st_data_valid ? STQ_WAIT_ST_DATA :
                                     STQ_DONE;
          r_entry.vaddr           <= i_ex1_q_updates.vaddr;
          r_entry.paddr           <= i_ex1_q_updates.paddr;
          r_entry.paddr_valid     <= ~i_ex1_q_updates.hazard_valid;
          r_entry.pipe_sel_idx_oh <= i_ex1_q_updates.pipe_sel_idx_oh;
          r_entry.inst            <= i_ex1_q_updates.inst;
          r_entry.size            <= i_ex1_q_updates.size;
          r_entry.inst.rs2_ready  <= w_entry_rs2_ready_next;

          r_entry.rs2_got_data    <= i_ex1_q_updates.st_data_valid;
          r_entry.rs2_data        <= i_ex1_q_updates.st_data;
        end
      STQ_TLB_HAZ : begin
        if (w_entry_flush) begin
          r_entry.state <= STQ_DEAD;
        end else if (|i_tlb_resolve) begin
          r_entry.state <= STQ_READY;
        end
      end
      STQ_DONE : begin
        if (w_entry_flush) begin
          r_entry.state <= STQ_DEAD;
        end else if (i_stq_entry_done) begin
          r_entry.state <= STQ_WAIT_COMMIT;
        end
      end
      STQ_WAIT_COMMIT : begin
        if (w_cmt_id_match) begin
          r_entry.state <= STQ_COMMIT;
        end
      end
      STQ_WAIT_ST_DATA : begin
        if (r_entry.inst.rs2_ready) begin
          r_entry.state <= STQ_READY;
        end
      end
      STQ_READY : begin
        if (i_rerun_accept) begin
          r_entry.state <= STQ_INIT;
        end
      end
      STQ_COMMIT : begin
        if (i_sq_op_accept) begin
          r_entry.state <= STQ_COMMIT_L1D_CHECK;
        end
      end
      STQ_COMMIT_L1D_CHECK : begin
        if (i_sq_l1d_rd_miss) begin
          r_entry.lrq_index_oh <= i_sq_lrq_index_oh;
`ifdef SIMULATION
          if (i_sq_lrq_conflict) begin
            if (!$onehot(i_sq_lrq_index_oh)) begin
              $fatal(0, "LRQ refill. i_sq_lrq_index_oh should be one hot.");
            end
          end else begin
            if (i_sq_lrq_index_oh != 'h0) begin
              $fatal(0, "LRQ request first request index_oh should be zero.");
            end
          end
`endif // SIMULATION
          r_entry.state <= STQ_WAIT_LRQ_REFILL;
        end else if (i_sq_l1d_rd_conflict) begin
          r_entry.state <= STQ_COMMIT; // Replay
        end else begin
          r_entry.state <= STQ_L1D_UPDATE;
        end
      end
      STQ_WAIT_LRQ_REFILL : begin
        if (r_entry.lrq_index_oh == 'h0) begin
          // if index_oh is zero, it means LRQ is correctly allocated,
          // so move to STQ_COMMIT and rerun, and set index_oh conflict bit set again.
          r_entry.state <= STQ_COMMIT; // Replay
        end else if (i_lrq_resolve.valid &&
                     i_lrq_resolve.resolve_index_oh == r_entry.lrq_index_oh) begin
          r_entry.state <= STQ_COMMIT; // Replay
        end
      end
      STQ_L1D_UPDATE : begin
        if (i_sq_l1d_wr_conflict) begin
          r_entry.state <= STQ_COMMIT; // Replay
        end else begin
          r_entry.is_valid <= 1'b0;
          r_entry.state <= STQ_INIT;
        end
      end
      STQ_DEAD : begin
        if (w_dead_state_clear) begin
          r_entry.state    <= STQ_INIT;
          r_entry.is_valid <= 1'b0;
          // prevent all updates from Pipeline
          r_entry.cmt_id <= 'h0;
          r_entry.grp_id <= 'h0;
        end
      end // case: msrh_pkg::DEAD
      default : begin
        $fatal (0, "This state sholudn't be reached.\n");
      end
    endcase // case (r_entry.state)
  end // else: !if(!i_reset_n)
end // always_ff @ (posedge i_clk, negedge i_reset_n)

function stq_entry_t assign_stq_disp (msrh_pkg::disp_t in,
                                                    logic [msrh_pkg::CMT_ID_W-1: 0] cmt_id,
                                                    logic [msrh_conf_pkg::DISP_SIZE-1: 0] grp_id);
  stq_entry_t ret;

  ret.is_valid  = 1'b1;

  ret.inst.rs2_valid = in.rs2_valid;
  ret.inst.rs2_rnid  = in.rs2_rnid;
  ret.inst.rs2_ready = in.rs2_ready;

  ret.rs2_got_data = in.rs2_ready;

  ret.cmt_id    = cmt_id;
  ret.grp_id    = grp_id;
  ret.state     = STQ_INIT;
  ret.vaddr     = 'h0;
  ret.paddr_valid = 1'b0;

  return ret;
endfunction // assign_stq_disp

endmodule // msrh_stq_entry
