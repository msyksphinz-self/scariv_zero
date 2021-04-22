module msrh_ldq_entry
  import msrh_lsu_pkg::*;
(
 input logic                                     i_clk,
 input logic                                     i_reset_n,

 input logic                                     i_disp_load,
 input logic [msrh_pkg::CMT_ID_W-1:0]           i_disp_cmt_id,
 input logic [msrh_conf_pkg::DISP_SIZE-1:0]      i_disp_grp_id,
 input                                           msrh_pkg::disp_t i_disp,

 // Updates from LSU Pipeline EX1 stage
 input logic                                     i_ex1_q_valid,
 input                                           ex1_q_update_t i_ex1_q_updates,
 // Updates from LSU Pipeline EX2 stage
 input logic [msrh_conf_pkg::LSU_INST_NUM-1: 0]  i_tlb_resolve,
 input logic                                     i_ex2_q_valid,
 input                                           ex2_q_update_t i_ex2_q_updates,
 input                                           ex2_addr_check_t i_ex2_addr_check[msrh_conf_pkg::LSU_INST_NUM],

 output                                          ldq_entry_t o_entry,
 output logic [msrh_conf_pkg::LSU_INST_NUM-1: 0] o_ex2_ldq_entries_recv,

 input logic                                     i_rerun_accept,

 input lrq_resolve_t                             i_lrq_resolve,
 input stq_resolve_t                             i_stq_resolve,
 // Commit notification
 input                                           msrh_pkg::commit_blk_t i_commit,

 output logic                                    o_entry_dead_done,

 input logic [msrh_conf_pkg::LSU_INST_NUM-1: 0]  i_ex3_done,
 input logic                                     i_ldq_done
 );

ldq_entry_t                                      r_entry;
logic                                            w_entry_flush;
logic                                            w_dead_state_clear;

logic                                            w_lrq_is_hazard;
logic                                            w_lrq_is_assigned;
logic                                            w_lrq_resolve_match;
logic                                            w_stq_is_hazard;
logic [msrh_conf_pkg::STQ_SIZE-1: 0]             stq_haz_idx_next;

logic [msrh_conf_pkg::LSU_INST_NUM-1: 0]         r_ex2_ldq_entries_recv;

logic                                            w_addr_conflict;

assign o_entry = r_entry;
assign o_ex2_ldq_entries_recv = r_ex2_ldq_entries_recv;

assign w_entry_flush = i_commit.commit &
                       i_commit.flush_valid &
                       !i_commit.all_dead &
                       r_entry.is_valid;
assign w_dead_state_clear = i_commit.commit &
                            i_commit.all_dead &
                            (i_commit.cmt_id == r_entry.cmt_id);

assign w_lrq_is_hazard = i_ex2_q_updates.hazard_typ == LRQ_CONFLICT ||
                         i_ex2_q_updates.hazard_typ == LRQ_FULL;
assign w_stq_is_hazard = i_ex2_q_updates.hazard_typ == STQ_DEPEND;
assign w_lrq_is_assigned = i_ex2_q_updates.hazard_typ == LRQ_ASSIGNED;
assign w_lrq_resolve_match = i_ex2_q_updates.hazard_typ == LRQ_CONFLICT &
                             i_lrq_resolve.valid &
                             (i_lrq_resolve.resolve_index_oh == i_ex2_q_updates.lrq_index_oh);

assign o_entry_dead_done = (r_entry.state == LDQ_DEAD) & w_dead_state_clear;

msrh_addr_check
  u_addr_check
    (
     .i_entry_cmt_id   (r_entry.cmt_id  ),
     .i_entry_grp_id   (r_entry.grp_id  ),
     .i_entry_paddr    (r_entry.paddr   ),
     .i_entry_size     (r_entry.size    ),
     .i_ex2_addr_check (i_ex2_addr_check),
     .o_addr_conflict  (w_addr_conflict )
     );

assign stq_haz_idx_next = i_stq_resolve.valid ? r_entry.stq_haz_idx & ~i_stq_resolve.resolve_index_oh :
                          r_entry.stq_haz_idx;

always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_entry.is_valid <= 1'b0;
    r_entry.state <= LDQ_INIT;
    r_entry.lrq_haz_index_oh <= 'h0;
    r_ex2_ldq_entries_recv <= 'h0;
  end else begin
    if (w_entry_flush) begin
      if ((i_commit.cmt_id == r_entry.cmt_id) &&
          (r_entry.state == LDQ_EX3_DONE)) begin
        r_entry.state <= LDQ_INIT;
        r_entry.is_valid <= 1'b0;
        // prevent all updates from Pipeline
        r_entry.cmt_id <= 'h0;
        r_entry.grp_id <= 'h0;
      end else begin
        r_entry.state <= LDQ_DEAD;
      end
    end else begin
      case (r_entry.state)
        LDQ_INIT :
          if (i_disp_load) begin
            r_entry <= assign_ldq_disp(i_disp, i_disp_cmt_id, i_disp_grp_id);
          end else if (r_entry.is_valid & i_ex1_q_valid) begin
            r_entry.state           <= i_ex1_q_updates.hazard_valid ? LDQ_TLB_HAZ : LDQ_EX2_RUN;
            r_entry.vaddr           <= i_ex1_q_updates.vaddr;
            r_entry.paddr           <= i_ex1_q_updates.paddr;
            r_entry.pipe_sel_idx_oh <= i_ex1_q_updates.pipe_sel_idx_oh;
            r_entry.inst            <= i_ex1_q_updates.inst;
            r_entry.size            <= i_ex1_q_updates.size;

            for (int p_idx = 0; p_idx < msrh_conf_pkg::LSU_INST_NUM; p_idx++) begin : pipe_loop
              r_ex2_ldq_entries_recv[p_idx] <=  i_ex1_q_valid &
                             !i_ex1_q_updates.hazard_valid &
                             i_ex1_q_updates.pipe_sel_idx_oh[p_idx];
            end
          end // if (i_ex1_q_valid)
        LDQ_TLB_HAZ : begin
          if (|i_tlb_resolve) begin
            r_entry.state <= LDQ_READY;
          end
        end
        LDQ_EX2_RUN : begin
          if (i_ex2_q_valid) begin
            r_entry.state <= i_ex2_q_updates.hazard_typ == L1D_CONFLICT ? LDQ_READY :
                             w_lrq_resolve_match ? LDQ_READY :
                             w_lrq_is_hazard ? LDQ_LRQ_HAZ :
                             w_stq_is_hazard ? LDQ_STQ_HAZ :
                             w_lrq_is_assigned ? LDQ_READY : // When LRQ Assigned, LRQ index return is zero so rerun and ge LRQ index.
                             LDQ_CHECK_ST_DEPEND;  // LDQ_EX3_DONE;
            r_entry.lrq_haz_index_oh <= i_ex2_q_updates.lrq_index_oh;
            r_entry.stq_haz_idx      <= i_ex2_q_updates.stq_haz_idx;
`ifdef SIMULATION
            if (!i_reset_n) begin
            end else begin
              if (w_lrq_is_assigned & i_ex2_q_updates.lrq_index_oh != 0) begin
                $fatal (0, "When LRQ is assigned, LRQ index ID must be zero\n");
              end
              if (w_lrq_is_hazard & !$onehot0(i_ex2_q_updates.lrq_index_oh)) begin
                $fatal (0, "lrq_index_oh must be one hot but actually %x\n", i_ex2_q_updates.lrq_index_oh);
              end
            end
`endif // SIMULATION
            r_ex2_ldq_entries_recv     <= 'h0;
          end
        end
        LDQ_LRQ_HAZ : begin
          if (i_lrq_resolve.valid && i_lrq_resolve.resolve_index_oh == r_entry.lrq_haz_index_oh) begin
            r_entry.state <= LDQ_READY;
          end
        end
        LDQ_READY : begin
          if (i_rerun_accept) begin
            r_entry.state <= LDQ_INIT;
          end
        end
        LDQ_STQ_HAZ : begin
          r_entry.stq_haz_idx <= stq_haz_idx_next;
          if (stq_haz_idx_next == 'h0) begin
            r_entry.state <= LDQ_READY;
          end
        end
        LDQ_EX3_DONE : begin
          if (i_ldq_done) begin
            r_entry.is_valid <= 1'b0;
            r_entry.state <= LDQ_INIT;
          end
        end
        LDQ_DEAD : begin
          if (w_dead_state_clear) begin
            r_entry.state <= LDQ_INIT;
            r_entry.is_valid <= 1'b0;
            // prevent all updates from Pipeline
            r_entry.cmt_id <= 'h0;
            r_entry.grp_id <= 'h0;
          end
        end // case: msrh_pkg::DEAD
        LDQ_CHECK_ST_DEPEND: begin
          // Younger Store Instruction, address conflict
          if (w_addr_conflict) begin
            r_entry.state <= LDQ_READY;
          end
          // When entry become oldest uncommitted
          if (i_commit.cmt_id == r_entry.cmt_id &&
              (i_commit.grp_id & (r_entry.grp_id-1)) == r_entry.grp_id-1) begin
            r_entry.state <= LDQ_EX3_DONE;
          end
        end
        default : begin
          $fatal ("This state sholudn't be reached.\n");
        end
      endcase // case (r_entry.state)
    end // else: !if(i_commit.commit &...
  end // else: !if(!i_reset_n)
end // always_ff @ (posedge i_clk, negedge i_reset_n)



function ldq_entry_t assign_ldq_disp (msrh_pkg::disp_t in,
                                      logic [msrh_pkg::CMT_ID_W-1: 0] cmt_id,
                                      logic [msrh_conf_pkg::DISP_SIZE-1: 0] grp_id);
  ldq_entry_t ret;

  ret.is_valid  = 1'b1;
  ret.cmt_id    = cmt_id;
  ret.grp_id    = grp_id;
  ret.state     = LDQ_INIT;
  ret.vaddr     = 'h0;

  return ret;
endfunction // assign_ldq_disp


endmodule // msrh_ldq_entry
