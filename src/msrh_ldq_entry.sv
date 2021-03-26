module msrh_ldq_entry
  import msrh_lsu_pkg::*;
(
 input logic                               i_clk,
 input logic                               i_reset_n,

 input logic                               i_disp_load,
 input logic [msrh_pkg::CMT_BLK_W-1:0]     i_disp_cmt_id,
 input logic [msrh_conf_pkg::DISP_SIZE-1:0]     i_disp_grp_id,
 input                                     msrh_pkg::disp_t i_disp,

 // Updates from LSU Pipeline EX1 stage
 input logic                               i_ex1_q_valid,
 input                                     msrh_lsu_pkg::ex1_q_update_t i_ex1_q_updates,
 // Updates from LSU Pipeline EX2 stage
 input logic [msrh_conf_pkg::LSU_INST_NUM-1: 0] i_tlb_resolve,
 input logic                               i_ex2_q_valid,
 input msrh_lsu_pkg::ex2_q_update_t        i_ex2_q_updates,

 output                                    msrh_lsu_pkg::ldq_entry_t o_entry,
 output logic [msrh_conf_pkg::LSU_INST_NUM-1: 0] o_ex2_ldq_entries_recv,

 input logic                               i_rerun_accept,

 input                                     msrh_lsu_pkg::lrq_resolve_t i_lrq_resolve,

 input logic [msrh_conf_pkg::LSU_INST_NUM-1: 0] i_ex3_done,
 input logic                               i_ldq_done
 );

msrh_lsu_pkg::ldq_entry_t r_entry;

logic                                          w_lrq_is_hazard;
logic                                          w_lrq_is_assigned;
logic                                          w_lrq_resolve_match;

logic [msrh_conf_pkg::LSU_INST_NUM-1: 0]            r_ex2_ldq_entries_recv;

assign o_entry = r_entry;
assign o_ex2_ldq_entries_recv = r_ex2_ldq_entries_recv;

assign w_lrq_is_hazard = i_ex2_q_updates.hazard_typ == msrh_lsu_pkg::LRQ_CONFLICT ||
                         i_ex2_q_updates.hazard_typ == msrh_lsu_pkg::LRQ_FULL;
assign w_lrq_is_assigned = i_ex2_q_updates.hazard_typ == msrh_lsu_pkg::LRQ_ASSIGNED;
assign w_lrq_resolve_match = i_ex2_q_updates.hazard_typ == msrh_lsu_pkg::LRQ_CONFLICT &
                             i_lrq_resolve.valid &
                             (i_lrq_resolve.resolve_index_oh == i_ex2_q_updates.lrq_index_oh);

always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_entry.is_valid <= 1'b0;
    r_entry.state <= LDQ_INIT;
    r_entry.lrq_haz_index_oh <= 'h0;
    r_ex2_ldq_entries_recv <= 'h0;
  end else begin
    case (r_entry.state)
      LDQ_INIT :
        if (i_disp_load) begin
          r_entry <= assign_ldq_disp(i_disp, i_disp_cmt_id, i_disp_grp_id);
        end else if (i_ex1_q_valid) begin
          r_entry.state           <= i_ex1_q_updates.hazard_vld ? LDQ_TLB_HAZ : LDQ_EX2_RUN;
          r_entry.vaddr           <= i_ex1_q_updates.vaddr;
          r_entry.pipe_sel_idx_oh <= i_ex1_q_updates.pipe_sel_idx_oh;
          r_entry.inst            <= i_ex1_q_updates.inst;

          for (int p_idx = 0; p_idx < msrh_conf_pkg::LSU_INST_NUM; p_idx++) begin : pipe_loop
            r_ex2_ldq_entries_recv[p_idx] <=  i_ex1_q_valid &
                                             !i_ex1_q_updates.hazard_vld &
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
          r_entry.state <= i_ex2_q_updates.hazard_typ == msrh_lsu_pkg::L1D_CONFLICT ? LDQ_READY :
                           w_lrq_resolve_match ? LDQ_READY :
                           w_lrq_is_hazard ? LDQ_LRQ_HAZ :
                           w_lrq_is_assigned ? LDQ_READY : // When LRQ Assigned, LRQ index return is zero so rerun and ge LRQ index.
                           LDQ_EX3_DONE;
          r_entry.lrq_haz_index_oh <= i_ex2_q_updates.lrq_index_oh;
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
      end
      LDQ_EX3_DONE : begin
        if (i_ldq_done) begin
          r_entry.is_valid <= 1'b0;
          r_entry.state <= LDQ_INIT;
        end
      end
      default : begin
        $fatal ("This state sholudn't be reached.\n");
      end
    endcase // case (r_entry.state)
  end
end


function msrh_lsu_pkg::ldq_entry_t assign_ldq_disp (msrh_pkg::disp_t in,
                                                    logic [msrh_pkg::CMT_BLK_W-1: 0] cmt_id,
                                                    logic [msrh_conf_pkg::DISP_SIZE-1: 0] grp_id);
  msrh_lsu_pkg::ldq_entry_t ret;

  ret.is_valid  = 1'b1;
  ret.cmt_id    = cmt_id;
  ret.grp_id    = grp_id;
  ret.state     = LDQ_INIT;
  ret.vaddr     = 'h0;

  return ret;
endfunction // assign_ldq_disp


endmodule // msrh_ldq_entry
