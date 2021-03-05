module msrh_stq_entry
  (
   input logic                                i_clk,
   input logic                                i_reset_n,

   input logic                                i_disp_load,
   input logic [msrh_pkg::CMT_BLK_W-1:0]      i_disp_cmt_id,
   input logic [msrh_pkg::DISP_SIZE-1:0]      i_disp_grp_id,
   input msrh_pkg::disp_t                     i_disp,

   // Updates from LSU Pipeline EX1 stage
   input logic                                i_ex1_q_valid,
   input msrh_lsu_pkg::ex1_q_update_t         i_ex1_q_updates,
   // Updates from LSU Pipeline EX2 stage
   input logic [msrh_pkg::LSU_INST_NUM-1: 0]  i_tlb_resolve,
   input logic                                i_ex2_q_valid,
   input msrh_lsu_pkg::ex2_q_update_t         i_ex2_q_updates,

   output logic                               o_stq_replay_valid,
   output msrh_lsu_pkg::stq_entry_t           o_entry,

   input logic                                i_rerun_accept,

   input logic [msrh_pkg::LSU_INST_NUM-1: 0]  i_ex3_done
   );

msrh_lsu_pkg::stq_entry_t r_entry;
assign o_entry = r_entry;

always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_entry.is_valid <= 1'b0;
    r_entry.state <= msrh_lsu_pkg::INIT;
  end else begin
    case (r_entry.state)
      msrh_lsu_pkg::INIT :
        if (i_disp_load) begin
          r_entry <= assign_stq_disp(i_disp, i_disp_cmt_id, i_disp_grp_id);
        end else if (i_ex1_q_valid) begin
          r_entry.state        <= i_ex1_q_updates.hazard_vld ? msrh_lsu_pkg::TLB_HAZ : msrh_lsu_pkg::EX2_RUN;
          r_entry.vaddr        <= i_ex1_q_updates.vaddr;
          r_entry.pipe_sel_idx <= i_ex1_q_updates.pipe_sel_idx;
          r_entry.inst         <= i_ex1_q_updates.inst;
        end
      msrh_lsu_pkg::TLB_HAZ : begin
        if (|i_tlb_resolve) begin
          r_entry.state <= msrh_lsu_pkg::EX2_RUN;
        end
      end
      msrh_lsu_pkg::EX2_RUN : begin
        if (i_ex2_q_valid) begin
          r_entry.state <= i_ex2_q_updates.hazard_typ == msrh_lsu_pkg::L1D_CONFLICT ? msrh_lsu_pkg::READY :
                           msrh_lsu_pkg::READY;  // Temporary
        end
      end
      msrh_lsu_pkg::READY : begin
        if (i_rerun_accept) begin
          r_entry.state <= msrh_lsu_pkg::EX2_RUN;
        end
      end
      default : begin
        $fatal ("This state sholudn't be reached.\n");
      end
    endcase // case (r_entry.state)
  end
end // always_ff @ (posedge i_clk, negedge i_reset_n)

function msrh_lsu_pkg::stq_entry_t assign_stq_disp (msrh_pkg::disp_t in,
                                      logic [msrh_pkg::CMT_BLK_W-1: 0] cmt_id,
                                      logic [msrh_pkg::DISP_SIZE-1: 0] grp_id);
  msrh_lsu_pkg::stq_entry_t ret;

  ret.is_valid  = 1'b1;
  ret.cmt_id    = cmt_id;
  ret.grp_id    = grp_id;
  ret.state     = msrh_lsu_pkg::INIT;
  ret.vaddr     = 'h0;

  return ret;
endfunction // assign_stq_disp

endmodule // msrh_stq_entry
