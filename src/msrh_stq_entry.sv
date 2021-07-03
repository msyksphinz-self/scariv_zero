module msrh_stq_entry
  import msrh_lsu_pkg::*;
(
   input logic                                i_clk,
   input logic                                i_reset_n,

   input logic                                i_disp_load,
   input logic [msrh_pkg::CMT_ID_W-1:0]       i_disp_cmt_id,
   input logic [msrh_conf_pkg::DISP_SIZE-1:0] i_disp_grp_id,
   input msrh_pkg::disp_t                     i_disp,
   input logic [msrh_conf_pkg::LSU_INST_NUM-1: 0] i_disp_pipe_sel_oh,

   /* Forwarding path */
   input msrh_pkg::early_wr_t                 i_early_wr[msrh_pkg::REL_BUS_SIZE],
   input msrh_pkg::phy_wr_t                   i_phy_wr [msrh_pkg::TGT_BUS_SIZE],
   input msrh_pkg::mispred_t                  i_mispred_lsu[msrh_conf_pkg::LSU_INST_NUM],

   // Updates from LSU Pipeline EX1 stage
   input logic                                i_ex1_q_valid,
   input ex1_q_update_t                       i_ex1_q_updates,
   // Updates from LSU Pipeline EX2 stage
   input logic [msrh_conf_pkg::LSU_INST_NUM-1: 0]  i_tlb_resolve,
   input logic                                i_ex2_q_valid,
   input ex2_q_update_t                       i_ex2_q_updates,

   output stq_entry_t                         o_entry,
   output logic                               o_entry_ready,

   input logic                                i_entry_picked,

   // input logic                                i_stq_entry_done,
   // Commit notification
   input msrh_pkg::commit_blk_t               i_commit,
   br_upd_if.slave                            br_upd_if,

   input logic                                i_sq_op_accept,
   input logic                                i_sq_l1d_rd_miss,
   input logic                                i_sq_l1d_rd_conflict,
   input logic                                i_sq_lrq_full,
   input logic                                i_sq_lrq_conflict,
   input logic [msrh_pkg::LRQ_ENTRY_SIZE-1: 0] i_sq_lrq_index_oh,

   input lrq_resolve_t                        i_lrq_resolve,

   input logic                                i_sq_l1d_wr_conflict,

   // Snoop Interface
   stq_snoop_if.slave                         stq_snoop_if,


   input logic [msrh_conf_pkg::LSU_INST_NUM-1: 0]  i_ex3_done,
   input logic                                     i_stq_outptr_valid,
   output logic                                    o_stq_entry_st_finish
   );

stq_entry_t                          r_entry;
stq_entry_t                          w_entry_next;
logic                                              w_entry_flush;
logic                                              w_commit_flush;
logic                                              w_br_flush;
logic                                              w_load_br_flush;
logic                                              w_dead_state_clear;
logic                                              w_cmt_id_match;

logic [msrh_pkg::RNID_W-1:0]                     w_rs1_rnid;
logic [msrh_pkg::RNID_W-1:0]                     w_rs2_rnid;
msrh_pkg::reg_t                                  w_rs1_type;
msrh_pkg::reg_t                                  w_rs2_type;
logic                                            w_rs1_rel_hit;
logic                                            w_rs1_phy_hit;
logic                                            w_rs1_may_mispred;
logic                                            w_rs1_mispredicted;
logic                                            w_rs2_phy_hit;
logic [riscv_pkg::XLEN_W-1: 0]                   w_rs2_phy_data;
logic                                            w_entry_rs2_ready_next;

assign o_entry = r_entry;

assign w_rs1_rnid = i_disp_load ? i_disp.rs1_rnid : r_entry.inst.rs1_rnid;
assign w_rs2_rnid = i_disp_load ? i_disp.rs2_rnid : r_entry.inst.rs2_rnid;

assign w_rs1_type = i_disp_load ? i_disp.rs1_type : r_entry.inst.rs1_type;
assign w_rs2_type = i_disp_load ? i_disp.rs2_type : r_entry.inst.rs2_type;

select_early_wr_bus rs1_rel_select
(
 .i_entry_rnid (w_rs1_rnid),
 .i_entry_type (w_rs1_type),
 .i_early_wr   (i_early_wr),

 .o_valid      (w_rs1_rel_hit),
 .o_may_mispred(w_rs1_may_mispred)
 );


select_phy_wr_bus rs1_phy_select
(
 .i_entry_rnid (w_rs1_rnid),
 .i_entry_type (w_rs1_type),
 .i_phy_wr     (i_phy_wr),

 .o_valid      (w_rs1_phy_hit)
 );


select_mispred_bus rs1_mispred_select
(
 .i_entry_rnid (w_rs1_rnid),
 .i_entry_type (w_rs1_type),
 .i_mispred    (i_mispred_lsu),

 .o_mispred    (w_rs1_mispredicted)
 );


select_phy_wr_data rs2_phy_select
(
 .i_entry_rnid (w_rs2_rnid),
 .i_entry_type (w_rs2_type),
 .i_phy_wr     (i_phy_wr),

 .o_valid      (w_rs2_phy_hit),
 .o_data       (w_rs2_phy_data)
 );



assign w_commit_flush = msrh_pkg::is_commit_flush_target(r_entry.cmt_id, r_entry.grp_id, i_commit) & r_entry.is_valid;
assign w_br_flush     = msrh_pkg::is_br_flush_target(r_entry.br_mask, br_upd_if.brtag) & br_upd_if.update & ~br_upd_if.dead & br_upd_if.mispredict & r_entry.is_valid;
assign w_entry_flush  = w_commit_flush | w_br_flush;

assign w_load_br_flush = msrh_pkg::is_br_flush_target(i_disp.br_mask, br_upd_if.brtag) & br_upd_if.update & ~br_upd_if.dead & br_upd_if.mispredict;

assign w_dead_state_clear = i_commit.commit &
                            (i_commit.cmt_id == r_entry.cmt_id);

assign w_entry_rs2_ready_next = r_entry.inst.rs2_ready |
                                w_rs2_phy_hit |
                                i_ex1_q_valid & i_ex1_q_updates.st_data_valid;

assign w_cmt_id_match = i_commit.commit &
                        (i_commit.cmt_id == r_entry.cmt_id) &
                        ((|i_commit.except_valid) ? ((i_commit.dead_id & r_entry.grp_id) == 0) : 1'b1);

assign o_stq_entry_st_finish = (r_entry.state == STQ_L1D_UPDATE) & !i_sq_l1d_wr_conflict |
                               (r_entry.state == STQ_DEAD) & i_stq_outptr_valid;

always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_entry.is_valid <= 1'b0;
    r_entry.state <= STQ_INIT;
  end else begin
    r_entry <= w_entry_next;

`ifdef SIMULATION
    if (i_disp_load && r_entry.state != STQ_INIT) begin
      $fatal(0, "When STQ is worked, it shouldn't come to i_disp_load");
    end
`endif // SIMULATION
  end
end

assign o_entry_ready = (r_entry.state == STQ_ISSUE_WAIT) & !w_entry_flush &
                       all_operand_ready(r_entry);

always_comb begin
  w_entry_next = r_entry;

  w_entry_next.inst.rs2_ready = w_entry_rs2_ready_next | r_entry.inst.rs2_ready;
  w_entry_next.rs2_data = w_rs2_phy_hit ? w_rs2_phy_data :
                          i_ex1_q_valid & i_ex1_q_updates.st_data_valid ? i_ex1_q_updates.st_data :
                          r_entry.rs2_data;
  w_entry_next.inst.rs1_ready = r_entry.inst.rs1_ready | (w_rs1_rel_hit & ~w_rs1_may_mispred) | w_rs1_phy_hit;
  w_entry_next.inst.rs1_pred_ready = w_rs1_rel_hit & w_rs1_may_mispred;

  case (r_entry.state)
    STQ_INIT :
      if (w_entry_flush & w_entry_next.is_valid) begin
        w_entry_next.state = STQ_DEAD;
        // w_entry_next.is_valid = 1'b0;
        // w_entry_next.cmt_id = 'h0;
        // w_entry_next.grp_id = 'h0;
      end else if (i_disp_load) begin
        w_entry_next = assign_stq_disp(i_disp, i_disp_cmt_id, i_disp_grp_id, i_disp_pipe_sel_oh);
        w_entry_next.inst = msrh_pkg::assign_issue_t(i_disp, i_disp_cmt_id, i_disp_grp_id,
                                                     w_rs1_rel_hit, 1'b0,
                                                     w_rs1_phy_hit, w_rs2_phy_hit,
                                                     w_rs1_may_mispred, 1'b0);
        if (w_load_br_flush) begin
          w_entry_next.state    = LDQ_DEAD;
        end
      end
    STQ_ISSUE_WAIT : begin
      if (w_entry_flush) begin
        w_entry_next.state = STQ_DEAD;
      end else if (o_entry_ready & i_entry_picked) begin
        w_entry_next.state = STQ_ISSUED;
      end
    end
    STQ_ISSUED : begin
      if (w_entry_flush) begin
        w_entry_next.state = STQ_DEAD;
      end else if (w_entry_next.is_valid & i_ex1_q_valid) begin
        w_entry_next.state           = i_ex1_q_updates.hazard_valid ? STQ_TLB_HAZ :
                                       !w_entry_rs2_ready_next ? STQ_WAIT_ST_DATA :
                                       STQ_DONE_EX2;
        w_entry_next.except_valid    = i_ex1_q_updates.tlb_except_valid;
        w_entry_next.except_type     = i_ex1_q_updates.tlb_except_type;
        w_entry_next.vaddr           = i_ex1_q_updates.vaddr;
        w_entry_next.paddr           = i_ex1_q_updates.paddr;
        w_entry_next.paddr_valid     = ~i_ex1_q_updates.hazard_valid;
        // w_entry_next.pipe_sel_idx_oh = i_ex1_q_updates.pipe_sel_idx_oh;
        // w_entry_next.inst            = i_ex1_q_updates.inst;
        w_entry_next.size            = i_ex1_q_updates.size;

      end // if (w_entry_next.is_valid & i_ex1_q_valid)
      if (r_entry.inst.rs1_pred_ready & w_rs1_mispredicted) begin
        w_entry_next.state = STQ_ISSUE_WAIT;
        w_entry_next.inst.rs1_pred_ready = 1'b0;
        w_entry_next.inst.rs2_pred_ready = 1'b0;
      end
    end // case: STQ_ISSUED
    STQ_TLB_HAZ : begin
      if (w_entry_flush) begin
        w_entry_next.state = STQ_DEAD;
      end else if (|i_tlb_resolve) begin
        w_entry_next.state = STQ_ISSUE_WAIT;
      end
    end
    STQ_DONE_EX2 : begin
      if (w_entry_flush) begin
        w_entry_next.state = STQ_DEAD;
      end else begin
        w_entry_next.state = STQ_DONE_EX3;
      end
    end
    STQ_DONE_EX3 : begin
      // Ex2 --> Ex3 needs due to adjust Load Pipeline with Done Port
      if (w_entry_flush) begin
        w_entry_next.state = STQ_DEAD;
      end else begin
        w_entry_next.state = STQ_WAIT_COMMIT;
      end
    end
    STQ_WAIT_COMMIT : begin
      if (w_entry_flush) begin
        w_entry_next.state = STQ_DEAD;
      end else if (w_cmt_id_match) begin
        w_entry_next.state = STQ_COMMIT;
      end
      // w_entry_next.is_valid = 1'b1;
      // prevent all updates from Pipeline
      // w_entry_next.cmt_id = 'h0;
      // w_entry_next.grp_id = 'h0;
      // end
    end
    STQ_WAIT_ST_DATA : begin
      if (w_entry_flush) begin
        w_entry_next.state = STQ_DEAD;
      end else if (w_entry_next.inst.rs2_ready) begin
        w_entry_next.state = STQ_ISSUE_WAIT;
      end
    end
    STQ_COMMIT : begin
      if (i_sq_op_accept) begin
        w_entry_next.state = STQ_COMMIT_L1D_CHECK;
      end
    end
    STQ_COMMIT_L1D_CHECK : begin
      if (i_sq_l1d_rd_miss) begin
        w_entry_next.lrq_index_oh = i_sq_lrq_index_oh;
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
        w_entry_next.state = STQ_WAIT_LRQ_REFILL;
      end else if (i_sq_l1d_rd_conflict) begin
        w_entry_next.state = STQ_COMMIT; // Replay
      end else begin
        w_entry_next.state = STQ_L1D_UPDATE;
      end
    end
    STQ_WAIT_LRQ_REFILL : begin
      if (w_entry_next.lrq_index_oh == 'h0) begin
        // if index_oh is zero, it means LRQ is correctly allocated,
        // so move to STQ_COMMIT and rerun, and set index_oh conflict bit set again.
        w_entry_next.state = STQ_COMMIT; // Replay
      end else if (i_lrq_resolve.valid &&
                   i_lrq_resolve.resolve_index_oh == r_entry.lrq_index_oh) begin
        w_entry_next.state = STQ_COMMIT; // Replay
      end
    end
    STQ_L1D_UPDATE : begin
      if (i_sq_l1d_wr_conflict) begin
        w_entry_next.state = STQ_COMMIT; // Replay
      end else begin
        w_entry_next.is_valid = 1'b0;
        w_entry_next.state = STQ_INIT;
      end
    end
    STQ_DEAD : begin
      if (/* w_dead_state_clear*/ i_stq_outptr_valid) begin
        w_entry_next.state    = STQ_INIT;
        w_entry_next.is_valid = 1'b0;
        // prevent all updates from Pipeline
        w_entry_next.cmt_id = 'h0;
        w_entry_next.grp_id = 'h0;
      end
    end // case: msrh_pkg::DEAD
    default : begin
      $fatal (0, "This state sholudn't be reached.\n");
    end
  endcase // case (w_entry_next.state)

end // always_comb


// Snoop Interface Hit
/* verilator lint_off WIDTH */
logic [$clog2(msrh_lsu_pkg::DCACHE_DATA_B_W)-1: 0] w_entry_snp_addr_diff;
assign w_entry_snp_addr_diff = r_entry.paddr - {stq_snoop_if.req_s0_paddr[riscv_pkg::PADDR_W-1:$clog2(msrh_lsu_pkg::DCACHE_DATA_B_W)], {$clog2(msrh_lsu_pkg::DCACHE_DATA_B_W){1'b0}}};
logic                                              w_snoop_s0_hit;
assign w_snoop_s0_hit = r_entry.paddr_valid &
                        ((r_entry.state == STQ_COMMIT) |
                         (r_entry.state == STQ_COMMIT_L1D_CHECK) |
                         (r_entry.state == STQ_WAIT_LRQ_REFILL) |
                         (r_entry.state == STQ_L1D_UPDATE)) &
                        (stq_snoop_if.req_s0_paddr[riscv_pkg::PADDR_W-1:$clog2(msrh_lsu_pkg::DCACHE_DATA_B_W)] ==
                         r_entry.paddr[riscv_pkg::PADDR_W-1:$clog2(msrh_lsu_pkg::DCACHE_DATA_B_W)]);

always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    stq_snoop_if.resp_s1_valid <= 1'b0;
  end else begin
    stq_snoop_if.resp_s1_valid <= stq_snoop_if.req_s0_valid;
    stq_snoop_if.resp_s1_be   <= w_snoop_s0_hit ? gen_dw_cacheline(r_entry.size, w_entry_snp_addr_diff) : 'h0;
    stq_snoop_if.resp_s1_data <= w_snoop_s0_hit ? {{(msrh_conf_pkg::DCACHE_DATA_W-riscv_pkg::XLEN_W){1'b0}}, r_entry.rs2_data} << {w_entry_snp_addr_diff, 3'b000} : 'h0;
  end // else: !if(!i_reset_n)
end // always_ff @ (posedge i_clk, negedge i_reset_n)


function stq_entry_t assign_stq_disp (msrh_pkg::disp_t in,
                                      logic [msrh_pkg::CMT_ID_W-1: 0] cmt_id,
                                      logic [msrh_conf_pkg::DISP_SIZE-1: 0] grp_id,
                                      logic [msrh_conf_pkg::LSU_INST_NUM-1: 0] pipe_sel_oh);
  stq_entry_t ret;

  ret.is_valid  = 1'b1;

  ret.cmt_id    = cmt_id;
  ret.grp_id    = grp_id;

  ret.brtag   = in.brtag;
  ret.br_mask = in.br_mask;

  ret.state     = STQ_ISSUE_WAIT;
  ret.pipe_sel_idx_oh = pipe_sel_oh;
  ret.vaddr     = 'h0;
  ret.paddr_valid = 1'b0;

  ret.except_valid = 1'b0;

  return ret;
endfunction // assign_stq_disp


function logic all_operand_ready(stq_entry_t entry);
  logic     ret;
  ret = (!entry.inst.rs1_valid | entry.inst.rs1_valid  & (entry.inst.rs1_ready | entry.inst.rs1_pred_ready));
  return ret;
endfunction // all_operand_ready

endmodule // msrh_stq_entry
