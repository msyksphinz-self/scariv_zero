module scariv_stq_entry
  import scariv_lsu_pkg::*;
#(parameter entry_index = 0)
(
   input logic                                i_clk,
   input logic                                i_reset_n,

   // ROB notification interface
   rob_info_if.slave                           rob_info_if,

   input logic                                i_disp_load,
   input scariv_pkg::cmt_id_t                   i_disp_cmt_id,
   input scariv_pkg::grp_id_t                   i_disp_grp_id,
   input scariv_pkg::disp_t                     i_disp,
   input logic [scariv_conf_pkg::LSU_INST_NUM-1: 0] i_disp_pipe_sel_oh,

   /* Forwarding path */
   input scariv_pkg::early_wr_t                 i_early_wr[scariv_pkg::REL_BUS_SIZE],
   input scariv_pkg::phy_wr_t                   i_phy_wr [scariv_pkg::TGT_BUS_SIZE],
   input scariv_pkg::mispred_t                  i_mispred_lsu[scariv_conf_pkg::LSU_INST_NUM],

   // Updates from LSU Pipeline EX1 stage
   input logic                                i_ex1_q_valid,
   input ex1_q_update_t                       i_ex1_q_updates,
   // Updates from LSU Pipeline EX2 stage
   input logic [scariv_conf_pkg::LSU_INST_NUM-1: 0]  i_tlb_resolve,
   input logic                                i_ex2_q_valid,
   input ex2_q_update_t                       i_ex2_q_updates,

   output stq_entry_t                         o_entry,
   output logic                               o_entry_ready,

   input logic                                i_entry_picked,

   // input logic                                i_stq_entry_done,
   // Commit notification
   input scariv_pkg::commit_blk_t               i_commit,
   br_upd_if.slave                            br_upd_if,

   input missu_resolve_t                      i_missu_resolve,
   input logic                                i_missu_is_full,
   input logic                                i_missu_is_empty,

   output logic                               o_stbuf_req_valid,
   input logic                                i_stbuf_accept,

   input logic                                i_st_buffer_empty,

   output logic                               o_uc_write_req_valid,
   input logic                                i_uc_write_accept,

   // // Snoop Interface
   // stq_snoop_if.slave                         stq_snoop_if,

   done_if.slave    ex3_done_if,
   input logic                                     i_stq_outptr_valid,
   output logic                                    o_stq_entry_st_finish
   );

stq_entry_t                          r_entry;
/* verilator lint_off UNOPTFLAT */
stq_entry_t                          w_entry_next;
logic                                              w_entry_flush;
logic                                              w_commit_flush;
logic                                              w_br_flush;
logic                                              w_load_br_flush;
logic                                              w_dead_state_clear;
logic                                              w_ready_to_mv_stbuf;

scariv_pkg::rnid_t                                   w_rs_rnid[2];
scariv_pkg::reg_t                                    w_rs_type[2];
logic [ 1: 0]                                      w_rs_rel_hit;
logic [ 1: 0]                                      w_rs_phy_hit;
logic [ 1: 0]                                      w_rs_may_mispred;
logic [ 1: 0]                                      w_rs_mispredicted;
scariv_pkg::alen_t                                   w_rs2_phy_data;
logic                                              w_entry_rs2_ready_next;

logic                                              w_commit_finish;

logic                                              w_oldest_ready;

logic                                              w_missu_is_conflict;
logic                                              w_missu_is_full;
logic                                              w_missu_is_assigned;
logic                                              w_missu_resolve_match;
logic                                              w_missu_evict_is_hazard;

always_comb begin
  o_entry = r_entry;
  // When EX3, fast forwarding to another flush
  if (r_entry.state == STQ_DONE_EX3) begin
    o_entry.another_flush_valid  = ex3_done_if.payload.another_flush_valid;
    o_entry.another_flush_cmt_id = ex3_done_if.payload.another_flush_cmt_id;
    o_entry.another_flush_grp_id = ex3_done_if.payload.another_flush_grp_id;
  end
end

assign w_rs_rnid[0] = i_disp_load ? i_disp.rd_regs[0].rnid : r_entry.inst.rd_regs[0].rnid;
assign w_rs_rnid[1] = i_disp_load ? i_disp.rd_regs[1].rnid : r_entry.inst.rd_regs[1].rnid;

assign w_rs_type[0] = i_disp_load ? i_disp.rd_regs[0].typ : r_entry.inst.rd_regs[0].typ;
assign w_rs_type[1] = i_disp_load ? i_disp.rd_regs[1].typ : r_entry.inst.rd_regs[1].typ;

select_early_wr_bus rs1_rel_select    (.i_entry_rnid (w_rs_rnid[0]), .i_entry_type (w_rs_type[0]), .i_early_wr (i_early_wr),
                                       .o_valid   (w_rs_rel_hit[0]), .o_may_mispred (w_rs_may_mispred[0]));
select_phy_wr_bus   rs1_phy_select    (.i_entry_rnid (w_rs_rnid[0]), .i_entry_type (w_rs_type[0]), .i_phy_wr   (i_phy_wr),
                                       .o_valid   (w_rs_phy_hit[0]));
select_mispred_bus  rs1_mispred_select(.i_entry_rnid (w_rs_rnid[0]), .i_entry_type (w_rs_type[0]), .i_mispred  (i_mispred_lsu),
                                       .o_mispred (w_rs_mispredicted[0]));
select_mispred_bus  rs2_mispred_select(.i_entry_rnid (w_rs_rnid[1]), .i_entry_type (w_rs_type[1]), .i_mispred  (i_mispred_lsu),
                                       .o_mispred (w_rs_mispredicted[1]));
assign w_rs_rel_hit[1] = 1'b0;
select_phy_wr_data rs2_phy_select (.i_entry_rnid (w_rs_rnid[1]), .i_entry_type (w_rs_type[1]), .i_phy_wr (i_phy_wr),
                                   .o_valid (w_rs_phy_hit[1]), .o_data (w_rs2_phy_data));



assign w_commit_flush = scariv_pkg::is_commit_flush_target(r_entry.cmt_id, r_entry.grp_id, i_commit) & r_entry.is_valid;
assign w_br_flush     = scariv_pkg::is_br_flush_target(r_entry.br_mask, br_upd_if.brtag,
                                                     br_upd_if.dead, br_upd_if.mispredict) & br_upd_if.update & r_entry.is_valid;
assign w_entry_flush  = w_commit_flush | w_br_flush;

assign w_load_br_flush = scariv_pkg::is_br_flush_target(i_disp.br_mask, br_upd_if.brtag,
                                                      br_upd_if.dead, br_upd_if.mispredict) & br_upd_if.update;

assign w_dead_state_clear = i_commit.commit &
                            (i_commit.cmt_id == r_entry.cmt_id);

assign w_entry_rs2_ready_next = r_entry.inst.rd_regs[1].ready |
                                w_rs_phy_hit[1] & !w_rs_mispredicted[1] |
                                i_ex1_q_valid & i_ex1_q_updates.st_data_valid;

scariv_pkg::grp_id_t w_normal_comitted_grp_id;
scariv_pkg::grp_id_t w_commit_grp_id_mask;
scariv_pkg::grp_id_t w_done_tree_grp_id;
assign w_commit_grp_id_mask = r_entry.grp_id - 1;
assign w_done_tree_grp_id   = w_commit_grp_id_mask & (rob_info_if.done_grp_id & ~rob_info_if.except_valid);

assign w_normal_comitted_grp_id = (w_done_tree_grp_id == w_commit_grp_id_mask);

assign w_ready_to_mv_stbuf = (i_commit.cmt_id == r_entry.cmt_id) & w_normal_comitted_grp_id;

assign o_stq_entry_st_finish = (r_entry.state == STQ_COMMIT    ) & w_commit_finish & ~r_entry.is_rmw |
                               (r_entry.state == STQ_COMMIT    ) & w_commit_finish & i_stq_outptr_valid & r_entry.is_rmw & (r_entry.except_valid | r_entry.is_lr | r_entry.is_sc & !r_entry.sc_success) |
                               (r_entry.state == STQ_WAIT_STBUF) & i_st_buffer_empty & i_stbuf_accept |
                               (r_entry.state == STQ_DEAD      ) & i_stq_outptr_valid ;



assign w_missu_is_conflict     = i_ex2_q_updates.hazard_typ == EX2_HAZ_MISSU_CONFLICT;
assign w_missu_is_full         = i_ex2_q_updates.hazard_typ == EX2_HAZ_MISSU_FULL;
assign w_missu_evict_is_hazard = i_ex2_q_updates.hazard_typ == EX2_HAZ_MISSU_EVICT_CONFLICT;

assign w_missu_is_assigned = i_ex2_q_updates.hazard_typ == EX2_HAZ_MISSU_ASSIGNED;

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
                       (r_entry.inst.oldest_valid ? r_entry.oldest_ready & i_st_buffer_empty & i_missu_is_empty & i_stq_outptr_valid : 1'b1) &
                       all_operand_ready(r_entry);

assign w_commit_finish = o_stbuf_req_valid    & i_stbuf_accept |
                         o_uc_write_req_valid & i_uc_write_accept |
                         (r_entry.is_lr | r_entry.is_sc & !r_entry.sc_success) |
                         r_entry.except_valid;

always_comb begin
  w_entry_next = r_entry;

  w_entry_next.inst.rd_regs[1].ready = w_entry_rs2_ready_next | r_entry.inst.rd_regs[1].ready;
  if (~w_entry_next.is_rs2_get) begin
    if (w_rs_phy_hit[1]) begin
      w_entry_next.rs2_data   = w_rs2_phy_data;
      w_entry_next.is_rs2_get = 1'b1;
    end else if (i_ex1_q_valid & i_ex1_q_updates.st_data_valid) begin
      w_entry_next.rs2_data   = i_ex1_q_updates.st_data;
      w_entry_next.is_rs2_get = 1'b1;
    end
  end
  w_entry_next.inst.rd_regs[0].ready = r_entry.inst.rd_regs[0].ready | w_rs_phy_hit[0];
  w_entry_next.inst.rd_regs[0].predict_ready = w_rs_rel_hit[0] & w_rs_may_mispred[0];

  if (r_entry.is_valid) begin
    w_entry_next.oldest_ready = r_entry.oldest_ready | w_oldest_ready;
  end

  case (r_entry.state)
    STQ_INIT : begin
      if (w_entry_flush & w_entry_next.is_valid) begin
        w_entry_next.state = STQ_DEAD;
        // w_entry_next.is_valid = 1'b0;
        // w_entry_next.cmt_id = 'h0;
        // w_entry_next.grp_id = 'h0;
      end else if (i_disp_load) begin
        w_entry_next = assign_stq_disp(i_disp, i_disp_cmt_id, i_disp_grp_id,
                                       1 << (entry_index % scariv_conf_pkg::LSU_INST_NUM),
                                       w_rs_rel_hit, w_rs_phy_hit, w_rs_may_mispred);
        if (w_load_br_flush) begin
          w_entry_next.state    = STQ_DEAD;
        end
      end
    end // case: STQ_INIT
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
        w_entry_next.state           = i_ex1_q_updates.hazard_typ == EX1_HAZ_TLB_MISS  ? STQ_TLB_HAZ :
                                       i_ex1_q_updates.hazard_typ == EX1_HAZ_UC_ACCESS ? STQ_WAIT_OLDEST :
                                       STQ_DONE_EX2;
        w_entry_next.except_valid    = i_ex1_q_updates.tlb_except_valid;
        w_entry_next.except_type     = i_ex1_q_updates.tlb_except_type;
        w_entry_next.vaddr           = i_ex1_q_updates.vaddr;
        w_entry_next.paddr           = i_ex1_q_updates.paddr;
        w_entry_next.paddr_valid     = i_ex1_q_updates.hazard_typ != EX1_HAZ_TLB_MISS;
        w_entry_next.size            = i_ex1_q_updates.size;
        w_entry_next.is_uc           = i_ex1_q_updates.hazard_typ == EX1_HAZ_NONE ? i_ex1_q_updates.tlb_uc :
                                       r_entry.is_uc;

        w_entry_next.is_rmw  = i_ex1_q_updates.is_rmw;
        w_entry_next.rmwop   = i_ex1_q_updates.rmwop;

        w_entry_next.inst.oldest_valid = r_entry.inst.oldest_valid |
                                         (i_ex1_q_updates.hazard_typ == EX1_HAZ_UC_ACCESS);
      end // if (w_entry_next.is_valid & i_ex1_q_valid)
      if (r_entry.inst.rd_regs[0].predict_ready & w_rs_mispredicted[0]) begin
        w_entry_next.state = STQ_ISSUE_WAIT;
        w_entry_next.inst.rd_regs[0].predict_ready = 1'b0;
        w_entry_next.inst.rd_regs[1].predict_ready = 1'b0;
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
      end else if (r_entry.is_rmw & i_ex2_q_valid) begin
        w_entry_next.state = i_ex2_q_updates.hazard_typ == EX2_HAZ_L1D_CONFLICT  ? STQ_ISSUE_WAIT :
                             i_ex2_q_updates.hazard_typ == EX2_HAZ_RMW_ORDER_HAZ ? STQ_WAIT_OLDEST :
                             w_missu_is_conflict     ? STQ_MISSU_CONFLICT  :
                             w_missu_is_full         ? STQ_MISSU_FULL      :
                             w_missu_evict_is_hazard ? STQ_MISSU_EVICT_HAZ :
                             w_missu_is_assigned     ? STQ_ISSUE_WAIT    : // When MISSU Assigned, MISSU index return is zero so rerun and ge MISSU index.
                             STQ_DONE_EX3;
        w_entry_next.missu_haz_index_oh = i_ex2_q_updates.missu_index_oh;
        w_entry_next.is_amo           = i_ex2_q_updates.is_amo;
        w_entry_next.is_lr            = i_ex2_q_updates.is_lr;
        w_entry_next.is_sc            = i_ex2_q_updates.is_sc;
        w_entry_next.sc_success       = i_ex2_q_updates.sc_success;
      end else if (i_ex2_q_valid) begin
        w_entry_next.state = i_ex2_q_updates.hazard_typ == EX2_HAZ_RMW_ORDER_HAZ ? STQ_WAIT_OLDEST :
                             STQ_DONE_EX3;
      end else begin
        w_entry_next.state = STQ_DONE_EX3;
      end // else: !if(r_entry.is_rmw & i_ex2_q_valid)
    end
    STQ_MISSU_CONFLICT : begin
      if (w_entry_flush) begin
        w_entry_next.state = STQ_DEAD;
      end else if (i_missu_resolve.valid && i_missu_resolve.resolve_index_oh == r_entry.missu_haz_index_oh) begin
        w_entry_next.state = STQ_ISSUE_WAIT;
      end else if (~|(i_missu_resolve.missu_entry_valids & r_entry.missu_haz_index_oh)) begin
        w_entry_next.state = STQ_ISSUE_WAIT;
      end
    end
    STQ_MISSU_FULL : begin
      if (w_entry_flush) begin
        w_entry_next.state = STQ_DEAD;
      end else if (!i_missu_is_full) begin
        w_entry_next.state = STQ_ISSUE_WAIT;
      end
    end
    STQ_MISSU_EVICT_HAZ : begin
      if (w_entry_flush) begin
        w_entry_next.state = STQ_DEAD;
      end else if (i_missu_resolve.valid && i_missu_resolve.resolve_index_oh == r_entry.missu_haz_index_oh) begin
        w_entry_next.state = STQ_ISSUE_WAIT;
      end else if (~|(i_missu_resolve.missu_entry_valids & r_entry.missu_haz_index_oh)) begin
        w_entry_next.state = STQ_ISSUE_WAIT;
      end
    end
    STQ_DONE_EX3 : begin
      // Ex2 --> Ex3 needs due to adjust Load Pipeline with Done Port
      if (w_entry_flush) begin
        w_entry_next.state = STQ_DEAD;
      end else begin
        w_entry_next.state = STQ_WAIT_COMMIT;
        w_entry_next.another_flush_valid  = ex3_done_if.payload.another_flush_valid;
        w_entry_next.another_flush_cmt_id = ex3_done_if.payload.another_flush_cmt_id;
        w_entry_next.another_flush_grp_id = ex3_done_if.payload.another_flush_grp_id;
      end
    end
    STQ_WAIT_OLDEST : begin
      if (w_entry_flush) begin
        w_entry_next.state = STQ_DEAD;
      end else if (r_entry.is_rmw & w_oldest_ready & i_st_buffer_empty & i_missu_is_empty & i_stq_outptr_valid) begin
        w_entry_next.state = STQ_ISSUE_WAIT;
      end else if (w_oldest_ready | r_entry.oldest_ready) begin
        w_entry_next.state = STQ_ISSUE_WAIT;
      end
    end
    STQ_WAIT_COMMIT : begin
      if (w_entry_flush) begin
        w_entry_next.state = STQ_DEAD;
      end else if (w_ready_to_mv_stbuf) begin
        w_entry_next.is_committed = 1'b1;
        if (r_entry.is_rmw) begin
          if (r_entry.except_valid |
              r_entry.is_lr |
              r_entry.is_sc & !r_entry.sc_success) begin
            w_entry_next.state = STQ_COMMIT;
          end else begin
            w_entry_next.state = STQ_WAIT_STBUF;
          end
        end else if (!w_entry_next.inst.rd_regs[1].ready) begin
          w_entry_next.state = STQ_WAIT_ST_DATA;
        end else begin
          w_entry_next.state = STQ_COMMIT;
        end
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
      end else if (w_entry_next.inst.rd_regs[1].ready) begin
        w_entry_next.state = STQ_COMMIT;
      end
    end
    STQ_COMMIT : begin
      if (o_stq_entry_st_finish) begin
        w_entry_next.state = STQ_INIT;
        w_entry_next.is_valid = 1'b0;
        // prevent all updates from Pipeline
        w_entry_next.cmt_id = 'h0;
        w_entry_next.grp_id = 'h0;
      end
    end // case: STQ_COMMIT
    STQ_WAIT_STBUF : begin
      if (i_st_buffer_empty & i_stbuf_accept) begin
        w_entry_next.state = STQ_INIT;
        w_entry_next.is_valid = 1'b0;
        // prevent all updates from Pipeline
        w_entry_next.cmt_id = 'h0;
        w_entry_next.grp_id = 'h0;
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
    end // case: scariv_pkg::DEAD
    default : begin
      w_entry_next.state    = STQ_INIT;
// `ifdef SIMULATION
//       $fatal (0, "This state sholudn't be reached.\n");
// `endif // SIMULATION
    end
  endcase // case (w_entry_next.state)

  // BrMask update
  if (br_upd_if.update) begin
    w_entry_next.br_mask[br_upd_if.brtag] = 1'b0;
  end

end // always_comb


// -----------------
// Oldest Detection
// -----------------

assign w_oldest_ready = (rob_info_if.cmt_id == r_entry.cmt_id) &
                        ((rob_info_if.done_grp_id & r_entry.grp_id-1) == r_entry.grp_id-1);

assign o_stbuf_req_valid = r_entry.is_rmw ? (r_entry.state == STQ_WAIT_STBUF) & i_st_buffer_empty & i_stq_outptr_valid  :
                           (r_entry.state == STQ_COMMIT) & ~r_entry.is_uc & ~r_entry.except_valid;


assign o_uc_write_req_valid = (r_entry.state == STQ_COMMIT) & r_entry.is_uc & ~r_entry.except_valid;

// // Snoop Interface Hit
// /* verilator lint_off WIDTH */
// logic [$clog2(scariv_lsu_pkg::DCACHE_DATA_B_W)-1: 0] w_entry_snp_addr_diff;
// assign w_entry_snp_addr_diff = r_entry.paddr - {stq_snoop_if.req_s0_paddr[riscv_pkg::PADDR_W-1:$clog2(scariv_lsu_pkg::DCACHE_DATA_B_W)], {$clog2(scariv_lsu_pkg::DCACHE_DATA_B_W){1'b0}}};
// // logic                                                w_snoop_s0_hit;
// assign o_snoop_s0_hit = r_entry.paddr_valid &
//                         (r_entry.state == STQ_COMMIT) &
//                         (stq_snoop_if.req_s0_paddr[riscv_pkg::PADDR_W-1:$clog2(scariv_lsu_pkg::DCACHE_DATA_B_W)] ==
//                          r_entry.paddr[riscv_pkg::PADDR_W-1:$clog2(scariv_lsu_pkg::DCACHE_DATA_B_W)]);
// assign stq_snoop_if.resp_s1_valid = stq_snoop_if.req_s0_valid;
// assign stq_snoop_if.resp_s1_be    = w_snoop_s0_hit ? gen_dw_cacheline(r_entry.size, w_entry_snp_addr_diff) : 'h0;
// assign stq_snoop_if.resp_s1_data  = w_snoop_s0_hit ? {{(scariv_conf_pkg::DCACHE_DATA_W-scariv_pkg::ALEN_W){1'b0}}, r_entry.rs2_data} << {w_entry_snp_addr_diff, 3'b000} : 'h0;

function stq_entry_t assign_stq_disp (scariv_pkg::disp_t in,
                                      scariv_pkg::cmt_id_t cmt_id,
                                      scariv_pkg::grp_id_t grp_id,
                                      logic [scariv_conf_pkg::LSU_INST_NUM-1: 0] pipe_sel_oh,
                                      logic [ 1: 0] rs_rel_hit, logic [ 1: 0] rs_phy_hit, logic [ 1: 0] rs_may_mispred);
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

  ret.is_rs2_get  = 1'b0;

  ret.except_valid = 1'b0;

  ret.inst.oldest_valid = (in.cat == decoder_inst_cat_pkg::INST_CAT_ST) &
                          (in.subcat == decoder_inst_cat_pkg::INST_SUBCAT_RMW);
  ret.oldest_ready = 1'b0;
  ret.is_committed = 1'b0;
  ret.is_uc = 1'b0;

  for (int rs_idx = 0; rs_idx < 2; rs_idx++) begin
    ret.inst.rd_regs[rs_idx].valid         = in.rd_regs[rs_idx].valid;
    ret.inst.rd_regs[rs_idx].typ           = in.rd_regs[rs_idx].typ;
    ret.inst.rd_regs[rs_idx].regidx        = in.rd_regs[rs_idx].regidx;
    ret.inst.rd_regs[rs_idx].rnid          = in.rd_regs[rs_idx].rnid;
    ret.inst.rd_regs[rs_idx].ready         = in.rd_regs[rs_idx].ready | rs_rel_hit[rs_idx] & ~rs_may_mispred[rs_idx] | rs_phy_hit[rs_idx];
    ret.inst.rd_regs[rs_idx].predict_ready = rs_rel_hit[rs_idx] & rs_may_mispred[rs_idx];
  end

  for (int rs_idx = 2; rs_idx < 3; rs_idx++) begin
    ret.inst.rd_regs[rs_idx].valid = 1'b0;
  end

`ifdef SIMULATION
  ret.kanata_id = in.kanata_id;
`endif // SIMULATION

  return ret;
endfunction // assign_stq_disp


function logic all_operand_ready(stq_entry_t entry);
  logic     ret;
  ret = (!entry.inst.rd_regs[0].valid | entry.inst.rd_regs[0].valid  & (entry.inst.rd_regs[0].ready |
                                                                        entry.inst.rd_regs[0].predict_ready & !w_rs_mispredicted[0]));
  return ret;
endfunction // all_operand_ready

endmodule // scariv_stq_entry
