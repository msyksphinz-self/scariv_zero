// ------------------------------------------------------------------------
// NAME : scariv_rob
// TYPE : module
// ------------------------------------------------------------------------
// Reorder Buffer
// ------------------------------------------------------------------------
// Input: Logical Register Index
// Output: Physical Register Index
// ------------------------------------------------------------------------

module scariv_rob
  import scariv_conf_pkg::*;
  import scariv_pkg::*;
(
   input logic                   i_clk,
   input logic                   i_reset_n,

`ifdef ILA_DEBUG
   output scariv_ila_pkg::ila_debug_rob_t  o_ila_debug_rob,
`endif // ILA_DEBUG

   scariv_front_if.slave                 rn_front_if,

   cre_ret_if.slave              cre_ret_if,

   output cmt_id_t o_sc_new_cmt_id,

   done_report_if.slave  done_report_if  [CMT_BUS_SIZE],
   flush_report_if.slave flush_report_if [LSU_INST_NUM],

   br_upd_if.slave  br_upd_slave_if,

   commit_if.master        commit_if,
   fflags_update_if.master fflags_update_if,
   output cmt_rnid_upd_t   o_commit_rnid_update,

   // Interrupt Request information
   interrupt_if.slave  int_if,

   // ROB notification interface
   rob_info_if.master rob_info_if
   );

rob_entry_t              w_entries[CMT_ENTRY_SIZE];
cmt_id_t     w_in_cmt_id, w_out_cmt_id;
logic [DISP_SIZE-1:0]              w_disp_grp_id;
logic [CMT_ENTRY_SIZE-1:0]         w_entry_all_done;
logic [DISP_SIZE-1:0]              w_br_upd_valid_oh;
// scariv_pkg::vaddr_t    w_upd_br_vaddr;
logic [DISP_SIZE-1:0]              w_dead_grp_id_except_tmp;
logic [DISP_SIZE-1:0]              w_dead_grp_id;
logic [DISP_SIZE-1:0]              w_frontend_exception_valid;
logic [DISP_SIZE-1:0]              w_frontend_exception_tree_valid;

logic [$clog2(CMT_ENTRY_SIZE)-1: 0] w_cmt_except_valid_encoded;

logic                                w_ignore_disp;
logic [$clog2(CMT_ENTRY_SIZE): 0]    w_credit_return_val;

rob_entry_t   w_out_entry;
rob_payload_t w_out_payload;

//
// Pointer
//
logic                                      w_in_valid, w_out_valid;
logic [CMT_ENTRY_W-1:0]                    w_out_cmt_entry_id;
logic [CMT_ENTRY_W-1:0]                    w_in_cmt_entry_id;

assign w_out_cmt_entry_id = w_out_cmt_id[CMT_ENTRY_W-1:0];
assign w_in_cmt_entry_id  = w_in_cmt_id [CMT_ENTRY_W-1:0];

assign w_in_valid  = rn_front_if.valid;
assign w_out_valid = w_entry_all_done[w_out_cmt_entry_id];

/* verilator lint_off UNOPTFLAT */
commit_blk_t     w_commit;
fflags_update_if w_fflags_update_if();
cmt_rnid_upd_t   w_commit_rnid_update;

logic                                      w_flush_valid;
assign w_flush_valid = scariv_pkg::is_flushed_commit(w_out_valid, w_commit) & w_out_valid |
                       scariv_pkg::is_flushed_commit(commit_if.commit_valid, commit_if.payload);

inoutptr #(.SIZE(CMT_ID_SIZE)) u_cmt_ptr(.i_clk (i_clk), .i_reset_n(i_reset_n),
                                         .i_clear (1'b0),
                                         .i_in_valid (w_in_valid ), .o_in_ptr (w_in_cmt_id  ),
                                         .i_out_valid(w_out_valid), .o_out_ptr(w_out_cmt_id));

assign rn_front_if.ready = 1'b1;
assign w_ignore_disp = w_flush_valid & (rn_front_if.valid & rn_front_if.ready);
assign w_credit_return_val = (w_out_valid ? 'h1 : 'h0) /* +
                             (w_ignore_disp   ? 'h1 : 'h0) */ ;

scariv_credit_return_slave
  #(.MAX_CREDITS(CMT_ENTRY_SIZE))
u_credit_return_slave
(
 .i_clk(i_clk),
 .i_reset_n(i_reset_n),

 .i_get_return(w_out_valid| w_ignore_disp),
 .i_return_val(w_credit_return_val),

 .cre_ret_if (cre_ret_if)
 );

generate for (genvar d_idx = 0; d_idx < DISP_SIZE; d_idx++) begin : disp_loop
  assign w_disp_grp_id[d_idx] = rn_front_if.payload.inst[d_idx].valid;
  assign w_frontend_exception_valid[d_idx] = rn_front_if.payload.tlb_except_valid[d_idx] | rn_front_if.payload.inst[d_idx].illegal_valid;
  assign w_frontend_exception_tree_valid[d_idx] = |w_frontend_exception_valid[d_idx: 0];
end
endgenerate

`ifdef SIMULATION
riscv_pkg::xlen_t w_sim_mstatus[CMT_ENTRY_SIZE][scariv_conf_pkg::DISP_SIZE];
`endif // SIMULATION

grp_id_t w_rn_is_cond_arr;
generate for (genvar d_idx = 0; d_idx < scariv_conf_pkg::DISP_SIZE; d_idx++) begin: br_loop
  assign w_rn_is_cond_arr[d_idx] = rn_front_if.payload.inst[d_idx].is_cond &
                                   rn_front_if.payload.resource_cnt.bru_inst_valid[d_idx];
end endgenerate
scariv_pkg::disp_t w_rn_front_if_cond_inst;

bit_oh_or_packed
  #(.T(scariv_pkg::disp_t),
    .WORDS(scariv_conf_pkg::DISP_SIZE)
    )
u_rn_br_cond_info (
 .i_oh      (w_rn_is_cond_arr),
 .i_data    (rn_front_if.payload.inst),
 .o_selected(w_rn_front_if_cond_inst)
 );


function automatic rob_entry_t assign_rob_entry();
  rob_entry_t ret;

  ret.valid       = 1'b1;
  ret.cmt_id_msb  = w_in_cmt_id[CMT_ENTRY_W];
  ret.dead        = w_disp_grp_id & {scariv_conf_pkg::DISP_SIZE{w_flush_valid}};
  ret.grp_id      = w_disp_grp_id;

  ret.fflags_update_valid = 'h0;

  ret.int_inserted = rn_front_if.payload.int_inserted;

  for (int d_idx = 0; d_idx < scariv_conf_pkg::DISP_SIZE; d_idx++) begin : disp_loop
    // If TLB Exception detected before execution, this instruction already done.
    ret.done_grp_id [d_idx] = w_frontend_exception_tree_valid[d_idx] ? w_disp_grp_id[d_idx] : 1'b0;
    ret.dead        [d_idx] = ret.dead[d_idx] /* | ret.except_valid[d_idx] */;
`ifdef SIMULATION
    // ret.sim_dead_reason[d_idx] = ret.except_valid[d_idx] ? DEAD_EXC : DEAD_NONE;
`endif // SIMULATION
  end

  return ret;

endfunction // assign_rob_entry


function automatic rob_payload_t assign_rob_payload ();
  rob_payload_t ret;

  for (int d_idx = 0; d_idx < scariv_conf_pkg::DISP_SIZE; d_idx++) begin : inst_loop
    ret.disp[d_idx].pc_addr        = rn_front_if.payload.inst[d_idx].pc_addr       ;
    ret.disp[d_idx].wr_reg         = rn_front_if.payload.inst[d_idx].wr_reg        ;
    ret.disp[d_idx].inst           = rn_front_if.payload.inst[d_idx].inst          ;
`ifdef SIMULATION
    ret.disp[d_idx].rvc_inst_valid = rn_front_if.payload.inst[d_idx].rvc_inst_valid;
    ret.disp[d_idx].rvc_inst       = rn_front_if.payload.inst[d_idx].rvc_inst      ;
    ret.disp[d_idx].kanata_id      = rn_front_if.payload.inst[d_idx].kanata_id     ;
`endif // SIMULATION
  end // block: inst_loop

  return ret;
endfunction // assign_rob_paylaod

rob_entry_t    w_entry_in;
rob_payload_t  w_payload_in;
always_comb begin
  w_entry_in   = assign_rob_entry();
  w_payload_in = assign_rob_payload();
end

generate for (genvar c_idx = 0; c_idx < CMT_ENTRY_SIZE; c_idx++) begin : entry_loop
logic w_load_valid;
  assign w_load_valid = rn_front_if.valid & (w_in_cmt_entry_id == c_idx);

  scariv_rob_entry u_entry
    (
     .i_clk (i_clk),
     .i_reset_n (i_reset_n),

     .i_cmt_id ({w_in_cmt_id[CMT_ENTRY_W], c_idx[CMT_ENTRY_W-1:0]}),

     .i_load_valid (w_load_valid),
     .i_entry_in   (w_entry_in),

     .done_report_if  (done_report_if),
     .flush_report_if (flush_report_if),

     .o_entry          (w_entries[c_idx]),
     .o_block_all_done (w_entry_all_done[c_idx]),
     .commit_if_finish  (w_entry_all_done[c_idx] &
                        (w_out_cmt_entry_id == c_idx)),

     .i_kill (w_flush_valid),

     .br_upd_slave_if (br_upd_slave_if)
     );

`ifdef SIMULATION
  for (genvar d = 0; d < scariv_conf_pkg::DISP_SIZE; d++) begin
    assign w_sim_mstatus[c_idx][d] = u_entry.r_mstatus[d];
  end
`endif // SIMULATION

end endgenerate

distributed_ram
  #(.WIDTH($bits(rob_payload_t)),
    .WORDS(CMT_ENTRY_SIZE)
    )
u_payload_ram
  (
   .i_clk     (i_clk    ),
   .i_reset_n (i_reset_n),

   .i_wr     (rn_front_if.valid & rn_front_if.ready),
   .i_wr_addr(w_in_cmt_entry_id),
   .i_wr_data(w_payload_in),

   .i_rd_addr(w_out_cmt_entry_id),
   .o_rd_data(w_out_payload)
   );

assign o_sc_new_cmt_id = w_in_cmt_id;

assign w_out_entry = w_entries[w_out_cmt_entry_id];

// Interrupt detection
logic w_int_valid;
logic [$clog2(riscv_pkg::XLEN_W)-1: 0] w_int_type;

assign w_int_valid = int_if.m_external_int_valid | int_if.m_timer_int_valid | int_if.m_software_int_valid |
                     int_if.s_external_int_valid | int_if.s_timer_int_valid | int_if.s_software_int_valid;

assign w_int_type = int_if.m_external_int_valid ? riscv_common_pkg::MACHINE_EXTERNAL_INT :
                    int_if.m_timer_int_valid    ? riscv_common_pkg::MACHINE_TIMER_INT    :
                    int_if.m_software_int_valid ? riscv_common_pkg::MACHINE_SOFT_INT     :
                    int_if.s_external_int_valid ? riscv_common_pkg::SUPER_EXTERNAL_INT   :
                    int_if.s_timer_int_valid    ? riscv_common_pkg::SUPER_TIMER_INT      :
                    int_if.s_software_int_valid ? riscv_common_pkg::SUPER_SOFT_INT       :
                    'h0;

assign w_commit.cmt_id       = w_out_cmt_id;
assign w_commit.grp_id       = w_out_entry.grp_id;
logic                                  w_rob_except_match;
assign w_rob_except_match = r_rob_except.valid & (r_rob_except.cmt_id == w_commit.cmt_id);

assign w_commit.except_valid = {scariv_conf_pkg::DISP_SIZE{w_rob_except_match}} & r_rob_except.grp_id | w_int_valid;
assign w_commit.int_valid    = w_int_valid;
assign w_commit.except_type  = w_int_valid ? except_t'(w_int_type) : r_rob_except.typ;
/* verilator lint_off WIDTH */
assign w_commit.tval          = (w_commit.except_type == scariv_pkg::INST_ADDR_MISALIGN  ||
                                 w_commit.except_type == scariv_pkg::INST_ACC_FAULT) ? {w_out_payload.disp[0].pc_addr, 1'b0} + {w_cmt_except_valid_encoded, 2'b00} :
                                r_rob_except.tval;
encoder #(.SIZE(CMT_ENTRY_SIZE)) except_pc_vaddr (.i_in (r_rob_except.grp_id), .o_out(w_cmt_except_valid_encoded));
/* verilator lint_off WIDTH */
assign w_commit.epc          = w_out_payload.disp[w_cmt_except_valid_encoded].pc_addr;
assign w_commit.dead_id      = (w_out_entry.dead | w_dead_grp_id | {{(scariv_conf_pkg::DISP_SIZE-1){w_int_valid}}, 1'b0}) & w_commit.grp_id;
assign w_commit.flush_valid  = {scariv_conf_pkg::DISP_SIZE{w_rob_except_match}} & r_rob_except.grp_id | w_int_valid;

always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    commit_if.commit_valid <= 1'b0;
  end else begin
    commit_if.commit_valid <= w_out_valid;
    commit_if.payload      <= w_commit;
  end
end

// -------------------------------
// Exception detect and selection
// -------------------------------

localparam EXCEPT_SIZE = CMT_BUS_SIZE + scariv_conf_pkg::LSU_INST_NUM + 1;  // +1 is from Frontend Exception

logic [EXCEPT_SIZE-1: 0] w_done_except_valid;
cmt_id_t          w_done_cmt_id      [EXCEPT_SIZE];
grp_id_t          w_done_grp_id      [EXCEPT_SIZE];
except_t          w_done_except_type [EXCEPT_SIZE];
riscv_pkg::xlen_t w_done_tval        [EXCEPT_SIZE];
generate for (genvar c_idx = 0; c_idx < CMT_BUS_SIZE; c_idx++) begin : done_exc_loop
  assign w_done_except_valid[c_idx] = done_report_if[c_idx].valid & done_report_if[c_idx].except_valid;
  assign w_done_cmt_id      [c_idx] = done_report_if[c_idx].cmt_id;
  assign w_done_grp_id      [c_idx] = done_report_if[c_idx].grp_id;
  assign w_done_except_type [c_idx] = done_report_if[c_idx].except_type;
  assign w_done_tval        [c_idx] = done_report_if[c_idx].except_tval;
end endgenerate
generate for (genvar c_idx = 0; c_idx < scariv_conf_pkg::LSU_INST_NUM; c_idx++) begin : done_exc_flush_loop
  assign w_done_except_valid[c_idx + CMT_BUS_SIZE] = flush_report_if[c_idx].valid;
  assign w_done_cmt_id      [c_idx + CMT_BUS_SIZE] = flush_report_if[c_idx].cmt_id;
  assign w_done_grp_id      [c_idx + CMT_BUS_SIZE] = flush_report_if[c_idx].grp_id;
  assign w_done_except_type [c_idx + CMT_BUS_SIZE] = ANOTHER_FLUSH;
  assign w_done_tval        [c_idx + CMT_BUS_SIZE] = 'h0;
end endgenerate
assign w_done_except_valid[CMT_BUS_SIZE + scariv_conf_pkg::LSU_INST_NUM] = |({DISP_SIZE{rn_front_if.valid}} & w_disp_grp_id & w_frontend_exception_valid);
assign w_done_cmt_id      [CMT_BUS_SIZE + scariv_conf_pkg::LSU_INST_NUM] = w_in_cmt_id;
assign w_done_grp_id      [CMT_BUS_SIZE + scariv_conf_pkg::LSU_INST_NUM] = {DISP_SIZE{rn_front_if.valid}} & w_disp_grp_id & w_frontend_exception_valid;
logic [$clog2(DISP_SIZE)-1: 0] w_frontend_exception_encoded;
encoder #(.SIZE(DISP_SIZE)) u_except_rob_in_disp (.i_in (w_frontend_exception_valid), .o_out(w_frontend_exception_encoded));
assign w_done_except_type [CMT_BUS_SIZE + scariv_conf_pkg::LSU_INST_NUM] = rn_front_if.payload.tlb_except_valid[w_frontend_exception_encoded] ? rn_front_if.payload.tlb_except_cause[w_frontend_exception_encoded] : ILLEGAL_INST;
assign w_done_tval        [CMT_BUS_SIZE + scariv_conf_pkg::LSU_INST_NUM] = rn_front_if.payload.tlb_except_valid[w_frontend_exception_encoded] & (rn_front_if.payload.tlb_except_cause[w_frontend_exception_encoded] != ILLEGAL_INST) ?
                                                                           rn_front_if.payload.tlb_except_tval[w_frontend_exception_encoded] :
                                                                           rn_front_if.payload.inst[w_frontend_exception_encoded].rvc_inst_valid ? rn_front_if.payload.inst[w_frontend_exception_encoded].rvc_inst : rn_front_if.payload.inst[w_frontend_exception_encoded].inst;

logic                             w_exc_min_valid;
logic [$clog2(EXCEPT_SIZE)-1: 0]  w_exc_min_idx;

bit_multiple_age_min
  #(.WORDS(EXCEPT_SIZE))
u_detect_exc_min
  (
   .i_valids(w_done_except_valid),
   .i_cmt_id(w_done_cmt_id),
   .i_grp_id(w_done_grp_id),

   .o_valid  (w_exc_min_valid),
   .o_min_idx(w_exc_min_idx)
   );

typedef struct packed {
  logic                valid;
  scariv_pkg::cmt_id_t cmt_id;
  scariv_pkg::grp_id_t grp_id;
  except_t             typ;
  riscv_pkg::xlen_t    tval;
} rob_except_t;

rob_except_t r_rob_except;
rob_except_t w_rob_except_next;

always_comb begin
  w_rob_except_next = r_rob_except;

  if (commit_if.commit_valid & (commit_if.payload.cmt_id == r_rob_except.cmt_id)) begin
    w_rob_except_next.valid = 'h0;
  end

  if (|w_done_except_valid) begin
    if (r_rob_except.valid) begin
      if (id0_is_older_than_id1(w_done_cmt_id[w_exc_min_idx], w_done_grp_id[w_exc_min_idx],
                                r_rob_except.cmt_id, r_rob_except.grp_id)) begin
        w_rob_except_next.cmt_id = w_done_cmt_id     [w_exc_min_idx];
        w_rob_except_next.grp_id = w_done_grp_id     [w_exc_min_idx];
        w_rob_except_next.typ    = w_done_except_type[w_exc_min_idx];
        w_rob_except_next.tval   = w_done_tval       [w_exc_min_idx];
      end
    end else begin
      w_rob_except_next.valid  = 1'b1;
      w_rob_except_next.cmt_id = w_done_cmt_id     [w_exc_min_idx];
      w_rob_except_next.grp_id = w_done_grp_id     [w_exc_min_idx];
      w_rob_except_next.typ    = w_done_except_type[w_exc_min_idx];
      w_rob_except_next.tval   = w_done_tval       [w_exc_min_idx];
    end
  end // if (|w_done_except_valid)

  if (scariv_pkg::is_br_flush_target(w_rob_except_next.cmt_id, w_rob_except_next.grp_id, br_upd_slave_if.cmt_id, br_upd_slave_if.grp_id,
                                     br_upd_slave_if.dead, br_upd_slave_if.mispredict) & br_upd_slave_if.update & w_rob_except_next.valid) begin
    w_rob_except_next.valid = 'h0;
  end
end // always_comb
always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_rob_except.valid <= 1'b0;
  end else begin
    r_rob_except <= w_rob_except_next;
  end
end


`ifdef SIMULATION
  `ifdef COMPARE_ISS

import "DPI-C" function void spike_update_timer (input longint value);

always_ff @ (negedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
  end else begin
    if (commit_if.commit_valid & w_out_entry.int_inserted) begin
      spike_update_timer (`SUBSYSTEM_TOP.u_clint.w_mtime_next);
    end
  end
end
  `endif //  COMPARE_ISS
`endif // SIMULATION

assign w_commit_rnid_update.commit     = w_out_valid;
generate for (genvar d_idx = 0; d_idx < DISP_SIZE; d_idx++) begin : commit_rd_loop
  assign w_commit_rnid_update.rnid_valid[d_idx] = w_out_payload.disp[d_idx].wr_reg.valid;
  assign w_commit_rnid_update.old_rnid  [d_idx] = w_out_payload.disp[d_idx].wr_reg.old_rnid;
  assign w_commit_rnid_update.rd_rnid   [d_idx] = w_out_payload.disp[d_idx].wr_reg.rnid;
  assign w_commit_rnid_update.rd_regidx [d_idx] = w_out_payload.disp[d_idx].wr_reg.regidx;
  assign w_commit_rnid_update.rd_typ    [d_idx] = w_out_payload.disp[d_idx].wr_reg.typ;
end
endgenerate
assign w_commit_rnid_update.dead_id        = w_commit.dead_id;
assign w_commit_rnid_update.except_valid   = w_commit.except_valid;
assign w_commit_rnid_update.except_type    = w_commit.except_type;

always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    o_commit_rnid_update.commit <= 1'b0;
  end else begin
    o_commit_rnid_update <= w_commit_rnid_update;
  end
end


grp_id_t w_fflags_update_valid_oh;
fflags_t w_fflags_sel;
bit_extract_msb  #(.WIDTH(DISP_SIZE)) u_bit_fflags_extract (.in(w_out_entry.fflags_update_valid), .out(w_fflags_update_valid_oh));
bit_oh_or_packed #(.T(fflags_t), .WORDS(DISP_SIZE)) u_bit_fflags_select (.i_oh(w_fflags_update_valid_oh), .i_data(w_out_entry.fflags), .o_selected(w_fflags_sel));

// --------------------------
// FFLAGS update when commit
// --------------------------
assign w_fflags_update_if.valid  = w_out_valid& (|w_out_entry.fflags_update_valid);
assign w_fflags_update_if.fflags = w_fflags_sel;

always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    fflags_update_if.valid <= 1'b0;
  end else begin
    fflags_update_if.valid  <= w_fflags_update_if.valid;
    fflags_update_if.fflags <= w_fflags_update_if.fflags;
  end
end

// --------------------------------------------------
// Notification of RAS Recovery by dead instruction
// --------------------------------------------------
grp_id_t w_is_call_array;
grp_id_t w_is_ret_array;
logic [$clog2(scariv_conf_pkg::RAS_ENTRY_SIZE)-1: 0] w_ras_index_array[scariv_conf_pkg::DISP_SIZE];


// Make dead Instruction, (after exception)
bit_tree_lsb #(.WIDTH(DISP_SIZE)) u_bit_dead_except_grp_id (.in(r_rob_except.grp_id), .out(w_dead_grp_id_except_tmp));
logic [DISP_SIZE-1: 0] w_except_dead_grp_id;
assign w_except_dead_grp_id = {w_dead_grp_id_except_tmp[DISP_SIZE-2: 0], 1'b0};  // active flush itself doesn't include dead instruction, so, 1-bit left shift
assign w_dead_grp_id = r_rob_except.valid & (w_commit.cmt_id == r_rob_except.cmt_id) ? w_except_dead_grp_id : 'h0;

// ROB Notification Information
// rob_info_if rob_info_if_pre();
always_ff @ (posedge i_clk) begin
  rob_info_if.cmt_id       <= w_out_cmt_id;
  rob_info_if.grp_id       <= w_out_entry.grp_id;
  rob_info_if.done_grp_id  <= {DISP_SIZE{w_out_entry.valid}} & w_out_entry.done_grp_id;
  rob_info_if.upd_pc_valid <= 1'b0;
  rob_info_if.except_valid <= r_rob_except.valid & (r_rob_except.cmt_id == w_out_cmt_id) ? r_rob_except.grp_id & ~w_out_entry.dead : 'h0;
end

// -----------------------------
// DeadLock Check for Debugging
// -----------------------------
logic [15: 0] r_uncommitted_counter;
logic         r_deadlocked;
always_ff @ (posedge i_clk, posedge i_reset_n) begin
  if (!i_reset_n) begin
    r_uncommitted_counter <= 'h0;
    r_deadlocked          <= 1'b0;
  end else begin
    if (commit_if.commit_valid) begin
      r_uncommitted_counter <= 'h0;
    end else begin
      r_uncommitted_counter <= r_uncommitted_counter + 'h1;
    end
    if (&r_uncommitted_counter) begin
      r_deadlocked <= 1'b1;
    end
  end // else: !if(!i_reset_n)
end // always_ff @ (posedge i_clk, posedge i_reset_n)

logic [ 7: 0] r_dead_uncommitted_counter;
logic         r_dead_deadlocked;
always_ff @ (posedge i_clk, posedge i_reset_n) begin
  if (!i_reset_n) begin
    r_dead_uncommitted_counter <= 'h0;
    r_dead_deadlocked          <= 1'b0;
  end else begin
    if (commit_if.commit_valid & |(commit_if.payload.grp_id ^ commit_if.payload.dead_id)) begin
      r_dead_uncommitted_counter <= 'h0;
    end else begin
      r_dead_uncommitted_counter <= r_dead_uncommitted_counter + 'h1;
    end
    if (&r_uncommitted_counter) begin
      r_dead_deadlocked <= 1'b1;
    end
  end // else: !if(!i_reset_n)
end // always_ff @ (posedge i_clk, posedge i_reset_n)

`ifdef SIMULATION
`ifdef MONITOR
logic [CMT_ENTRY_SIZE-1: 0] w_entry_valids;
generate for (genvar c_idx = 0; c_idx < CMT_ENTRY_SIZE; c_idx++) begin : dbg_entry_loop
  assign w_entry_valids[c_idx] = w_entries[c_idx].valid;
end
endgenerate

function void dump_entry_json(int fp, rob_entry_t entry, int index);

  if (entry.valid) begin
    $fwrite(fp, "    \"scariv_rob_entry[%d]\" : {", index[$clog2(CMT_ENTRY_SIZE)-1:0]);
    $fwrite(fp, "valid:%d, ", entry.valid);
    // $fwrite(fp, "pc_addr:\"0x%0x\", ", entry.pc_addr << 1);

    $fwrite(fp, "grp_id:\"0x%02x\", ", entry.grp_id);
    $fwrite(fp, "done_grp_id:\"0x%02x\", ", entry.done_grp_id);

    $fwrite(fp, "dead:%d, ", entry.dead);
    // $fwrite(fp, "except_valid:0x%02x", entry.except_valid);

    $fwrite(fp, " },\n");
  end // if (entry.valid)

endfunction // dump_json


function void dump_json(int fp);
  if (|w_entry_valids) begin
    $fwrite(fp, "  \"scariv_rob\" : {\n");
    $fwrite(fp, "    in_cmt_id: %d,\n", w_in_cmt_id);
    $fwrite(fp, "    out_cmt_id: %d,\n", w_out_cmt_id);
    for (int c_idx = 0; c_idx < CMT_ENTRY_SIZE; c_idx++) begin
      dump_entry_json (fp, w_entries[c_idx], c_idx);
    end
    $fwrite(fp, "  },\n");
  end
endfunction // dump_json

logic [63: 0] r_cycle_count;
logic [63: 0] r_commit_count;
logic [63: 0] r_inst_count;
logic [63: 0] r_dead_count;
logic [63: 0] r_rn_front_if_count;
logic [63: 0] r_rn_front_if_inst_count;
logic [63: 0] r_rob_max_period;
logic [63: 0] r_rob_entry_count;

struct packed {
  logic [63: 0] dead_exc;
  logic [63: 0] dead_branch;
  logic [63: 0] dead_previnst;
  logic [63: 0] dead_anotherflush;
  logic [63: 0] dead_ext_kill;
} r_dead_reason_count;

always_ff @ (negedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_rn_front_if_count <= 'h0;
    r_rn_front_if_inst_count <= 'h0;

    r_commit_count <= 'h0;
    r_inst_count   <= 'h0;
    r_dead_count   <= 'h0;
    r_cycle_count  <= 'h0;

    r_rob_max_period  <= 'h0;
    r_rob_entry_count <= 'h0;
  end else begin
    r_cycle_count <= r_cycle_count + 'h1;
    if (r_cycle_count % sim_pkg::COUNT_UNIT == sim_pkg::COUNT_UNIT-1) begin
      r_rn_front_if_count <= 'h0;
      r_rn_front_if_inst_count <= 'h0;

      r_commit_count <= 'h0;
      r_inst_count   <= 'h0;
      r_dead_count   <= 'h0;
      r_dead_reason_count.dead_exc          = 'h0;
      r_dead_reason_count.dead_branch       = 'h0;
      r_dead_reason_count.dead_previnst     = 'h0;
      r_dead_reason_count.dead_anotherflush = 'h0;
      r_dead_reason_count.dead_ext_kill     = 'h0;

      r_rob_max_period  <= 'h0;
      r_rob_entry_count <= 'h0;
    end else begin
      if (rn_front_if.valid & rn_front_if.ready) begin
        r_rn_front_if_count      <= r_rn_front_if_count + 'h1;
        r_rn_front_if_inst_count <= r_rn_front_if_inst_count + $countones(w_disp_grp_id);
      end

      if (|w_entry_valids) begin
        if (&w_entry_valids) begin
          r_rob_max_period  <= r_rob_max_period + 'h1;
        end
        r_rob_entry_count <= r_rob_entry_count + $countones(w_entry_valids);
      end

      if (w_out_valid) begin
        r_commit_count <= r_commit_count + 'h1;
        r_inst_count   <= r_inst_count + $countones(w_commit_if.payload.grp_id & ~w_commit_if.payload.dead_id);
        r_dead_count   <= r_dead_count + $countones(w_commit_if.payload.grp_id &  w_commit_if.payload.dead_id);
        for (int grp_idx = 0; grp_idx < scariv_conf_pkg::DISP_SIZE; grp_idx++) begin
          if ((w_commit_if.payload.grp_id & w_commit_if.payload.dead_id >> grp_idx) & 'h1) begin
            case (w_out_entry.sim_dead_reason[grp_idx])
              DEAD_EXC          : r_dead_reason_count.dead_exc          = r_dead_reason_count.dead_exc          + 'h1;
              DEAD_BRANCH       : r_dead_reason_count.dead_branch       = r_dead_reason_count.dead_branch       + 'h1;
              DEAD_PREVINST     : r_dead_reason_count.dead_previnst     = r_dead_reason_count.dead_previnst     + 'h1;
              DEAD_ANOTHERFLUSH : r_dead_reason_count.dead_anotherflush = r_dead_reason_count.dead_anotherflush + 'h1;
              DEAD_EXT_KILL     : r_dead_reason_count.dead_ext_kill     = r_dead_reason_count.dead_ext_kill     + 'h1;
              default           : ;
            endcase // case (w_commit.dead_reason[grp_idx])
          end
        end // for (int grp_idx = 0; grp_idx < scariv_conf_pkg::DISP_SIZE; grp_idx++)
      end // if (w_out_valid)
    end // else: !if(r_cycle_count % sim_pkg::COUNT_UNIT == sim_pkg::COUNT_UNIT-1)
  end // else: !if(!i_reset_n)
end // always_ff @ (negedge i_clk, negedge i_reset_n)



function void dump_perf (int fp);
  $fwrite(fp, "  \"dispatch\" : {");
  $fwrite(fp, "  \"count\" : %5d, ", r_rn_front_if_count);
  $fwrite(fp, "  \"inst\" : %5d},\n", r_rn_front_if_inst_count);

  $fwrite(fp, "  \"rob_entry\" : {");
  $fwrite(fp, "  \"max_period\" : %5d, ", r_rob_max_period);
  $fwrite(fp, "  \"average count\" : %5f},\n", r_rob_entry_count / 1000.0);

  $fwrite(fp, "  \"commit\" : {");
  $fwrite(fp, "  \"cmt\" : %5d, ", r_commit_count);
  $fwrite(fp, "  \"inst\" : %5d, ", r_inst_count);
  $fwrite(fp, "  \"dead\" : %5d,\n  ", r_dead_count);
  $fwrite(fp, "  \"reason\" : {");
  $fwrite(fp, "  \"exc\" : %5d, "       , r_dead_reason_count.dead_exc);
  $fwrite(fp, "  \"branch\" : %5d, "      , r_dead_reason_count.dead_branch);
  $fwrite(fp, "  \"previnst\" : %5d, "    , r_dead_reason_count.dead_previnst);
  $fwrite(fp, "  \"anotherflush\" : %5d, ", r_dead_reason_count.dead_anotherflush);
  $fwrite(fp, "  \"ext_kill\" : %5d"    , r_dead_reason_count.dead_ext_kill);
  $fwrite(fp, "  }},\n");
endfunction

import "DPI-C" function void retire_inst
(
 input longint id,
 input longint retire_id,
 input int     retire
);
import "DPI-C" function void log_stage
(
 input longint id,
 input string stage
);

always_ff @ (negedge i_clk, negedge i_reset_n) begin
  if (i_reset_n) begin
    if (w_out_valid) begin
      for (int i = 0; i < scariv_conf_pkg::DISP_SIZE; i++) begin
        if (w_out_entry.grp_id[i]) begin
          log_stage (w_out_payload.disp[i].kanata_id, "CMT");
        end
      end
    end
  end
end

rob_entry_t   r_out_entry_d1;
rob_payload_t r_out_payload_d1;
logic r_commit_d1;
logic [DISP_SIZE-1:0] r_dead_grp_d1;

always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_commit_d1    <= 1'b0;
    r_out_entry_d1 <= 'h0;
    r_out_payload_d1 <= 'h0;
    r_dead_grp_d1  <= 'h0;
  end else begin
    r_commit_d1 <= w_out_valid;
    r_out_entry_d1 <= w_out_entry;
    r_out_payload_d1 <= w_out_payload;
    r_dead_grp_d1  <= w_dead_grp_id;
  end
end

logic [63: 0] kanata_retire_id;

always_ff @ (negedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    kanata_retire_id = 'h0;
  end else begin
    if (r_commit_d1) begin
      for (int i = 0; i < scariv_conf_pkg::DISP_SIZE; i++) begin
        if (r_out_entry_d1.grp_id[i]) begin
          retire_inst (r_out_payload_d1.disp[i].kanata_id, kanata_retire_id,
                       r_out_entry_d1.dead[i] | r_dead_grp_d1[i]);
          if (!(r_out_entry_d1.dead[i] | r_dead_grp_d1[i])) begin
            kanata_retire_id = kanata_retire_id + 1;
          end
        end
      end
    end
  end
end // always_ff @ (negedge i_clk, negedge i_reset_n)


`endif // MONITOR
`endif // SIMULATION

`ifdef NATIVE_DUMP
integer native_dump_fp;
initial begin
  native_dump_fp = $fopen("native_dump.txt", "w");
end

logic [riscv_pkg::XLEN_W-1: 0] w_physical_int_data [scariv_pkg::XPR_RNID_SIZE + 32];
logic [riscv_pkg::FLEN_W-1: 0] w_physical_fp_data  [scariv_pkg::FPR_RNID_SIZE + 32];
generate for (genvar r_idx = 0; r_idx < scariv_pkg::XPR_RNID_SIZE; r_idx++) begin: reg_loop
`ifdef NORMAL_MULTIPORT
  assign w_physical_int_data[r_idx] = u_scariv_subsystem.u_tile.u_int_phy_registers.r_phy_regs[r_idx];
`else  // NORMAL_MULTIPORT
  assign w_physical_int_data[r_idx] = u_scariv_subsystem.u_tile.u_int_phy_registers.sim_phy_regs[r_idx];
`endif // IVT_MULTIPORT
end endgenerate
generate if (riscv_pkg::FLEN_W != 0) begin
  for (genvar r_idx = 0; r_idx < scariv_pkg::FPR_RNID_SIZE; r_idx++) begin: reg_loop
`ifdef NORMAL_MULTIPORT
    assign w_physical_fp_data [r_idx] = u_scariv_subsystem.u_tile.fpu.u_fp_phy_registers.r_phy_regs[r_idx];
`else // IVT_MULTIPORT
    assign w_physical_fp_data [r_idx] = u_scariv_subsystem.u_tile.fpu.u_fp_phy_registers.sim_phy_regs[r_idx];
`endif // IVT_MULTIPORT
  end
end endgenerate

always_ff @ (negedge i_clk) begin
  for (int grp_idx = 0; grp_idx < scariv_pkg::DISP_SIZE; grp_idx++) begin
    if (w_out_valid &
        w_commit.grp_id[grp_idx] &
        ~w_commit.dead_id[grp_idx]) begin
      /* verilator lint_off WIDTH */
      $fwrite(native_dump_fp, "%t PC=%08x: INST=0x%08x, DASM(0x%08x) | ",
              $time,
              w_out_payload.disp[grp_idx].pc_addr,
              w_out_payload.disp[grp_idx].inst,
              w_out_payload.disp[grp_idx].inst);
      if (w_out_payload.disp[grp_idx].wr_reg.valid) begin
        $fwrite (native_dump_fp, "x%02d(%d)<=%016x",
                 w_out_payload.disp[grp_idx].wr_reg.regidx,
                 w_out_payload.disp[grp_idx].wr_reg.rnid,
                 w_physical_int_data[w_out_payload.disp[grp_idx].wr_reg.rnid]);
      end
      if (w_commit.except_valid[grp_idx]) begin
        $fwrite(native_dump_fp, "Exception, Type=%d\n", w_commit.except_type);
      end else begin
        $fwrite(native_dump_fp, "\n");
      end
    end
  end // for (int grp_idx = 0; grp_idx < scariv_pkg::DISP_SIZE; grp_idx++)
end // always_ff @ (negedge i_clk)

`endif //  `ifdef NATIVE_DUMP

`ifdef ILA_DEBUG

always_ff @ (posedge i_clk) begin
  o_ila_debug_rob.head_ptr <= w_in_cmt_id;
  o_ila_debug_rob.tail_ptr <= w_out_cmt_id;
  o_ila_debug_rob.entry    <= w_out_entry;
  o_ila_debug_rob.payload  <= w_out_payload;
end

`endif // ILA_DEBUG


endmodule // scariv_rob
