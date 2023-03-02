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

   disp_if.slave                 sc_disp,

   cre_ret_if.slave              cre_ret_if,

   output cmt_id_t o_sc_new_cmt_id,

   input done_rpt_t      i_done_rpt             [CMT_BUS_SIZE],
   input another_flush_t i_another_flush_report [LSU_INST_NUM],

   br_upd_if.slave  ex3_br_upd_if,

   output commit_blk_t     o_commit,
   fflags_update_if.master fflags_update_if,
   output cmt_rnid_upd_t   o_commit_rnid_update,

   // Interrupt Request information
   interrupt_if.slave  int_if,

   // Branch Tag Update Signal
   cmt_brtag_if.master cmt_brtag_if,

   // ROB notification interface
   rob_info_if.master rob_info_if
   );

rob_entry_t              w_entries[CMT_ENTRY_SIZE];
cmt_id_t     w_in_cmt_id, w_out_cmt_id;
logic [DISP_SIZE-1:0]              w_disp_grp_id;
logic [CMT_ENTRY_SIZE-1:0]         w_entry_all_done;
logic [DISP_SIZE-1:0]              w_br_upd_valid_oh;
// scariv_pkg::vaddr_t    w_upd_br_vaddr;
logic [DISP_SIZE-1:0]              w_dead_grp_id_br_tmp;
logic [DISP_SIZE-1:0]              w_dead_grp_id_except_tmp;
logic [DISP_SIZE-1:0]              w_dead_grp_id;

logic [$clog2(CMT_ENTRY_SIZE)-1: 0] w_cmt_except_valid_encoded;
except_t                            w_except_type_selected;
riscv_pkg::xlen_t      w_except_tval_selected;

logic                                w_ignore_disp;
logic [$clog2(CMT_ENTRY_SIZE): 0]    w_credit_return_val;

//
// Pointer
//
logic                                      w_in_valid, w_out_valid;
logic [CMT_ENTRY_W-1:0]                    w_out_cmt_entry_id;
logic [CMT_ENTRY_W-1:0]                    w_in_cmt_entry_id;

// Commiter Selection
logic [DISP_SIZE-1: 0]              w_valid_upd_pc_grp_id;
logic [DISP_SIZE-1: 0]              w_cmt_pc_upd_valid_oh;
logic [DISP_SIZE-1: 0]              w_valid_except_grp_id;
// logic [DISP_SIZE-1: 0]              w_valid_branch_grp_id;

assign w_out_cmt_entry_id = w_out_cmt_id[CMT_ENTRY_W-1:0];
assign w_in_cmt_entry_id  = w_in_cmt_id [CMT_ENTRY_W-1:0];

assign w_in_valid  = sc_disp.valid;
assign w_out_valid = w_entry_all_done[w_out_cmt_entry_id];

logic                                      w_flush_valid;
assign w_flush_valid = scariv_pkg::is_flushed_commit(o_commit);

inoutptr #(.SIZE(CMT_ID_SIZE)) u_cmt_ptr(.i_clk (i_clk), .i_reset_n(i_reset_n),
                                         .i_clear (1'b0),
                                         .i_in_valid (w_in_valid ), .o_in_ptr (w_in_cmt_id  ),
                                         .i_out_valid(w_out_valid), .o_out_ptr(w_out_cmt_id));

assign sc_disp.ready = 1'b1;
assign w_ignore_disp = w_flush_valid & (sc_disp.valid & sc_disp.ready);
assign w_credit_return_val = (o_commit.commit ? 'h1 : 'h0) /* +
                             (w_ignore_disp   ? 'h1 : 'h0) */ ;

scariv_credit_return_slave
  #(.MAX_CREDITS(CMT_ENTRY_SIZE))
u_credit_return_slave
(
 .i_clk(i_clk),
 .i_reset_n(i_reset_n),

 .i_get_return(o_commit.commit | w_ignore_disp),
 .i_return_val(w_credit_return_val),

 .cre_ret_if (cre_ret_if)
 );

generate for (genvar d_idx = 0; d_idx < DISP_SIZE; d_idx++) begin : disp_loop
  assign w_disp_grp_id[d_idx] = sc_disp.inst[d_idx].valid;
end
endgenerate

`ifdef SIMULATION
riscv_pkg::xlen_t w_sim_mstatus[CMT_ENTRY_SIZE][scariv_conf_pkg::DISP_SIZE];
`endif // SIMULATION

function automatic rob_entry_t assign_rob_entry();
  rob_entry_t ret;

  ret.valid       = 1'b1;
  ret.dead        = w_disp_grp_id & {scariv_conf_pkg::DISP_SIZE{w_flush_valid}};
  ret.grp_id      = w_disp_grp_id;
  ret.pc_addr     = sc_disp.pc_addr;
  for (int d_idx = 0; d_idx < scariv_conf_pkg::DISP_SIZE; d_idx++) begin : inst_loop
    ret.inst[d_idx].valid          = sc_disp.inst[d_idx].valid         ;
    ret.inst[d_idx].pc_addr        = sc_disp.inst[d_idx].pc_addr       ;
    ret.inst[d_idx].br_mask        = sc_disp.inst[d_idx].br_mask       ;
    ret.inst[d_idx].cat            = sc_disp.inst[d_idx].cat           ;
    ret.inst[d_idx].brtag          = sc_disp.inst[d_idx].brtag         ;
    ret.inst[d_idx].wr_reg         = sc_disp.inst[d_idx].wr_reg        ;
    ret.inst[d_idx].ras_index      = sc_disp.inst[d_idx].ras_index     ;
    ret.inst[d_idx].is_call        = sc_disp.inst[d_idx].is_call       ;
    ret.inst[d_idx].is_ret         = sc_disp.inst[d_idx].is_ret        ;
`ifdef SIMULATION
    ret.inst[d_idx].rvc_inst_valid = sc_disp.inst[d_idx].rvc_inst_valid;
    ret.inst[d_idx].rvc_inst       = sc_disp.inst[d_idx].rvc_inst      ;
    ret.inst[d_idx].inst           = sc_disp.inst[d_idx].inst          ;
    ret.inst[d_idx].kanata_id      = sc_disp.inst[d_idx].kanata_id     ;
`endif // SIMULATION
  end // block: inst_loop

  ret.br_upd_info = 'h0;
  ret.fflags_update_valid = 'h0;

  ret.is_br_included = sc_disp.is_br_included;

  ret.int_inserted = sc_disp.int_inserted;

  for (int d_idx = 0; d_idx < scariv_conf_pkg::DISP_SIZE; d_idx++) begin : disp_loop
    // If TLB Exception detected before execution, this instruction already done.
    ret.done_grp_id [d_idx] = (sc_disp.tlb_except_valid[d_idx] | sc_disp.inst[d_idx].illegal_valid) ? w_disp_grp_id[d_idx] : 1'b0;
    ret.except_valid[d_idx] = (sc_disp.tlb_except_valid[d_idx] | sc_disp.inst[d_idx].illegal_valid) & w_disp_grp_id[d_idx];
    ret.except_type [d_idx] = sc_disp.tlb_except_valid[d_idx] ? sc_disp.tlb_except_cause[d_idx] : ILLEGAL_INST;
    ret.except_tval [d_idx] = sc_disp.tlb_except_valid[d_idx] & (sc_disp.tlb_except_cause[d_idx] != ILLEGAL_INST) ? sc_disp.tlb_except_tval[d_idx] : 'h0;
    ret.flush_valid [d_idx] = ret.dead[d_idx] ? 1'b0 : ret.except_valid[d_idx];
    ret.dead        [d_idx] = ret.dead[d_idx] | ret.except_valid[d_idx];
`ifdef SIMULATION
    ret.sim_dead_reason[d_idx] = ret.except_valid[d_idx] ? DEAD_EXC : DEAD_NONE;
`endif // SIMULATION
  end

  return ret;

endfunction // assign_rob_entry


rob_entry_t w_entry_in;
assign w_entry_in = assign_rob_entry();


generate for (genvar c_idx = 0; c_idx < CMT_ENTRY_SIZE; c_idx++) begin : entry_loop
logic w_load_valid;
  assign w_load_valid = sc_disp.valid & (w_in_cmt_entry_id == c_idx);

  scariv_rob_entry u_entry
    (
     .i_clk (i_clk),
     .i_reset_n (i_reset_n),

     .i_cmt_id (c_idx[CMT_ENTRY_W-1:0]),

     .i_load_valid (w_load_valid),
     .i_entry_in   (w_entry_in),

     .i_done_rpt             (i_done_rpt),
     .i_another_flush_report (i_another_flush_report),

     .o_entry          (w_entries[c_idx]),
     .o_block_all_done (w_entry_all_done[c_idx]),
     .i_commit_finish  (w_entry_all_done[c_idx] &
                        (w_out_cmt_entry_id == c_idx)),

     .i_kill (w_flush_valid),

     .br_upd_if (ex3_br_upd_if)
     );

`ifdef SIMULATION
  for (genvar d = 0; d < scariv_conf_pkg::DISP_SIZE; d++) begin
    assign w_sim_mstatus[c_idx][d] = u_entry.r_mstatus[d];
  end
`endif // SIMULATION

end
endgenerate

assign o_sc_new_cmt_id = w_in_cmt_id;

rob_entry_t w_out_entry;
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

assign o_commit.commit       = w_entry_all_done[w_out_cmt_entry_id];
assign o_commit.cmt_id       = w_out_cmt_id;
assign o_commit.grp_id       = w_out_entry.grp_id;
assign o_commit.except_valid = w_valid_except_grp_id | w_int_valid;
assign o_commit.int_valid    = w_int_valid;
assign o_commit.except_type  = w_int_valid ? except_t'(w_int_type) : except_t'(w_except_type_selected);
/* verilator lint_off WIDTH */
assign o_commit.tval          = (o_commit.except_type == scariv_pkg::INST_ADDR_MISALIGN  ||
                                 o_commit.except_type == scariv_pkg::INST_ACC_FAULT) ? {w_out_entry.pc_addr, 1'b0} + {w_cmt_except_valid_encoded, 2'b00} :
                                w_except_tval_selected;
encoder #(.SIZE(CMT_ENTRY_SIZE)) except_pc_vaddr (.i_in (w_valid_except_grp_id), .o_out(w_cmt_except_valid_encoded));
/* verilator lint_off WIDTH */
assign o_commit.epc          = w_out_entry.inst[w_cmt_except_valid_encoded].pc_addr;
assign o_commit.dead_id      = (w_out_entry.dead | w_dead_grp_id) & o_commit.grp_id;
assign o_commit.flush_valid  = w_out_entry.flush_valid | w_int_valid;

generate for (genvar d_idx = 0; d_idx < DISP_SIZE; d_idx++) begin : commit_ras_loop
  assign o_commit.ras_index [d_idx] = w_out_entry.inst[d_idx].ras_index;
  assign o_commit.ras_update[d_idx] = w_out_entry.inst[d_idx].is_call | w_out_entry.inst[d_idx].is_ret;
end
endgenerate

`ifdef SIMULATION

import "DPI-C" function void spike_update_timer (longint value);

always_ff @ (negedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
  end else begin
    if (o_commit.commit & w_out_entry.int_inserted) begin
      spike_update_timer (u_scariv_subsystem_wrapper.u_scariv_subsystem.u_clint.w_mtime_next);
    end
  end
end
`endif // SIMULATION

// Select Jump Insntruction
assign w_valid_upd_pc_grp_id = (w_out_entry.br_upd_info.upd_valid |
                                w_out_entry.except_valid) /* & w_out_entry.done_grp_id */;
bit_extract_lsb #(.WIDTH(DISP_SIZE)) u_bit_pc_upd_valid (.in(w_valid_upd_pc_grp_id), .out(w_cmt_pc_upd_valid_oh));

// Select Exception Instruction
assign w_valid_except_grp_id = w_out_entry.except_valid & w_cmt_pc_upd_valid_oh;
bit_oh_or_packed #(.T(except_t), .WORDS(DISP_SIZE)) u_bit_except_select (.i_oh(w_valid_except_grp_id), .i_data(w_out_entry.except_type), .o_selected(w_except_type_selected));
bit_oh_or_packed #(.T(riscv_pkg::xlen_t), .WORDS(DISP_SIZE)) u_bit_except_tval_select (.i_oh(w_valid_except_grp_id), .i_data(w_out_entry.except_tval), .o_selected(w_except_tval_selected));

assign o_commit_rnid_update.commit     = o_commit.commit;
generate for (genvar d_idx = 0; d_idx < DISP_SIZE; d_idx++) begin : commit_rd_loop
  assign o_commit_rnid_update.rnid_valid[d_idx] = w_out_entry.inst[d_idx].wr_reg.valid;
  assign o_commit_rnid_update.old_rnid  [d_idx] = w_out_entry.inst[d_idx].wr_reg.old_rnid;
  assign o_commit_rnid_update.rd_rnid   [d_idx] = w_out_entry.inst[d_idx].wr_reg.rnid;
  assign o_commit_rnid_update.rd_regidx [d_idx] = w_out_entry.inst[d_idx].wr_reg.regidx;
  assign o_commit_rnid_update.rd_typ    [d_idx] = w_out_entry.inst[d_idx].wr_reg.typ;
end
endgenerate
assign o_commit_rnid_update.dead_id        = o_commit.dead_id;
assign o_commit_rnid_update.except_valid   = o_commit.except_valid;
assign o_commit_rnid_update.except_type    = o_commit.except_type;


grp_id_t w_fflags_update_valid_oh;
fflags_t w_fflags_sel;
bit_extract_msb  #(.WIDTH(DISP_SIZE)) u_bit_fflags_extract (.in(w_out_entry.fflags_update_valid), .out(w_fflags_update_valid_oh));
bit_oh_or_packed #(.T(fflags_t), .WORDS(DISP_SIZE)) u_bit_fflags_select (.i_oh(w_fflags_update_valid_oh), .i_data(w_out_entry.fflags), .o_selected(w_fflags_sel));

// --------------------------
// FFLAGS update when commit
// --------------------------
assign fflags_update_if.valid  = o_commit.commit & (|w_out_entry.fflags_update_valid);
assign fflags_update_if.fflags = w_fflags_sel;

// --------------------------------------------------
// Notification of RAS Recovery by dead instruction
// --------------------------------------------------
grp_id_t w_is_call_array;
grp_id_t w_is_ret_array;
logic [$clog2(scariv_conf_pkg::RAS_ENTRY_SIZE)-1: 0] w_ras_index_array[scariv_conf_pkg::DISP_SIZE];


// Make dead Instruction, (after branch instruction)
bit_tree_lsb #(.WIDTH(DISP_SIZE)) u_bit_dead_br_grp_id (.in(w_out_entry.br_upd_info.upd_valid), .out(w_dead_grp_id_br_tmp));

// Make dead Instruction, (after exception)
bit_tree_lsb #(.WIDTH(DISP_SIZE)) u_bit_dead_except_grp_id (.in(w_out_entry.except_valid), .out(w_dead_grp_id_except_tmp));
logic [DISP_SIZE-1: 0] w_except_dead_grp_id;
logic                  w_is_active_except;   // Instruction generates exception but itself active
// assign w_is_active_except = (w_except_type_selected == scariv_pkg::SILENT_FLUSH) |
//                             (w_except_type_selected == scariv_pkg::ECALL_U)      |
//                             (w_except_type_selected == scariv_pkg::ECALL_S)      |
//                             (w_except_type_selected == scariv_pkg::ECALL_M)      |
//                             (w_except_type_selected == scariv_pkg::URET)         |
//                             (w_except_type_selected == scariv_pkg::SRET)         |
//                             (w_except_type_selected == scariv_pkg::MRET)         |
//                             1'b0;
assign w_is_active_except = 1'b1;

assign w_except_dead_grp_id = w_is_active_except ?  // active flush itself doesn't include dead instruction
                              {w_dead_grp_id_except_tmp[DISP_SIZE-2: 0], 1'b0} :  // so, 1-bit left shift
                              w_dead_grp_id_except_tmp;                           // otherwise, except itself includes dead instruction
assign w_dead_grp_id = w_except_dead_grp_id |
                       {w_dead_grp_id_br_tmp[DISP_SIZE-2: 0], 1'b0} ;   // branch: 1-bit left shift

// Killing all uncommitted instructions
// always_ff @ (posedge i_clk, negedge i_reset_n) begin
//   if (!i_reset_n) begin
//     r_killing_uncmts <= 1'b0;
//   end else begin
//     if (o_commit.commit & (|o_commit.except_valid) & !r_killing_uncmts) begin
//       r_killing_uncmts <= 1'b1;
//     end else if (r_killing_uncmts & !o_commit.commit) begin  // Commit finished
//       r_killing_uncmts <= 1'b0;
//     end
//   end
// end

// ROB Notification Information
assign rob_info_if.cmt_id       = w_out_cmt_id;
assign rob_info_if.grp_id       = w_out_entry.grp_id;
assign rob_info_if.done_grp_id  = w_out_entry.done_grp_id;
assign rob_info_if.upd_pc_valid = w_out_entry.br_upd_info.upd_valid;
assign rob_info_if.except_valid = w_out_entry.except_valid;

// Commit Branch Tag Update
assign cmt_brtag_if.commit     = o_commit.commit;
generate for (genvar d_idx = 0; d_idx < DISP_SIZE; d_idx++) begin : brtag_loop
  assign cmt_brtag_if.is_br_inst[d_idx] = w_out_entry.inst[d_idx].cat == decoder_inst_cat_pkg::INST_CAT_BR;
  assign cmt_brtag_if.brtag     [d_idx] = w_out_entry.inst[d_idx].brtag;
end
endgenerate


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
    $fwrite(fp, "pc_addr:\"0x%0x\", ", entry.pc_addr << 1);

    $fwrite(fp, "grp_id:\"0x%02x\", ", entry.grp_id);
    $fwrite(fp, "done_grp_id:\"0x%02x\", ", entry.done_grp_id);

    $fwrite(fp, "dead:%d, ", entry.dead);
    $fwrite(fp, "except_valid:0x%02x", entry.except_valid);

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
logic [63: 0] r_sc_disp_count;
logic [63: 0] r_sc_disp_inst_count;
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
    r_sc_disp_count <= 'h0;
    r_sc_disp_inst_count <= 'h0;

    r_commit_count <= 'h0;
    r_inst_count   <= 'h0;
    r_dead_count   <= 'h0;
    r_cycle_count  <= 'h0;

    r_rob_max_period  <= 'h0;
    r_rob_entry_count <= 'h0;
  end else begin
    r_cycle_count <= r_cycle_count + 'h1;
    if (r_cycle_count % sim_pkg::COUNT_UNIT == sim_pkg::COUNT_UNIT-1) begin
      r_sc_disp_count <= 'h0;
      r_sc_disp_inst_count <= 'h0;

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
      if (sc_disp.valid & sc_disp.ready) begin
        r_sc_disp_count      <= r_sc_disp_count + 'h1;
        r_sc_disp_inst_count <= r_sc_disp_inst_count + $countones(w_disp_grp_id);
      end

      if (|w_entry_valids) begin
        if (&w_entry_valids) begin
          r_rob_max_period  <= r_rob_max_period + 'h1;
        end
        r_rob_entry_count <= r_rob_entry_count + $countones(w_entry_valids);
      end

      if (o_commit.commit) begin
        r_commit_count <= r_commit_count + 'h1;
        r_inst_count   <= r_inst_count + $countones(o_commit.grp_id & ~o_commit.dead_id);
        r_dead_count   <= r_dead_count + $countones(o_commit.grp_id &  o_commit.dead_id);
        for (int grp_idx = 0; grp_idx < scariv_conf_pkg::DISP_SIZE; grp_idx++) begin
          if ((o_commit.grp_id & o_commit.dead_id >> grp_idx) & 'h1) begin
            case (w_out_entry.sim_dead_reason[grp_idx])
              DEAD_EXC          : r_dead_reason_count.dead_exc          = r_dead_reason_count.dead_exc          + 'h1;
              DEAD_BRANCH       : r_dead_reason_count.dead_branch       = r_dead_reason_count.dead_branch       + 'h1;
              DEAD_PREVINST     : r_dead_reason_count.dead_previnst     = r_dead_reason_count.dead_previnst     + 'h1;
              DEAD_ANOTHERFLUSH : r_dead_reason_count.dead_anotherflush = r_dead_reason_count.dead_anotherflush + 'h1;
              DEAD_EXT_KILL     : r_dead_reason_count.dead_ext_kill     = r_dead_reason_count.dead_ext_kill     + 'h1;
              default           : ;
            endcase // case (o_commit.dead_reason[grp_idx])
          end
        end // for (int grp_idx = 0; grp_idx < scariv_conf_pkg::DISP_SIZE; grp_idx++)
      end // if (o_commit.commit)
    end // else: !if(r_cycle_count % sim_pkg::COUNT_UNIT == sim_pkg::COUNT_UNIT-1)
  end // else: !if(!i_reset_n)
end // always_ff @ (negedge i_clk, negedge i_reset_n)



function void dump_perf (int fp);
  $fwrite(fp, "  \"dispatch\" : {");
  $fwrite(fp, "  \"count\" : %5d, ", r_sc_disp_count);
  $fwrite(fp, "  \"inst\" : %5d},\n", r_sc_disp_inst_count);

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
 input int retire
);
import "DPI-C" function void log_stage
(
 input longint id,
 input string stage
);

always_ff @ (negedge i_clk, negedge i_reset_n) begin
  if (i_reset_n) begin
    if (o_commit.commit) begin
      for (int i = 0; i < scariv_conf_pkg::DISP_SIZE; i++) begin
        if (w_out_entry.grp_id[i]) begin
          log_stage (w_out_entry.inst[i].kanata_id, "CMT");
        end
      end
    end
  end
end

rob_entry_t r_out_entry_d1;
logic r_commit_d1;
logic [DISP_SIZE-1:0] r_dead_grp_d1;

always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_commit_d1    <= 1'b0;
    r_out_entry_d1 <= 'h0;
    r_dead_grp_d1  <= 'h0;
  end else begin
    r_commit_d1 <= o_commit.commit;
    r_out_entry_d1 <= w_out_entry;
    r_dead_grp_d1  <= w_dead_grp_id;
  end
end


always_ff @ (negedge i_clk, negedge i_reset_n) begin
  if (i_reset_n) begin
    if (r_commit_d1) begin
      for (int i = 0; i < scariv_conf_pkg::DISP_SIZE; i++) begin
        if (r_out_entry_d1.grp_id[i]) begin
          retire_inst (r_out_entry_d1.inst[i].kanata_id,
                       r_out_entry_d1.flush_valid[i] | r_out_entry_d1.dead[i] | r_dead_grp_d1[i]);
        end
      end
    end
  end
end // always_ff @ (negedge i_clk, negedge i_reset_n)


`endif // MONITOR
`endif // SIMULATION

endmodule // scariv_rob
