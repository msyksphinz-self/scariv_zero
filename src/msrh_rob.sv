module msrh_rob
  import msrh_conf_pkg::*;
  import msrh_pkg::*;
(
   input logic                   i_clk,
   input logic                   i_reset_n,

   disp_if.slave                 sc_disp,

   cre_ret_if.slave              cre_ret_if,

   output logic [CMT_ID_W-1: 0] o_sc_new_cmt_id,

   input done_rpt_t i_done_rpt [CMT_BUS_SIZE],
   br_upd_if.slave  ex3_br_upd_if,

   output commit_blk_t o_commit,
   output cmt_rnid_upd_t o_commit_rnid_update,

   // Branch Tag Update Signal
   cmt_brtag_if.master cmt_brtag_if,

   // ROB notification interface
   rob_info_if.master rob_info_if
   );

rob_entry_t              w_entries[CMT_ENTRY_SIZE];
logic [CMT_ID_W-1:0]     w_in_cmt_id, w_out_cmt_id;
logic [DISP_SIZE-1:0]              w_disp_grp_id;
logic [CMT_ENTRY_SIZE-1:0]         w_entry_all_done;
logic [DISP_SIZE-1:0]              w_br_upd_valid_oh;
logic [riscv_pkg::VADDR_W-1: 0]    w_upd_br_vaddr;
logic [DISP_SIZE-1:0]              w_dead_grp_id_br_tmp;
logic [DISP_SIZE-1:0]              w_dead_grp_id_except_tmp;
logic [DISP_SIZE-1:0]              w_dead_grp_id;

logic [DISP_SIZE-1: 0] w_cmt_except_valid_oh;
logic [$clog2(CMT_ENTRY_SIZE)-1: 0] w_cmt_except_valid_encoded;
except_t                            w_except_type_selected;
logic [riscv_pkg::XLEN_W-1: 0]      w_except_tval_selected;

logic                                w_ignore_disp;
logic [$clog2(CMT_ENTRY_SIZE): 0]    w_credit_return_val;

// When this signal is 1, committer is killing uncommitted instructions
logic                              r_killing_uncmts;
logic                              w_killing_uncmts;

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
logic [DISP_SIZE-1: 0]              w_valid_branch_grp_id;

assign w_out_cmt_entry_id = w_out_cmt_id[CMT_ENTRY_W-1:0];
assign w_in_cmt_entry_id  = w_in_cmt_id [CMT_ENTRY_W-1:0];

assign w_in_valid  = sc_disp.valid;
assign w_out_valid = w_entry_all_done[w_out_cmt_entry_id] | w_killing_uncmts;

logic                                      w_flush_valid;
assign w_flush_valid = o_commit.commit & o_commit.flush_valid & !o_commit.all_dead;

inoutptr #(.SIZE(CMT_ID_SIZE)) u_cmt_ptr(.i_clk (i_clk), .i_reset_n(i_reset_n),
                                         .i_clear (1'b0),
                                         .i_in_valid (w_in_valid ), .o_in_ptr (w_in_cmt_id  ),
                                         .i_out_valid(w_out_valid), .o_out_ptr(w_out_cmt_id));

assign sc_disp.ready = 1'b1;
assign w_ignore_disp = w_flush_valid & (sc_disp.valid & sc_disp.ready);
assign w_credit_return_val = (o_commit.commit ? 'h1 : 'h0) /* +
                             (w_ignore_disp   ? 'h1 : 'h0) */ ;

msrh_credit_return_slave
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
logic [riscv_pkg::XLEN_W-1: 0] w_sim_mstatus[CMT_ENTRY_SIZE][msrh_conf_pkg::DISP_SIZE];
`endif // SIMULATION

generate for (genvar c_idx = 0; c_idx < CMT_ENTRY_SIZE; c_idx++) begin : entry_loop
logic w_load_valid;
  assign w_load_valid = sc_disp.valid & (w_in_cmt_entry_id == c_idx);

  msrh_rob_entry u_entry
    (
     .i_clk (i_clk),
     .i_reset_n (i_reset_n),

     .i_cmt_id (c_idx[CMT_ENTRY_W-1:0]),

     .i_load_valid   (w_load_valid),
     .i_load_pc_addr (sc_disp.pc_addr),
     .i_load_inst    (sc_disp.inst),
     .i_load_grp_id  (w_disp_grp_id),
     .i_load_br_included (sc_disp.is_br_included),
     .i_load_tlb_except_valid (sc_disp.tlb_except_valid),
     .i_load_tlb_except_cause (sc_disp.tlb_except_cause),

     .i_done_rpt (i_done_rpt),

     .o_entry          (w_entries[c_idx]),
     .o_block_all_done (w_entry_all_done[c_idx]),
     .i_commit_finish  ((w_entry_all_done[c_idx] | r_killing_uncmts) &
                        (w_out_cmt_entry_id == c_idx)),

     .i_kill (w_flush_valid),

     .br_upd_if (ex3_br_upd_if)
     );

`ifdef SIMULATION
  for (genvar d = 0; d < msrh_conf_pkg::DISP_SIZE; d++) begin
    assign w_sim_mstatus[c_idx][d] = u_entry.r_mstatus[d];
  end
`endif // SIMULATION

end
endgenerate

assign o_sc_new_cmt_id = w_in_cmt_id;

assign w_killing_uncmts = r_killing_uncmts &
                          w_entries[w_out_cmt_entry_id].valid &
                          w_entries[w_out_cmt_entry_id].dead;

assign o_commit.commit       = w_entry_all_done[w_out_cmt_entry_id] | w_killing_uncmts;
assign o_commit.cmt_id       = w_out_cmt_id;
assign o_commit.grp_id       = w_entries[w_out_cmt_entry_id].done_grp_id;
assign o_commit.upd_pc_valid   = |((w_entries[w_out_cmt_entry_id].br_upd_info.upd_valid |
                                    w_entries[w_out_cmt_entry_id].except_valid) &
                                   w_entries[w_out_cmt_entry_id].grp_id);
assign o_commit.upd_pc_vaddr = w_upd_br_vaddr;
assign o_commit.flush_valid   = o_commit.upd_pc_valid;
assign o_commit.except_valid  = w_valid_except_grp_id;
assign o_commit.except_type   = w_except_type_selected;
/* verilator lint_off WIDTH */
assign o_commit.tval          = (o_commit.except_type == msrh_pkg::INST_ADDR_MISALIGN  ||
                                 o_commit.except_type == msrh_pkg::INST_ACC_FAULT      ||
                                 o_commit.except_type == msrh_pkg::INST_PAGE_FAULT) ? {w_entries[w_out_cmt_entry_id].pc_addr, 1'b0} + {w_cmt_except_valid_encoded, 2'b00}:
                                w_except_tval_selected;
encoder #(.SIZE(CMT_ENTRY_SIZE)) except_pc_vaddr (.i_in (w_valid_except_grp_id), .o_out(w_cmt_except_valid_encoded));
/* verilator lint_off WIDTH */
assign o_commit.epc          = {w_entries[w_out_cmt_entry_id].pc_addr, 1'b0} + {w_cmt_except_valid_encoded, 2'b00};
assign o_commit.dead_id      = w_dead_grp_id & o_commit.grp_id;
assign o_commit.all_dead     = w_entries[w_out_cmt_entry_id].dead;

// Select Jump Insntruction
assign w_valid_upd_pc_grp_id = (w_entries[w_out_cmt_entry_id].br_upd_info.upd_valid |
                                w_entries[w_out_cmt_entry_id].except_valid) & w_entries[w_out_cmt_entry_id].done_grp_id;
bit_extract_lsb #(.WIDTH(DISP_SIZE)) u_bit_pc_upd_valid (.in(w_valid_upd_pc_grp_id), .out(w_cmt_pc_upd_valid_oh));

// Select Exception Instruction
assign w_valid_except_grp_id = w_entries[w_out_cmt_entry_id].except_valid & w_cmt_pc_upd_valid_oh;
bit_oh_or_packed #(.T(except_t), .WORDS(DISP_SIZE)) u_bit_except_select (.i_oh(w_valid_except_grp_id), .i_data(w_entries[w_out_cmt_entry_id].except_type), .o_selected(w_except_type_selected));
// logic [riscv_pkg::XLEN_W-1: 0] except_tval_packed[DISP_SIZE];
// generate for (genvar d_idx = 0; d_idx < DISP_SIZE; d_idx++) begin : except_tval_loop
//   assign except_tval_packed[d_idx] = w_entries[w_out_cmt_entry_id].except_tval[d_idx];
// end
// endgenerate
bit_oh_or_packed #(.T(logic[riscv_pkg::XLEN_W-1:0]), .WORDS(DISP_SIZE)) u_bit_except_tval_select (.i_oh(w_valid_except_grp_id), .i_data(w_entries[w_out_cmt_entry_id].except_tval), .o_selected(w_except_tval_selected));


// Select Branch Target Address
assign w_valid_branch_grp_id = w_entries[w_out_cmt_entry_id].br_upd_info.upd_valid & w_cmt_pc_upd_valid_oh;
bit_oh_or_packed #(.T(logic[riscv_pkg::VADDR_W-1:0]), .WORDS(DISP_SIZE))
br_sel_addr (.i_oh(w_valid_branch_grp_id),
             .i_data(w_entries[w_out_cmt_entry_id].br_upd_info.upd_br_vaddr),
             .o_selected(w_upd_br_vaddr));

assign o_commit_rnid_update.commit     = o_commit.commit;
generate for (genvar d_idx = 0; d_idx < DISP_SIZE; d_idx++) begin : commit_rd_loop
  assign o_commit_rnid_update.rnid_valid[d_idx] = w_entries[w_out_cmt_entry_id].inst[d_idx].rd_valid;
  assign o_commit_rnid_update.old_rnid  [d_idx] = w_entries[w_out_cmt_entry_id].inst[d_idx].rd_old_rnid;
  assign o_commit_rnid_update.rd_rnid   [d_idx] = w_entries[w_out_cmt_entry_id].inst[d_idx].rd_rnid;
  assign o_commit_rnid_update.rd_regidx [d_idx] = w_entries[w_out_cmt_entry_id].inst[d_idx].rd_regidx;
end
endgenerate
assign o_commit_rnid_update.is_br_included = w_entries[w_out_cmt_entry_id].is_br_included;
assign o_commit_rnid_update.upd_pc_valid   = o_commit.upd_pc_valid & !o_commit.all_dead;
assign o_commit_rnid_update.dead_id        = w_dead_grp_id;
assign o_commit_rnid_update.all_dead       = w_killing_uncmts;
assign o_commit_rnid_update.except_valid   = o_commit.except_valid;
assign o_commit_rnid_update.except_type    = o_commit.except_type;


// Make dead Instruction, (after branch instruction)
bit_tree_lsb #(.WIDTH(DISP_SIZE)) u_bit_dead_br_grp_id (.in(w_entries[w_out_cmt_entry_id].br_upd_info.upd_valid), .out(w_dead_grp_id_br_tmp));

// Make dead Instruction, (after exception)
bit_tree_lsb #(.WIDTH(DISP_SIZE)) u_bit_dead_except_grp_id (.in(w_entries[w_out_cmt_entry_id].except_valid), .out(w_dead_grp_id_except_tmp));
logic [DISP_SIZE-1: 0] w_except_dead_grp_id;
logic                  w_is_active_except;   // Instruction generates exception but itself active
// assign w_is_active_except = (w_except_type_selected == msrh_pkg::SILENT_FLUSH) |
//                             (w_except_type_selected == msrh_pkg::ECALL_U)      |
//                             (w_except_type_selected == msrh_pkg::ECALL_S)      |
//                             (w_except_type_selected == msrh_pkg::ECALL_M)      |
//                             (w_except_type_selected == msrh_pkg::URET)         |
//                             (w_except_type_selected == msrh_pkg::SRET)         |
//                             (w_except_type_selected == msrh_pkg::MRET)         |
//                             1'b0;
assign w_is_active_except = 1'b1;

assign w_except_dead_grp_id = w_is_active_except ?  // active flush itself doesn't include dead instruction
                              {w_dead_grp_id_except_tmp[DISP_SIZE-2: 0], 1'b0} :  // so, 1-bit left shift
                              w_dead_grp_id_except_tmp;                           // otherwise, except itself includes dead instruction
assign w_dead_grp_id = w_except_dead_grp_id |
                       {w_dead_grp_id_br_tmp[DISP_SIZE-2: 0], 1'b0} ;   // branch: 1-bit left shift

// Killing all uncommitted instructions
always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_killing_uncmts <= 1'b0;
  end else begin
    if (o_commit.commit & o_commit.flush_valid & (w_in_cmt_id != w_out_cmt_id)) begin
      r_killing_uncmts <= 1'b1;
    end else if (r_killing_uncmts & !w_entries[w_out_cmt_entry_id].dead) begin
      r_killing_uncmts <= 1'b0;
    end
  end
end

// ROB Notification Information
assign rob_info_if.cmt_id       = w_out_cmt_id;
assign rob_info_if.grp_id       = w_entries[w_out_cmt_entry_id].grp_id;
assign rob_info_if.done_grp_id  = w_entries[w_out_cmt_entry_id].done_grp_id;
assign rob_info_if.upd_pc_valid = w_entries[w_out_cmt_entry_id].br_upd_info.upd_valid;
assign rob_info_if.except_valid = w_entries[w_out_cmt_entry_id].except_valid;

// Commit Branch Tag Update
assign cmt_brtag_if.commit     = o_commit.commit;
generate for (genvar d_idx = 0; d_idx < DISP_SIZE; d_idx++) begin : brtag_loop
  assign cmt_brtag_if.is_br_inst[d_idx] = w_entries[w_out_cmt_entry_id].inst[d_idx].cat == decoder_inst_cat_pkg::INST_CAT_BR;
  assign cmt_brtag_if.brtag     [d_idx] = w_entries[w_out_cmt_entry_id].inst[d_idx].brtag;
end
endgenerate


`ifdef SIMULATION
logic [CMT_ENTRY_SIZE-1: 0] w_entry_valids;
generate for (genvar c_idx = 0; c_idx < CMT_ENTRY_SIZE; c_idx++) begin : dbg_entry_loop
  assign w_entry_valids[c_idx] = w_entries[c_idx].valid;
end
endgenerate

function void dump_entry_json(int fp, rob_entry_t entry, int index);

  if (entry.valid) begin
    $fwrite(fp, "    \"msrh_rob_entry[%d]\" : {", index[$clog2(CMT_ENTRY_SIZE)-1:0]);
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
    $fwrite(fp, "  \"msrh_rob\" : {\n");
    $fwrite(fp, "    in_cmt_id: %d,\n", w_in_cmt_id);
    $fwrite(fp, "    out_cmt_id: %d,\n", w_out_cmt_id);
    $fwrite(fp, "    killing: %d,\n", w_killing_uncmts);
    for (int c_idx = 0; c_idx < CMT_ENTRY_SIZE; c_idx++) begin
      dump_entry_json (fp, w_entries[c_idx], c_idx);
    end
    $fwrite(fp, "  },\n");
  end
endfunction // dump_json
`endif // SIMULATION

endmodule // msrh_rob
