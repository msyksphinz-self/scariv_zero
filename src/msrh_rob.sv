module msrh_rob
  import msrh_conf_pkg::*;
  import msrh_pkg::*;
(
   input logic                   i_clk,
   input logic                   i_reset_n,

   disp_if.watch                 sc_disp,

   output logic [CMT_BLK_W-1: 0] o_sc_new_cmt_id,

   input done_rpt_t i_done_rpt [CMT_BUS_SIZE],
   br_upd_if.slave  ex3_br_upd_if,

   output commit_blk_t o_commit,
   output cmt_rnid_upd_t o_commit_rnid_update
   );

rob_entry_t              w_entries[CMT_BLK_SIZE];
logic [CMT_BLK_W-1:0]    w_in_cmt_id, w_out_cmt_id;
logic [DISP_SIZE-1:0]              w_disp_grp_id;
logic [CMT_BLK_SIZE-1:0] w_entry_all_done;
logic [DISP_SIZE-1:0]              w_br_upd_valid_oh;
logic [riscv_pkg::VADDR_W-1: 0]    w_upd_br_vaddr;
logic [DISP_SIZE-1:0]              w_dead_grp_id_br_tmp;
logic [DISP_SIZE-1:0]              w_dead_grp_id_excpt_tmp;
logic [DISP_SIZE-1:0]              w_dead_grp_id;

logic [DISP_SIZE-1: 0] w_cmt_excpt_valid_oh;
excpt_t                excpt_type_selected;

// When this signal is 1, committer is killing uncommitted instructions
logic                              r_killing_uncmts;
logic                              w_killing_uncmts;

//
// LRQ Pointer
//
logic                                      w_in_vld, w_out_vld;
assign w_in_vld  = sc_disp.valid;
assign w_out_vld = w_entry_all_done[w_out_cmt_id] | w_killing_uncmts;


inoutptr #(.SIZE(CMT_BLK_SIZE)) u_cmt_ptr(.i_clk (i_clk), .i_reset_n(i_reset_n),
                                          .i_clear (1'b0),
                                          .i_in_vld (w_in_vld ), .o_in_ptr (w_in_cmt_id  ),
                                          .i_out_vld(w_out_vld), .o_out_ptr(w_out_cmt_id));


generate for (genvar d_idx = 0; d_idx < DISP_SIZE; d_idx++) begin : disp_loop
  assign w_disp_grp_id[d_idx] = sc_disp.inst[d_idx].valid;
end
endgenerate


generate for (genvar c_idx = 0; c_idx < CMT_BLK_SIZE; c_idx++) begin : entry_loop
logic w_load_valid;
  assign w_load_valid = sc_disp.valid & (w_in_cmt_id == c_idx);

  msrh_rob_entry u_entry
    (
     .i_clk (i_clk),
     .i_reset_n (i_reset_n),

     .i_cmt_id (c_idx[CMT_BLK_W-1:0]),

     .i_load_valid   (w_load_valid),
     .i_load_pc_addr (sc_disp.pc_addr),
     .i_load_inst    (sc_disp.inst),
     .i_load_grp_id  (w_disp_grp_id),
     .i_load_br_included (sc_disp.is_br_included),

     .i_done_rpt (i_done_rpt),

     .o_entry          (w_entries[c_idx]),
     .o_block_all_done (w_entry_all_done[c_idx]),
     .i_commit_finish  ((w_entry_all_done[c_idx] | r_killing_uncmts) &
                        (w_out_cmt_id == c_idx)),

     .br_upd_if (ex3_br_upd_if)
     );

end
endgenerate

assign o_sc_new_cmt_id = w_in_cmt_id;

assign w_killing_uncmts = r_killing_uncmts & (w_in_cmt_id != w_out_cmt_id);

assign o_commit.commit       = w_entry_all_done[w_out_cmt_id];
assign o_commit.cmt_id       = w_out_cmt_id;
assign o_commit.grp_id       = w_entries[w_out_cmt_id].done_grp_id;
assign o_commit.upd_pc_vld   = |w_entries[w_out_cmt_id].br_upd_info.upd_valid | (|w_entries[w_out_cmt_id].excpt_valid);
assign o_commit.upd_pc_vaddr = w_upd_br_vaddr;
assign o_commit.flush_vld    = o_commit.upd_pc_vld;
assign o_commit.excpt_valid  = |w_entries[w_out_cmt_id].excpt_valid;
assign o_commit.excpt_type   = excpt_type_selected;
assign o_commit.dead_id      = w_dead_grp_id;
assign o_commit.all_dead     = w_killing_uncmts;

// Select Exception Instruction
bit_extract_lsb #(.WIDTH(DISP_SIZE)) u_bit_excpt_valid (.in(w_entries[w_out_cmt_id].excpt_valid), .out(w_cmt_excpt_valid_oh));
bit_oh_or_packed #(.T(excpt_t), .WORDS(DISP_SIZE)) u_bit_excpt_select (.i_oh(w_cmt_excpt_valid_oh), .i_data(w_entries[w_out_cmt_id].excpt_type), .o_selected(excpt_type_selected));


assign o_commit_rnid_update.commit     = o_commit.commit | w_killing_uncmts;
generate for (genvar d_idx = 0; d_idx < DISP_SIZE; d_idx++) begin : commit_rd_loop
  assign o_commit_rnid_update.rnid_valid[d_idx] = w_entries[w_out_cmt_id].inst[d_idx].rd_valid;
  assign o_commit_rnid_update.rd_rnid   [d_idx] = w_entries[w_out_cmt_id].inst[d_idx].rd_rnid;
  assign o_commit_rnid_update.rd_regidx [d_idx] = w_entries[w_out_cmt_id].inst[d_idx].rd_regidx;
end
endgenerate
assign o_commit_rnid_update.is_br_included = w_entries[w_out_cmt_id].is_br_included;
assign o_commit_rnid_update.upd_pc_vld     = o_commit.upd_pc_vld & !o_commit.all_dead;
assign o_commit_rnid_update.dead_id        = w_dead_grp_id;
assign o_commit_rnid_update.all_dead       = w_killing_uncmts;

// Select Branch Target Address
bit_extract_lsb #(.WIDTH(DISP_SIZE)) u_bit_br_sel (.in(w_entries[w_out_cmt_id].br_upd_info.upd_valid), .out(w_br_upd_valid_oh));
bit_oh_or_packed #(.T(logic[riscv_pkg::VADDR_W-1:0]), .WORDS(DISP_SIZE))
br_sel_addr (.i_oh(w_br_upd_valid_oh),
             .i_data(w_entries[w_out_cmt_id].br_upd_info.upd_br_vaddr),
             .o_selected(w_upd_br_vaddr));

// Make dead Instruction, (after branch instruction)
bit_tree_lsb #(.WIDTH(DISP_SIZE)) u_bit_dead_br_grp_id (.in(w_entries[w_out_cmt_id].br_upd_info.upd_valid), .out(w_dead_grp_id_br_tmp));

// Make dead Instruction, (after exception)
bit_tree_lsb #(.WIDTH(DISP_SIZE)) u_bit_dead_excpt_grp_id (.in(w_entries[w_out_cmt_id].excpt_valid), .out(w_dead_grp_id_excpt_tmp));
assign w_dead_grp_id = {w_dead_grp_id_excpt_tmp[DISP_SIZE-2: 0], 1'b0} |   // 1-bit shift
                       {w_dead_grp_id_br_tmp   [DISP_SIZE-2: 0], 1'b0} ;   // 1-bit shift

// Killing all uncommitted instructions
always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_killing_uncmts <= 1'b0;
  end else begin
    if (o_commit.commit & o_commit.flush_vld & (w_in_cmt_id != w_out_cmt_id)) begin
      r_killing_uncmts <= 1'b1;
    end else if (r_killing_uncmts & (w_in_cmt_id == w_out_cmt_id)) begin
      r_killing_uncmts <= 1'b0;
    end
  end
end

`ifdef SIMULATION
logic [CMT_BLK_SIZE-1: 0] w_entry_valids;
generate for (genvar c_idx = 0; c_idx < CMT_BLK_SIZE; c_idx++) begin : dbg_entry_loop
  assign w_entry_valids[c_idx] = w_entries[c_idx].valid;
end
endgenerate

function void dump_entry_json(int fp, rob_entry_t entry, int index);

  if (entry.valid) begin
    $fwrite(fp, "    \"msrh_rob_entry[%d]\" : {", index);
    $fwrite(fp, "valid:%d, ", entry.valid);
    $fwrite(fp, "pc_addr:\"0x%0x\", ", entry.pc_addr << 1);

    $fwrite(fp, "grp_id:%d, ", entry.grp_id);
    $fwrite(fp, "done_grp_id:%d, ", entry.done_grp_id);

    $fwrite(fp, "excpt_valid:%d", entry.excpt_valid);

    $fwrite(fp, " },\n");
  end // if (entry.valid)

endfunction // dump_json


function void dump_json(int fp);
  if (|w_entry_valids) begin
    $fwrite(fp, "  \"msrh_rob\" : {\n");
    $fwrite(fp, "    in_cmt_id: %d,\n", w_in_cmt_id);
    $fwrite(fp, "    out_cmt_id: %d,\n", w_out_cmt_id);
    $fwrite(fp, "    killing: %d,\n", w_killing_uncmts);
    for (int c_idx = 0; c_idx < CMT_BLK_SIZE; c_idx++) begin
      dump_entry_json (fp, w_entries[c_idx], c_idx);
    end
    $fwrite(fp, "  },\n");
  end
endfunction // dump_json
`endif // SIMULATION

endmodule // msrh_rob
