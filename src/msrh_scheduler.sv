module msrh_scheduler
  #(
    parameter IS_STORE = 0,
    parameter IS_BRANCH = 1'b0,
    parameter ENTRY_SIZE = 32,
    parameter IN_PORT_SIZE = 2,
    parameter EN_OLDEST = 0
    )
(
 input logic                           i_clk,
 input logic                           i_reset_n,

 // ROB notification interface
 rob_info_if.slave                     rob_info_if,

 input logic [IN_PORT_SIZE-1: 0]       i_disp_valid,
 input msrh_pkg::cmt_id_t  i_cmt_id,
 input msrh_pkg::grp_id_t i_grp_id[IN_PORT_SIZE],
 msrh_pkg::disp_t                      i_disp_info[IN_PORT_SIZE],

 cre_ret_if.slave                      cre_ret_if,

 input logic                           i_stall,

 /* Forwarding path */
 input msrh_pkg::early_wr_t i_early_wr[msrh_pkg::REL_BUS_SIZE],
 input msrh_pkg::phy_wr_t   i_phy_wr  [msrh_pkg::TGT_BUS_SIZE],

 output                                msrh_pkg::issue_t o_issue,
 output [ENTRY_SIZE-1:0]               o_iss_index_oh,

 input msrh_pkg::mispred_t             i_mispred_lsu[msrh_conf_pkg::LSU_INST_NUM],

 done_if.slave                         pipe_done_if,

 output                                msrh_pkg::done_rpt_t o_done_report,

 // Commit notification
 input msrh_pkg::commit_blk_t          i_commit,
 // Branch Flush Notification
 br_upd_if.slave                       br_upd_if
 );

logic [ENTRY_SIZE-1:0] w_entry_valid;
logic [ENTRY_SIZE-1:0] w_entry_ready;
logic [ENTRY_SIZE-1:0] w_picked_inst;
logic [ENTRY_SIZE-1:0] w_picked_inst_pri;
logic [ENTRY_SIZE-1:0] w_picked_inst_oh;

msrh_pkg::issue_t w_entry[ENTRY_SIZE];

logic [$clog2(IN_PORT_SIZE): 0] w_input_valid_cnt;
logic [ENTRY_SIZE-1: 0]         w_entry_in_ptr_oh;
logic [ENTRY_SIZE-1: 0]         w_entry_out_ptr_oh;

logic [ENTRY_SIZE-1:0]          w_entry_done;
logic [ENTRY_SIZE-1:0]          w_entry_wait_complete;
logic [ENTRY_SIZE-1:0]          w_entry_complete;
logic [ENTRY_SIZE-1:0]          w_entry_finish;
msrh_pkg::cmt_id_t w_entry_cmt_id [ENTRY_SIZE];
msrh_pkg::grp_id_t w_entry_grp_id [ENTRY_SIZE];
logic [ENTRY_SIZE-1:0]               w_entry_except_valid;
msrh_pkg::except_t                   w_entry_except_type [ENTRY_SIZE];
logic [riscv_pkg::XLEN_W-1: 0]       w_entry_except_tval [ENTRY_SIZE];

logic                                w_flush_valid;
assign w_flush_valid = msrh_pkg::is_flushed_commit(i_commit);

logic                                w_ignore_disp;
logic [$clog2(ENTRY_SIZE): 0]        w_credit_return_val;

/* verilator lint_off WIDTH */
bit_cnt #(.WIDTH(IN_PORT_SIZE)) u_input_valid_cnt (.in(i_disp_valid), .out(w_input_valid_cnt));

inoutptr_var_oh
  #(.SIZE(ENTRY_SIZE))
u_req_ptr
  (
   .i_clk (i_clk),
   .i_reset_n(i_reset_n),

   .i_rollback (1'b0),

   .i_in_valid (|i_disp_valid & ~w_ignore_disp),
   .i_in_val   ({{($clog2(ENTRY_SIZE)-$clog2(IN_PORT_SIZE)){1'b0}}, w_input_valid_cnt}),
   .o_in_ptr_oh(w_entry_in_ptr_oh   ),

   .i_out_valid  (|w_entry_finish),
   .i_out_val    ({{($clog2(ENTRY_SIZE)){1'b0}}, 1'b1}),
   .o_out_ptr_oh (w_entry_out_ptr_oh                  )
   );

assign w_ignore_disp = w_flush_valid & (|i_disp_valid);
assign w_credit_return_val = ((|w_entry_finish)    ? 'h1 : 'h0) +
                             (w_ignore_disp        ? w_input_valid_cnt  : 'h0) ;

msrh_credit_return_slave
  #(.MAX_CREDITS(ENTRY_SIZE))
u_credit_return_slave
(
 .i_clk(i_clk),
 .i_reset_n(i_reset_n),

 .i_get_return((|w_entry_finish) | w_ignore_disp),
 .i_return_val(w_credit_return_val),

 .cre_ret_if (cre_ret_if)
 );

`ifdef SIMULATION
/* verilator lint_off WIDTH */
logic [$clog2(ENTRY_SIZE): 0]      w_entry_valid_cnt;
bit_cnt #(.WIDTH(ENTRY_SIZE)) u_entry_valid_cnt (.in(w_entry_valid), .out(w_entry_valid_cnt));

always_ff @ (negedge i_clk, negedge i_reset_n) begin
  if (i_reset_n) begin
    if (u_credit_return_slave.r_credits != w_entry_valid_cnt) begin
      $display("%m credit and entry number different. r_credits = %d, entry_mask = %x\n",
               u_credit_return_slave.r_credits,
               w_entry_valid_cnt);
      $finish;
      // $fatal(0, "%m credit and entry number different. r_credits = %d, entry_mask = %x\n",
      //        u_credit_return_slave.r_credits,
      //        w_entry_valid_cnt);
    end
  end
end
`endif // SIMULATION

bit_brshift
  #(.WIDTH(ENTRY_SIZE))
u_age_selector
  (
   .in   (w_entry_valid & w_entry_ready & {ENTRY_SIZE{~i_stall}}),
   .i_sel(w_entry_out_ptr_oh),
   .out  (w_picked_inst)
   );

bit_extract_lsb #(.WIDTH(ENTRY_SIZE)) u_pick_ready_inst (.in(w_picked_inst), .out(w_picked_inst_pri));

bit_blshift
  #(.WIDTH(ENTRY_SIZE))
u_inst_selector
  (
   .in   (w_picked_inst_pri),
   .i_sel(w_entry_out_ptr_oh),
   .out  (w_picked_inst_oh)
   );


generate for (genvar s_idx = 0; s_idx < ENTRY_SIZE; s_idx++) begin : entry_loop
  logic [IN_PORT_SIZE-1: 0] w_input_valid;
  msrh_pkg::disp_t          w_disp_entry;
  msrh_pkg::grp_id_t        w_disp_grp_id;
  for (genvar i_idx = 0; i_idx < IN_PORT_SIZE; i_idx++) begin : in_loop
    logic [ENTRY_SIZE-1: 0] target_idx_oh;
    bit_rotate_left #(.WIDTH(ENTRY_SIZE), .VAL(i_idx)) target_bit_rotate (.i_in(w_entry_in_ptr_oh), .o_out(target_idx_oh));
    assign w_input_valid[i_idx] = i_disp_valid[i_idx] & !w_flush_valid & (target_idx_oh[s_idx]);
  end

  bit_oh_or #(.T(msrh_pkg::disp_t), .WORDS(IN_PORT_SIZE)) bit_oh_entry (.i_oh(w_input_valid), .i_data(i_disp_info), .o_selected(w_disp_entry));
  bit_oh_or #(.T(logic[msrh_conf_pkg::DISP_SIZE-1:0]), .WORDS(IN_PORT_SIZE)) bit_oh_grp_id (.i_oh(w_input_valid), .i_data(i_grp_id), .o_selected(w_disp_grp_id));

  msrh_sched_entry
    #(
      .IS_STORE(IS_STORE),
      .IS_BRANCH (IS_BRANCH),
      .EN_OLDEST(EN_OLDEST)
      )
  u_sched_entry(
    .i_clk    (i_clk    ),
    .i_reset_n(i_reset_n),

    .i_out_ptr_valid (w_entry_out_ptr_oh [s_idx]),
    .rob_info_if   (rob_info_if),

    .i_put      (|w_input_valid),

    .i_cmt_id   (i_cmt_id  ),
    .i_grp_id   (w_disp_grp_id  ),
    .i_put_data (w_disp_entry  ),

    .o_entry_valid(w_entry_valid[s_idx]),
    .o_entry_ready(w_entry_ready[s_idx]),
    .o_entry(w_entry[s_idx]),

    .i_early_wr(i_early_wr),
    .i_phy_wr(i_phy_wr),
    .i_mispred_lsu(i_mispred_lsu),

    .i_pipe_done (pipe_done_if.done & pipe_done_if.index_oh[s_idx]),
    .pipe_done_if (pipe_done_if),

    .i_commit (i_commit),
    .br_upd_if (br_upd_if),

    .i_entry_picked    (w_picked_inst_oh[s_idx]),
    .o_entry_done      (w_entry_done[s_idx]),
    .o_entry_wait_complete (w_entry_wait_complete[s_idx]),
    .o_entry_finish    (w_entry_finish[s_idx]),
    .o_cmt_id          (w_entry_cmt_id[s_idx]),
    .o_grp_id          (w_entry_grp_id[s_idx]),
    .o_except_valid    (w_entry_except_valid[s_idx]),
    .o_except_type     (w_entry_except_type [s_idx]),
    .o_except_tval     (w_entry_except_tval [s_idx])
  );

end
endgenerate

bit_oh_or #(.T(msrh_pkg::issue_t), .WORDS(ENTRY_SIZE)) u_picked_inst (.i_oh(w_picked_inst_oh), .i_data(w_entry), .o_selected(o_issue));
assign o_iss_index_oh = w_picked_inst_oh;

// --------------
// Done signals
// --------------
bit_oh_or #(.T(logic[msrh_pkg::CMT_ID_W-1:0]),       .WORDS(ENTRY_SIZE)) bit_oh_entry       (.i_oh(w_entry_done), .i_data(w_entry_cmt_id    ), .o_selected(o_done_report.cmt_id  ));
bit_oh_or #(.T(logic[msrh_conf_pkg::DISP_SIZE-1:0]), .WORDS(ENTRY_SIZE)) bit_oh_grp_id      (.i_oh(w_entry_done), .i_data(w_entry_grp_id    ), .o_selected(o_done_report.grp_id  ));
bit_oh_or #(.T(msrh_pkg::except_t),                  .WORDS(ENTRY_SIZE)) bit_oh_except_type (.i_oh(w_entry_done), .i_data(w_entry_except_type), .o_selected(o_done_report.except_type));
bit_oh_or #(.T(logic[riscv_pkg::XLEN_W-1: 0]),       .WORDS(ENTRY_SIZE)) bit_oh_except_tval (.i_oh(w_entry_done), .i_data(w_entry_except_tval), .o_selected(o_done_report.except_tval));

assign o_done_report.valid = |w_entry_done;
assign o_done_report.except_valid = |(w_entry_except_valid & w_entry_done);

`ifdef SIMULATION
typedef struct packed {
  msrh_pkg::issue_t entry;
  msrh_pkg::sched_state_t state;
} entry_ptr_t;

function void dump_entry_json(int fp, entry_ptr_t entry, int index);

  if (entry.entry.valid) begin
    $fwrite(fp, "    \"msrh_sched_entry[%d]\" : {", index[$clog2(ENTRY_SIZE)-1: 0]);
    $fwrite(fp, "valid:%d, ", entry.entry.valid);
    $fwrite(fp, "pc_addr:\"0x%0x\", ", entry.entry.pc_addr);
    $fwrite(fp, "inst:\"%08x\", ", entry.entry.inst);

    $fwrite(fp, "cmt_id:%d, ", entry.entry.cmt_id);
    $fwrite(fp, "grp_id:%d, ", entry.entry.grp_id);

    // Destination Register
    $fwrite(fp, "rd:{ valid:%1d, idx:%02d, rnid:%d },", entry.entry.wr_reg.valid, entry.entry.wr_reg.regidx, entry.entry.wr_reg.rnid);
    // Source 1
    $fwrite(fp, "rs1:{ valid:%1d, idx:%02d, rnid:%d, ready:%01d },", entry.entry.rd_regs[0].valid, entry.entry.rd_regs[0].regidx, entry.entry.rd_regs[0].rnid, entry.entry.rd_regs[0].ready);
    // Source 2
    $fwrite(fp, "rs2:{ valid:%1d, idx:%02d, rnid:%d, ready:%01d },", entry.entry.rd_regs[1].valid, entry.entry.rd_regs[1].regidx, entry.entry.rd_regs[1].rnid, entry.entry.rd_regs[1].ready);
    $fwrite(fp, "state:\"%s\", ", entry.state == msrh_pkg::INIT          ? "INIT" :
                                  entry.state == msrh_pkg::WAIT          ? "WAIT" :
                                  entry.state == msrh_pkg::ISSUED        ? "ISSUED" :
                                  entry.state == msrh_pkg::DONE          ? "DONE" :
                                  entry.state == msrh_pkg::WAIT_COMPLETE ? "WAIT_COMPLETE" :
                                  entry.state == msrh_pkg::DEAD          ? "DEAD" : "x");
    $fwrite(fp, " },\n");
  end // if (entry.entry.valid)

endfunction // dump_json

entry_ptr_t w_entry_ptr[ENTRY_SIZE];
generate for (genvar s_idx = 0; s_idx < ENTRY_SIZE; s_idx++) begin : entry_loop_ptr
  assign w_entry_ptr[s_idx].entry = entry_loop[s_idx].u_sched_entry.r_entry;
  assign w_entry_ptr[s_idx].state = entry_loop[s_idx].u_sched_entry.r_state;
end
endgenerate

function void dump_json(string name, int fp, int index);
  if (|w_entry_valid) begin
    $fwrite(fp, "  \"msrh_scheduler_%s[%d]\" : {\n", name, index[$clog2(ENTRY_SIZE)-1: 0]);
    $fwrite(fp, "    \"in_ptr\"  : %d\n", w_entry_in_ptr_oh);
    $fwrite(fp, "    \"out_ptr\" : %d\n", w_entry_out_ptr_oh);
    for (int s_idx = 0; s_idx < ENTRY_SIZE; s_idx++) begin
      dump_entry_json (fp, w_entry_ptr[s_idx], s_idx);
    end
    $fwrite(fp, "  },\n");
  end
endfunction // dump_json
`endif // SIMULATION

endmodule // msrh_scheduler
