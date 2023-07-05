// ------------------------------------------------------------------------
// NAME : scariv_lsu_issue_unit
// TYPE : module
// ------------------------------------------------------------------------
// SCARIV Instruction Scheduler for LSU
// ------------------------------------------------------------------------
// ------------------------------------------------------------------------

module scariv_lsu_issue_unit
  import scariv_lsu_pkg::*;
#(
    parameter IS_STORE = 0,
    parameter IS_BRANCH = 1'b0,
    parameter ENTRY_SIZE = 32,
    parameter IN_PORT_SIZE = 2,
    parameter EN_OLDEST = 0,
    parameter NUM_OPERANDS = 2,
    parameter NUM_DONE_PORT = 1
    )
(
  input logic                           i_clk,
  input logic                           i_reset_n,
  
  // ROB notification interface
  rob_info_if.slave                     rob_info_if,
  
  input logic [IN_PORT_SIZE-1: 0]       i_disp_valid,
  input scariv_pkg::cmt_id_t  i_cmt_id,
  input scariv_pkg::grp_id_t i_grp_id[IN_PORT_SIZE],
  scariv_pkg::disp_t                      i_disp_info[IN_PORT_SIZE],
  
  cre_ret_if.slave                      cre_ret_if,
  
  input logic                           i_stall,
  
  /* Forwarding path */
  input scariv_pkg::early_wr_t i_early_wr[scariv_pkg::REL_BUS_SIZE],
  input scariv_pkg::phy_wr_t   i_phy_wr  [scariv_pkg::TGT_BUS_SIZE],
  
  output scariv_pkg::issue_t o_issue,
  output [ENTRY_SIZE-1:0]    o_iss_index_oh,
  
  input scariv_pkg::mispred_t           i_mispred_lsu[scariv_conf_pkg::LSU_INST_NUM],
  // Execution updates from pipeline
  input ex1_q_update_t                  i_ex1_updates,
  input logic                           i_tlb_resolve,
  input logic                           i_st_buffer_empty,
  input logic                           i_st_requester_empty,

  done_if.slave                         pipe_done_if,
  
  output scariv_pkg::done_rpt_t         o_done_report,
  
  // Commit notification
  input scariv_pkg::commit_blk_t          i_commit,
  // Branch Flush Notification
  br_upd_if.slave                       br_upd_if
);

logic [ENTRY_SIZE-1:0] w_entry_valid;
logic [ENTRY_SIZE-1:0] w_entry_ready;
logic [ENTRY_SIZE-1:0] w_picked_inst;
logic [ENTRY_SIZE-1:0] w_picked_inst_pri;
logic [ENTRY_SIZE-1:0] w_picked_inst_oh;

scariv_pkg::issue_t w_entry[ENTRY_SIZE];

logic [$clog2(IN_PORT_SIZE): 0] w_input_valid_cnt;
logic [ENTRY_SIZE-1: 0]         w_entry_in_ptr_oh;
logic [ENTRY_SIZE-1: 0]         w_entry_out_ptr_oh;

logic [ENTRY_SIZE-1:0]          w_entry_wait_complete;
logic [ENTRY_SIZE-1:0]          w_entry_complete;
logic [ENTRY_SIZE-1:0]          w_entry_finish;
logic [ENTRY_SIZE-1:0]          w_entry_finish_oh;
logic [ENTRY_SIZE-1: 0]         w_entry_done;
logic [ENTRY_SIZE-1: 0]         w_entry_done_oh;
scariv_pkg::done_rpt_t          w_entry_done_report[ENTRY_SIZE];

logic                                w_flush_valid;
assign w_flush_valid = scariv_pkg::is_flushed_commit(i_commit);

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

   .i_out_valid  (|w_entry_finish_oh),
   .i_out_val    ({{($clog2(ENTRY_SIZE)){1'b0}}, 1'b1}),
   .o_out_ptr_oh (w_entry_out_ptr_oh                  )
   );

assign w_ignore_disp = w_flush_valid & (|i_disp_valid);
assign w_credit_return_val = ((|w_entry_finish_oh) ? 'h1 : 'h0) +
                             (w_ignore_disp        ? w_input_valid_cnt  : 'h0) ;

scariv_credit_return_slave
  #(.MAX_CREDITS(ENTRY_SIZE))
u_credit_return_slave
(
 .i_clk(i_clk),
 .i_reset_n(i_reset_n),

 .i_get_return((|w_entry_finish_oh) | w_ignore_disp),
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
  scariv_pkg::disp_t          w_disp_entry;
  scariv_pkg::grp_id_t        w_disp_grp_id;
  for (genvar i_idx = 0; i_idx < IN_PORT_SIZE; i_idx++) begin : in_loop
    logic [ENTRY_SIZE-1: 0] target_idx_oh;
    bit_rotate_left #(.WIDTH(ENTRY_SIZE), .VAL(i_idx)) target_bit_rotate (.i_in(w_entry_in_ptr_oh), .o_out(target_idx_oh));
    assign w_input_valid[i_idx] = i_disp_valid[i_idx] & !w_flush_valid & (target_idx_oh[s_idx]);
  end

  bit_oh_or #(.T(scariv_pkg::disp_t), .WORDS(IN_PORT_SIZE)) bit_oh_entry (.i_oh(w_input_valid), .i_data(i_disp_info), .o_selected(w_disp_entry));
  bit_oh_or #(.T(logic[scariv_conf_pkg::DISP_SIZE-1:0]), .WORDS(IN_PORT_SIZE)) bit_oh_grp_id (.i_oh(w_input_valid), .i_data(i_grp_id), .o_selected(w_disp_grp_id));

  logic  w_pipe_done_valid;
  scariv_pkg::done_payload_t    w_done_payloads;
  assign w_pipe_done_valid = pipe_done_if.done & pipe_done_if.index_oh[s_idx];
  assign w_done_payloads   = pipe_done_if.payload;

  scariv_lsu_issue_entry
  u_entry(
    .i_clk    (i_clk    ),
    .i_reset_n(i_reset_n),

    .i_out_ptr_valid (w_entry_out_ptr_oh [s_idx] ),

    .rob_info_if (rob_info_if),

    .i_put      (|w_input_valid),

    .i_cmt_id   (i_cmt_id  ),
    .i_grp_id   (w_disp_grp_id  ),
    .i_put_data (w_disp_entry  ),

    .o_entry_valid(w_entry_valid[s_idx]),
    .o_entry_ready(w_entry_ready[s_idx]),
    .o_entry(w_entry[s_idx]),

    .i_early_wr(i_early_wr),
    .i_phy_wr(i_phy_wr),

    .i_mispred_lsu (i_mispred_lsu),
    .i_ex1_updates (i_ex1_updates),
    .i_tlb_resolve        (i_tlb_resolve       ),
    .i_st_buffer_empty    (i_st_buffer_empty   ),
    .i_st_requester_empty (i_st_requester_empty),  
  
    .i_commit (i_commit),
    .br_upd_if (br_upd_if),

    .o_issue_succeeded (w_entry_finish   [s_idx]),
    .i_clear_entry     (w_entry_finish_oh[s_idx]),

    .i_entry_picked    (w_picked_inst_oh[s_idx])
  );

  assign w_entry_done[s_idx] = w_entry_done_report[s_idx].valid;

end
endgenerate

bit_oh_or #(.T(scariv_pkg::issue_t), .WORDS(ENTRY_SIZE)) u_picked_inst (.i_oh(w_picked_inst_oh), .i_data(w_entry), .o_selected(o_issue));
assign o_iss_index_oh = w_picked_inst_oh;
// Clear selection
assign w_entry_finish_oh = w_entry_finish & w_entry_out_ptr_oh;

// --------------
// Done signals
// --------------
bit_extract_lsb_ptr_oh #(.WIDTH(ENTRY_SIZE)) bit_extract_done (.in(w_entry_done), .i_ptr_oh(w_entry_out_ptr_oh), .out(w_entry_done_oh));
bit_oh_or #(.T(scariv_pkg::done_rpt_t), .WORDS(ENTRY_SIZE)) bit_oh_done_report  (.i_oh(w_entry_done_oh), .i_data(w_entry_done_report), .o_selected(o_done_report ));

`ifdef SIMULATION
typedef struct packed {
  scariv_pkg::issue_t entry;
  scariv_pkg::sched_state_t state;
} entry_ptr_t;

function void dump_entry_json(int fp, entry_ptr_t entry, int index);

  if (entry.entry.valid) begin
    $fwrite(fp, "    \"scariv_issue_entry[%d]\" : {", index[$clog2(ENTRY_SIZE)-1: 0]);
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
    $fwrite(fp, "state:\"%s\", ", entry.state == scariv_pkg::INIT          ? "INIT" :
                                  entry.state == scariv_pkg::WAIT          ? "WAIT" :
                                  entry.state == scariv_pkg::ISSUED        ? "ISSUED" :
                                  entry.state == scariv_pkg::DONE          ? "DONE" :
                                  entry.state == scariv_pkg::WAIT_COMPLETE ? "WAIT_COMPLETE" :
                                  entry.state == scariv_pkg::DEAD          ? "DEAD" : "x");
    $fwrite(fp, " },\n");
  end // if (entry.entry.valid)

endfunction // dump_json

entry_ptr_t w_entry_ptr[ENTRY_SIZE];
generate for (genvar s_idx = 0; s_idx < ENTRY_SIZE; s_idx++) begin : entry_loop_ptr
  assign w_entry_ptr[s_idx].entry = entry_loop[s_idx].u_entry.r_entry;
  assign w_entry_ptr[s_idx].state = entry_loop[s_idx].u_entry.r_state;
end
endgenerate

function void dump_json(string name, int fp, int index);
  if (|w_entry_valid) begin
    $fwrite(fp, "  \"scariv_lsu_issue_unit_%s[%d]\" : {\n", name, index[$clog2(ENTRY_SIZE)-1: 0]);
    $fwrite(fp, "    \"in_ptr\"  : %d\n", w_entry_in_ptr_oh);
    $fwrite(fp, "    \"out_ptr\" : %d\n", w_entry_out_ptr_oh);
    for (int s_idx = 0; s_idx < ENTRY_SIZE; s_idx++) begin
      dump_entry_json (fp, w_entry_ptr[s_idx], s_idx);
    end
    $fwrite(fp, "  },\n");
  end
endfunction // dump_json


logic [63: 0] r_cycle_count;
logic [63: 0] r_sched_max_period;
logic [63: 0] r_sched_entry_count;

always_ff @ (negedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_sched_max_period  <= 'h0;
    r_sched_entry_count <= 'h0;
    r_cycle_count  <= 'h0;
  end else begin
    r_cycle_count <= r_cycle_count + 'h1;
    if (r_cycle_count % sim_pkg::COUNT_UNIT == sim_pkg::COUNT_UNIT-1) begin
      r_sched_max_period  <= 'h0;
      r_sched_entry_count <= 'h0;
    end else begin
      if (|w_entry_valid) begin
        if (&w_entry_valid) begin
          r_sched_max_period  <= r_sched_max_period + 'h1;
        end
        r_sched_entry_count <= r_sched_entry_count + $countones(w_entry_valid);
      end
    end // else: !if(r_cycle_count % sim_pkg::COUNT_UNIT == sim_pkg::COUNT_UNIT-1)
  end // else: !if(!i_reset_n)
end // always_ff @ (negedge i_clk, negedge i_reset_n)


function void dump_perf (string name, int fp);
  $fwrite(fp, "  \"%s\" : {", name);
  $fwrite(fp, "  \"max_period\" : %5d, ", r_sched_max_period);
  $fwrite(fp, "  \"average count\" : %5f},\n", r_sched_entry_count / 1000.0);
endfunction // dump_perf

`endif // SIMULATION

endmodule // scariv_lsu_issue_unit
