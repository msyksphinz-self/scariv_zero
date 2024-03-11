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
  input scariv_pkg::cmt_id_t            i_cmt_id,
  input scariv_pkg::grp_id_t            i_grp_id[IN_PORT_SIZE],
  scariv_pkg::disp_t                    i_disp_info[IN_PORT_SIZE],

  cre_ret_if.slave                      cre_ret_if,

  input logic                           i_stall,

  /* Forwarding path */
  early_wr_if.slave early_wr_if[scariv_pkg::REL_BUS_SIZE],
  phy_wr_if.slave   phy_wr_if  [scariv_pkg::TGT_BUS_SIZE],

  output scariv_lsu_pkg::lsu_issue_entry_t o_issue,
  output [ENTRY_SIZE-1:0]                  o_iss_index_oh,

  lsu_mispred_if.slave           mispred_if[scariv_conf_pkg::LSU_INST_NUM],
  // Execution updates from pipeline
  iq_upd_if.slave  iq_upd_if,
  input logic                           i_st_buffer_empty,
  input logic                           i_st_requester_empty,
  input logic                           i_missu_is_empty,
  input logic                           i_replay_queue_full,
  input logic                           i_stq_rmw_existed,

  done_if.slave                         pipe_done_if,

  // Commit notification
  commit_if.monitor          commit_if,
  // Branch Flush Notification
  br_upd_if.slave                       br_upd_if
);

logic [ENTRY_SIZE-1:0] w_entry_valid;
logic [ENTRY_SIZE-1:0] w_entry_ready;
logic [ENTRY_SIZE-1:0] w_entry_oldest_valid;
logic [ENTRY_SIZE-1:0] w_picked_inst;
logic [ENTRY_SIZE-1:0] w_picked_inst_pri;
logic [ENTRY_SIZE-1:0] w_picked_inst_oh;

scariv_lsu_pkg::iq_entry_t w_entry[ENTRY_SIZE];

logic [$clog2(IN_PORT_SIZE): 0] w_input_valid_cnt;
logic [ENTRY_SIZE-1: 0]         w_entry_in_ptr_oh;
logic [ENTRY_SIZE-1: 0]         r_entry_out_ptr_oh;

logic [ENTRY_SIZE-1:0]          w_entry_wait_complete;
logic [ENTRY_SIZE-1:0]          w_entry_complete;
logic [ENTRY_SIZE-1:0]          w_entry_finish;
logic [ENTRY_SIZE-1:0]          w_entry_finish_oh;

logic                                w_flush_valid;
assign w_flush_valid = scariv_pkg::is_flushed_commit(commit_if.commit_valid, commit_if.payload);

logic                                w_ignore_disp;
logic [$clog2(ENTRY_SIZE): 0]        w_credit_return_val;

logic [$clog2(ENTRY_SIZE)-1: 0] w_entry_load_index[IN_PORT_SIZE];
logic [$clog2(ENTRY_SIZE)-1: 0] w_entry_finish_index[IN_PORT_SIZE];

scariv_lsu_pkg::iq_entry_t   w_iq_entry_selected;
scariv_lsu_pkg::iq_payload_t w_iq_payload_selected;

/* verilator lint_off WIDTH */
bit_cnt #(.WIDTH(IN_PORT_SIZE)) u_input_valid_cnt (.in(i_disp_valid), .out(w_input_valid_cnt));

generate for (genvar p_idx = 0; p_idx < IN_PORT_SIZE; p_idx++) begin : entry_finish_loop
  if (p_idx == 0) begin
    bit_encoder #(.WIDTH(ENTRY_SIZE)) u_finish_entry_encoder (.i_in(w_entry_finish_oh), .o_out(w_entry_finish_index[p_idx]));
  end else begin
    assign w_entry_finish_index[p_idx] = 'h0;
  end
end endgenerate

scariv_freelist_multiports
  #(.SIZE (ENTRY_SIZE),
    .WIDTH ($clog2(ENTRY_SIZE)),
    .PORTS (IN_PORT_SIZE)
    )
u_entry_freelist
  (
   .i_clk    (i_clk),
   .i_reset_n(i_reset_n),

   .i_push    (|w_entry_finish_oh),
   .i_push_id (w_entry_finish_index),

   .i_pop   (i_disp_valid),
   .o_pop_id(w_entry_load_index),

   .o_is_empty()
   );


always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_entry_out_ptr_oh <= 'h1;
  end else begin
    if (scariv_pkg::is_flushed_commit(commit_if.commit_valid, commit_if.payload)) begin
      r_entry_out_ptr_oh <= 'h1;
    end else if (o_issue.valid & ~i_stall ) begin
      r_entry_out_ptr_oh <= o_iss_index_oh;
    end
  end
end


assign w_ignore_disp = w_flush_valid & (|i_disp_valid);
assign w_credit_return_val = (|w_entry_finish_oh) ? 'h1 : 'h0;

scariv_credit_return_slave
  #(.MAX_CREDITS(ENTRY_SIZE))
u_credit_return_slave
(
 .i_clk(i_clk),
 .i_reset_n(i_reset_n),

 .i_get_return(|w_entry_finish_oh ),
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
   .in   (|w_entry_oldest_valid ? w_entry_oldest_valid : w_entry_valid & w_entry_ready),
   .i_sel(r_entry_out_ptr_oh),
   .out  (w_picked_inst)
   );

bit_extract_lsb #(.WIDTH(ENTRY_SIZE)) u_pick_ready_inst (.in(w_picked_inst), .out(w_picked_inst_pri));

bit_blshift
  #(.WIDTH(ENTRY_SIZE))
u_inst_selector
  (
   .in   (w_picked_inst_pri),
   .i_sel(r_entry_out_ptr_oh),
   .out  (w_picked_inst_oh)
   );

scariv_lsu_pkg::iq_entry_t w_input_entry[IN_PORT_SIZE];
logic [IN_PORT_SIZE-1: 0] w_disp_oldest_valid;
generate for (genvar idx = 0; idx < IN_PORT_SIZE; idx++) begin : in_port_loop

  logic [ 1: 0]             w_rs_rel_hit;
  logic [ 1: 0]             w_rs_may_mispred;
  scariv_pkg::rel_bus_idx_t [ 1: 0] w_rs_rel_index;
  logic [ 1: 0]             w_rs_phy_hit;
  logic [ 1: 0]             w_rs_mispredicted;

  for (genvar rs_idx = 0; rs_idx < 2; rs_idx++) begin : rs_loop
    scariv_pkg::rnid_t        w_rs_rnid;
    scariv_pkg::reg_t         w_rs_type;

    assign w_rs_rnid = i_disp_info[idx].rd_regs[rs_idx].rnid;
    assign w_rs_type = i_disp_info[idx].rd_regs[rs_idx].typ ;

    select_early_wr_bus_oh rs_rel_select_oh (.i_entry_rnid (w_rs_rnid), .i_entry_type (w_rs_type), .early_wr_if (early_wr_if),
                                             .o_valid   (w_rs_rel_hit[rs_idx]), .o_hit_index (w_rs_rel_index[rs_idx]), .o_may_mispred (w_rs_may_mispred[rs_idx]));
    select_phy_wr_bus   rs_phy_select    (.i_entry_rnid (w_rs_rnid), .i_entry_type (w_rs_type), .phy_wr_if   (phy_wr_if),
                                          .o_valid      (w_rs_phy_hit[rs_idx]));
    select_mispred_bus  rs_mispred_select(.i_entry_rnid (w_rs_rnid), .i_entry_type (w_rs_type), .i_mispred  (mispred_if),
                                          .o_mispred    (w_rs_mispredicted[rs_idx]));
  end

  assign w_input_entry[idx] = assign_entry(i_disp_info[idx], w_flush_valid, i_cmt_id, i_grp_id[idx],
                                           w_rs_rel_hit, w_rs_phy_hit, w_rs_may_mispred, w_rs_rel_index,
                                           i_stq_rmw_existed, w_disp_oldest_valid[idx]);

  decoder_lsu_sched u_lsu_sched (.inst(i_disp_info[idx].inst), .oldest(w_disp_oldest_valid[idx]));

end endgenerate

generate for (genvar s_idx = 0; s_idx < ENTRY_SIZE; s_idx++) begin : entry_loop
  logic [IN_PORT_SIZE-1: 0] w_input_valid;
  iq_entry_t                w_disp_entry;
  scariv_pkg::grp_id_t      w_disp_grp_id;
  for (genvar i_idx = 0; i_idx < IN_PORT_SIZE; i_idx++) begin : in_loop
    assign w_input_valid[i_idx] = i_disp_valid[i_idx] & (w_entry_load_index[i_idx] == s_idx);
  end

  bit_oh_or #(.T(iq_entry_t), .WORDS(IN_PORT_SIZE)) bit_oh_entry (.i_oh(w_input_valid), .i_data(w_input_entry), .o_selected(w_disp_entry));
  bit_oh_or #(.T(logic[scariv_conf_pkg::DISP_SIZE-1:0]), .WORDS(IN_PORT_SIZE)) bit_oh_grp_id (.i_oh(w_input_valid), .i_data(i_grp_id), .o_selected(w_disp_grp_id));

  logic  w_pipe_done_valid;
  scariv_pkg::done_payload_t    w_done_payloads;
  assign w_pipe_done_valid = pipe_done_if.done & pipe_done_if.index_oh[s_idx];
  assign w_done_payloads   = pipe_done_if.payload;

  assign w_entry_oldest_valid[s_idx] = w_entry[s_idx].valid & w_entry_ready[s_idx] & w_entry[s_idx].oldest_valid;

  scariv_lsu_issue_entry
  u_entry(
    .i_clk    (i_clk    ),
    .i_reset_n(i_reset_n),

    .i_out_ptr_valid (r_entry_out_ptr_oh [s_idx] ),

    .rob_info_if (rob_info_if),

    .i_put             (|w_input_valid   ),
    .i_put_entry       (w_disp_entry     ),
    .i_cmt_id          (i_cmt_id         ),
    .i_grp_id          (w_disp_grp_id    ),
    .i_stq_rmw_existed (i_stq_rmw_existed),

    .o_entry_valid(w_entry_valid[s_idx]),
    .o_entry_ready(w_entry_ready[s_idx]),
    .o_entry(w_entry[s_idx]),

    .early_wr_if(early_wr_if),
    .phy_wr_if(phy_wr_if),

    .mispred_if (mispred_if),
    .iq_upd_if  (iq_upd_if ),
    .i_st_buffer_empty    (i_st_buffer_empty   ),
    .i_st_requester_empty (i_st_requester_empty),
    .i_replay_queue_full  (i_replay_queue_full ),
    .i_missu_is_empty     (i_missu_is_empty    ),

    .commit_if (commit_if),
    .br_upd_if (br_upd_if),

    .o_issue_succeeded (w_entry_finish   [s_idx]),
    .i_clear_entry     (w_entry_finish_oh[s_idx]),

    .i_entry_picked    (w_picked_inst_oh[s_idx] & ~i_stall)
  );

end
endgenerate


scariv_lsu_pkg::iq_payload_t w_in_payload[IN_PORT_SIZE];
generate for (genvar p_idx = 0; p_idx < IN_PORT_SIZE; p_idx++) begin : in_payload_loop
  assign w_in_payload[p_idx] = scariv_lsu_pkg::assign_payload (i_disp_info[p_idx]);
end endgenerate

// Payload RAM
logic [$clog2(ENTRY_SIZE)-1: 0] w_picked_inst_index;
bit_encoder #(.WIDTH(ENTRY_SIZE)) u_issue_index_encoder (.i_in(w_picked_inst_oh), .o_out(w_picked_inst_index));
distributed_1rd_ram
  #(.WR_PORTS(IN_PORT_SIZE), .WIDTH($bits(scariv_lsu_pkg::iq_payload_t)), .WORDS(ENTRY_SIZE))
u_iq_payload_ram
  (
   .i_clk     (i_clk    ),
   .i_reset_n (i_reset_n),

   .i_wr      (i_disp_valid      ),
   .i_wr_addr (w_entry_load_index),
   .i_wr_data (w_in_payload      ),

   .i_rd_addr (w_picked_inst_index  ),
   .o_rd_data (w_iq_payload_selected)
   );


assign o_issue = scariv_lsu_pkg::assign_issue(w_iq_entry_selected, w_iq_payload_selected);

bit_oh_or #(.T(scariv_lsu_pkg::iq_entry_t), .WORDS(ENTRY_SIZE)) u_picked_inst (.i_oh(w_picked_inst_oh), .i_data(w_entry), .o_selected(w_iq_entry_selected));
assign o_iss_index_oh = w_picked_inst_oh;

// Clear selection
bit_extract_lsb_ptr_oh #(.WIDTH(ENTRY_SIZE)) u_entry_finish_bit_oh (.in(w_entry_finish), .i_ptr_oh(r_entry_out_ptr_oh), .out(w_entry_finish_oh));


`ifdef SIMULATION
typedef struct packed {
  scariv_lsu_pkg::lsu_issue_entry_t entry;
  scariv_lsu_pkg::lsu_sched_state_t state;
} entry_ptr_t;

function void dump_entry_json(int fp, entry_ptr_t entry, int index);

  if (entry.entry.valid) begin
    $fwrite(fp, "    \"scariv_issue_entry[%d]\" : {", index[$clog2(ENTRY_SIZE)-1: 0]);
    $fwrite(fp, "valid:%d, ", entry.entry.valid);
    $fwrite(fp, "pc_addr:\"0x%0x\", ", entry.entry.sim_pc_addr);
    $fwrite(fp, "inst:\"%08x\", ", entry.entry.inst);

    $fwrite(fp, "cmt_id:%d, ", entry.entry.cmt_id);
    $fwrite(fp, "grp_id:%d, ", entry.entry.grp_id);

    // Destination Register
    // $fwrite(fp, "rd:{ valid:%1d, idx:%02d, rnid:%d },", entry.entry.wr_reg.valid, entry.entry.wr_reg.regidx, entry.entry.wr_reg.rnid);
    // Source 1
    $fwrite(fp, "rs1:{ valid:%1d, idx:%02d, rnid:%d, ready:%01d },", entry.entry.rd_regs[0].valid, entry.entry.rd_regs[0].regidx, entry.entry.rd_regs[0].rnid, entry.entry.rd_regs[0].ready);
    // Source 2
    // $fwrite(fp, "rs2:{ valid:%1d, idx:%02d, rnid:%d, ready:%01d },", entry.entry.rd_regs[1].valid, entry.entry.rd_regs[1].regidx, entry.entry.rd_regs[1].rnid, entry.entry.rd_regs[1].ready);
    $fwrite(fp, "state:\"%s\", ", entry.state == scariv_lsu_pkg::LSU_SCHED_INIT          ? "INIT" :
                                  entry.state == scariv_lsu_pkg::LSU_SCHED_WAIT          ? "WAIT" :
                                  entry.state == scariv_lsu_pkg::LSU_SCHED_ISSUED        ? "ISSUED" :
                                  "x");
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
    $fwrite(fp, "    \"out_ptr\" : %d\n", r_entry_out_ptr_oh);
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
