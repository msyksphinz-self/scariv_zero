module msrh_stq
  import msrh_lsu_pkg::*;
  (
    input logic i_clk,
    input logic i_reset_n,

    input logic         [msrh_conf_pkg::DISP_SIZE-1:0] i_disp_valid,
    disp_if.slave                                 disp,

   /* Forwarding path */
   input msrh_pkg::early_wr_t                 i_early_wr[msrh_pkg::REL_BUS_SIZE],

   // Updates from LSU Pipeline EX1 stage
   input ex1_q_update_t        i_ex1_q_updates[msrh_conf_pkg::LSU_INST_NUM],
   // Updates from LSU Pipeline EX2 stage
   input logic [msrh_conf_pkg::LSU_INST_NUM-1: 0] i_tlb_resolve,
   input ex2_q_update_t        i_ex2_q_updates[msrh_conf_pkg::LSU_INST_NUM],

   // Forwarding checker
   fwd_check_if.slave                        ex2_fwd_check_if[msrh_conf_pkg::LSU_INST_NUM],


   lsu_replay_if.master stq_replay_if[msrh_conf_pkg::LSU_INST_NUM],

   input logic [msrh_conf_pkg::LSU_INST_NUM-1: 0] i_ex3_done,

   // Commit notification
   input msrh_pkg::commit_blk_t               i_commit,

   l1d_rd_if.master                      l1d_rd_if,
   l1d_lrq_if.master                     l1d_lrq_stq_miss_if,  // Interface of Missed Data for Store

   input lrq_resolve_t     i_lrq_resolve,

   // Write Data to DCache
   l1d_wr_if.master                      l1d_wr_if,

   output                                msrh_pkg::done_rpt_t o_done_report
   );

// =========================
// Declarations
// =========================
msrh_pkg::disp_t disp_picked_inst[msrh_conf_pkg::MEM_DISP_SIZE];
logic [msrh_conf_pkg::MEM_DISP_SIZE-1:0] disp_picked_inst_valid;
logic [msrh_conf_pkg::DISP_SIZE-1:0] disp_picked_grp_id[msrh_conf_pkg::MEM_DISP_SIZE];

stq_entry_t w_stq_entries[MEM_Q_SIZE];

logic [LDQ_SIZE-1: 0] w_rerun_request[msrh_conf_pkg::LSU_INST_NUM];
logic [LDQ_SIZE-1: 0] w_rerun_request_oh[msrh_conf_pkg::LSU_INST_NUM];
logic [msrh_conf_pkg::LSU_INST_NUM-1: 0] w_rerun_request_rev_oh[STQ_SIZE] ;
logic [msrh_conf_pkg::LSU_INST_NUM-1: 0] w_stq_replay_conflict[STQ_SIZE] ;

logic                               r_l1d_rd_if_resp;

// Forwarding Logic
logic [MEM_Q_SIZE-1: 0]             w_ex2_fwd_vld[msrh_conf_pkg::LSU_INST_NUM];


function logic [msrh_conf_pkg::DCACHE_DATA_W-1: 0] merge(logic [msrh_conf_pkg::DCACHE_DATA_W-1: 0] dcache_in,
                                                         logic [riscv_pkg::XLEN_W-1: 0] st_data);
  /* verilator lint_off WIDTH */
  return dcache_in | st_data;
endfunction // merge

//
// Done Selection
//
stq_entry_t w_stq_done_entry;
logic [STQ_SIZE-1:0]  w_stq_done_oh;

logic [STQ_SIZE-1:0]  w_sq_commit_req;
logic [STQ_SIZE-1:0]  w_sq_commit_req_oh;
stq_entry_t w_stq_cmt_entry;
stq_entry_t r_st1_committed_entry;
logic [$clog2(STQ_SIZE)-1: 0] r_cmt_head_idx;

// Instruction Pick up from Dispatch
msrh_disp_pickup
  #(
    .PORT_BASE(0),
    .PORT_SIZE(msrh_conf_pkg::MEM_DISP_SIZE)
    )
u_msrh_disp_pickup
  (
   .i_disp_valid (i_disp_valid),
   .i_disp (disp),

   .o_disp_valid  (disp_picked_inst_valid),
   .o_disp        (disp_picked_inst),
   .o_disp_grp_id (disp_picked_grp_id)
   );

//
// STQ Pointer
//
logic [$clog2(STQ_SIZE)-1:0] w_in_ptr;
logic [$clog2(STQ_SIZE)-1:0] w_out_ptr;
logic                                      w_in_vld;
logic                                      w_out_vld;
logic [$clog2(STQ_SIZE):0]   w_disp_picked_num;

assign w_in_vld  = |disp_picked_inst_valid;
assign w_out_vld = o_done_report.valid;

/* verilator lint_off WIDTH */
bit_cnt #(.WIDTH(STQ_SIZE)) cnt_disp_vld(.in({{(STQ_SIZE-msrh_conf_pkg::MEM_DISP_SIZE){1'b0}}, disp_picked_inst_valid}), .out(w_disp_picked_num));
inoutptr_var #(.SIZE(STQ_SIZE)) u_req_ptr(.i_clk (i_clk), .i_reset_n(i_reset_n),
                                          .i_rollback(i_commit.commit & i_commit.flush_vld),
                                          .i_in_vld (w_in_vld ), .i_in_val (w_disp_picked_num[$clog2(STQ_SIZE)-1: 0]), .o_in_ptr (w_in_ptr ),
                                          .i_out_vld(w_out_vld), .i_out_val({{($clog2(LDQ_SIZE)-1){1'b0}}, 1'b1}), .o_out_ptr(w_out_ptr));

`ifdef SIMULATION
always_ff @ (negedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
  end else begin
    if (w_disp_picked_num[$clog2(STQ_SIZE)]) begin
      $fatal("w_disp_picked_num MSB == 1, too much requests inserted\n");
    end
  end
end
`endif

generate for (genvar s_idx = 0; s_idx < MEM_Q_SIZE; s_idx++) begin : stq_loop
  logic [msrh_conf_pkg::MEM_DISP_SIZE-1: 0]  w_input_valid;
  msrh_pkg::disp_t           w_disp_entry;
  logic [msrh_conf_pkg::DISP_SIZE-1: 0] w_disp_grp_id;
  logic [msrh_conf_pkg::LSU_INST_NUM-1: 0] r_ex2_stq_entries_recv;

  for (genvar i_idx = 0; i_idx < msrh_conf_pkg::MEM_DISP_SIZE; i_idx++) begin : in_loop
    logic [$clog2(LDQ_SIZE)-1: 0]  w_in_entry_ptr;
    assign w_in_entry_ptr = w_in_ptr + i_idx;
    assign w_input_valid[i_idx] = disp_picked_inst_valid[i_idx] & (w_in_entry_ptr == s_idx);
  end

  bit_oh_or #(.WIDTH($size(msrh_pkg::disp_t)), .WORDS(msrh_conf_pkg::MEM_DISP_SIZE)) bit_oh_entry  (.i_oh(w_input_valid), .i_data(disp_picked_inst),   .o_selected(w_disp_entry));
  bit_oh_or #(.WIDTH(msrh_conf_pkg::DISP_SIZE),     .WORDS(msrh_conf_pkg::MEM_DISP_SIZE)) bit_oh_grp_id (.i_oh(w_input_valid), .i_data(disp_picked_grp_id), .o_selected(w_disp_grp_id));

  // Selection of EX1 Update signal
  ex1_q_update_t w_ex1_q_updates;
  logic [msrh_conf_pkg::LSU_INST_NUM-1: 0] w_ex1_q_valid;
  ex1_update_select u_ex1_update_select (.i_ex1_q_updates(i_ex1_q_updates), .cmt_id(w_stq_entries[s_idx].cmt_id), .grp_id(w_stq_entries[s_idx].grp_id),
                                         .o_ex1_q_valid(w_ex1_q_valid), .o_ex1_q_updates(w_ex1_q_updates));

  // Selection of EX2 Update signal
  ex2_q_update_t w_ex2_q_updates;
  logic w_ex2_q_valid;
  ex2_update_select u_ex2_update_select (.i_ex2_q_updates(i_ex2_q_updates),
                                         .q_index(s_idx[$clog2(STQ_SIZE)-1:0]),
                                         .i_ex2_recv(r_ex2_stq_entries_recv),
                                         .o_ex2_q_valid(w_ex2_q_valid), .o_ex2_q_updates(w_ex2_q_updates));

  msrh_stq_entry
  u_msrh_stq_entry
    (
     .i_clk     (i_clk    ),
     .i_reset_n (i_reset_n),

     .i_disp_load   (|w_input_valid),
     .i_disp_cmt_id (disp.cmt_id),
     .i_disp_grp_id (w_disp_grp_id),
     .i_disp        (w_disp_entry),

     .i_early_wr (i_early_wr),

     .i_ex1_q_valid   (|w_ex1_q_valid),
     .i_ex1_q_updates (w_ex1_q_updates),

     .i_tlb_resolve (i_tlb_resolve),

     .i_ex2_q_valid  (|w_ex2_q_valid),
     .i_ex2_q_updates(w_ex2_q_updates),

     .o_entry (w_stq_entries[s_idx]),

     .i_rerun_accept (|w_rerun_request_rev_oh[s_idx] & !(|w_stq_replay_conflict[s_idx])),

     .i_commit (i_commit),

     .i_sq_op_accept(w_sq_commit_req_oh[s_idx]),
     .i_sq_l1d_rd_miss     (l1d_rd_if.miss),
     .i_sq_l1d_rd_conflict (l1d_rd_if.conflict),
     .i_sq_lrq_full    (l1d_lrq_stq_miss_if.resp_payload.full    ),
     .i_sq_lrq_conflict(l1d_lrq_stq_miss_if.resp_payload.conflict),
     .i_sq_lrq_index_oh(l1d_lrq_stq_miss_if.resp_payload.lrq_index_oh),

     .i_lrq_resolve (i_lrq_resolve),
     .i_sq_l1d_wr_conflict (l1d_wr_if.conflict),

     .i_ex3_done (i_ex3_done)
     );

    for (genvar p_idx = 0; p_idx < msrh_conf_pkg::LSU_INST_NUM; p_idx++) begin : pipe_loop
      assign w_rerun_request[p_idx][s_idx] = w_stq_entries[s_idx].state == STQ_READY &&
                                             w_stq_entries[s_idx].pipe_sel_idx_oh[p_idx];
    end
    assign w_sq_commit_req[s_idx] = (w_stq_entries[s_idx].state == STQ_COMMIT);

    // Forwarding check
    for (genvar p_idx = 0; p_idx < msrh_conf_pkg::LSU_INST_NUM; p_idx++) begin : fwd_loop
      assign w_ex2_fwd_vld[p_idx][s_idx] = w_stq_entries[s_idx].is_valid &
                                           w_stq_entries[s_idx].rs2_got_data &
                                           (w_stq_entries[s_idx].paddr == ex2_fwd_check_if[p_idx].paddr);
    end
  end // block: stq_loop
endgenerate

// ===============
// replay logic
// ===============
generate for (genvar p_idx = 0; p_idx < msrh_conf_pkg::LSU_INST_NUM; p_idx++) begin : pipe_loop
  assign stq_replay_if[p_idx].valid = |w_rerun_request[p_idx];
  stq_entry_t w_stq_replay_entry;

  bit_extract_lsb #(.WIDTH(STQ_SIZE)) u_bit_req_sel (.in(w_rerun_request[p_idx]), .out(w_rerun_request_oh[p_idx]));
  bit_oh_or #(.WIDTH($size(stq_entry_t)), .WORDS(STQ_SIZE)) select_rerun_oh  (.i_oh(w_rerun_request_oh[p_idx]), .i_data(w_stq_entries), .o_selected(w_stq_replay_entry));

  assign stq_replay_if[p_idx].issue    = w_stq_replay_entry.inst;
  assign stq_replay_if[p_idx].index_oh = w_rerun_request_oh[p_idx];

  for (genvar s_idx = 0; s_idx < STQ_SIZE; s_idx++) begin : stq_loop
    assign w_rerun_request_rev_oh[s_idx][p_idx] = w_rerun_request_oh[p_idx][s_idx];

    assign w_stq_replay_conflict[s_idx][p_idx] = stq_replay_if[p_idx].conflict & w_rerun_request[p_idx][s_idx];
  end

end // block: pipe_loop
endgenerate

// =========================
// STQ Forwarding Logic
// =========================
generate for (genvar p_idx = 0; p_idx < msrh_conf_pkg::LSU_INST_NUM; p_idx++) begin : fwd_loop
  logic [STQ_SIZE-1: 0] w_ex2_fwd_vld_oh;
  stq_entry_t w_stq_fwd_entry;

  bit_extract_msb #(.WIDTH(STQ_SIZE)) u_bit_req_sel (.in(w_ex2_fwd_vld[p_idx]), .out(w_ex2_fwd_vld_oh));
  bit_oh_or #(.WIDTH($size(stq_entry_t)), .WORDS(STQ_SIZE)) select_rerun_oh  (.i_oh(w_ex2_fwd_vld_oh), .i_data(w_stq_entries), .o_selected(w_stq_fwd_entry));

  assign ex2_fwd_check_if[p_idx].fwd_vld  = |w_ex2_fwd_vld[p_idx];
  assign ex2_fwd_check_if[p_idx].fwd_data = w_stq_fwd_entry.rs2_data;
end
endgenerate

// ===============
// Done Logic
// ===============
generate for (genvar s_idx = 0; s_idx < STQ_SIZE; s_idx++) begin : done_loop
  assign w_stq_done_oh[s_idx] = w_stq_entries[s_idx].state == STQ_DONE && (w_out_ptr == s_idx);
end
endgenerate
bit_oh_or #(.WIDTH($size(stq_entry_t)), .WORDS(STQ_SIZE)) select_rerun_oh  (.i_oh(w_stq_done_oh), .i_data(w_stq_entries), .o_selected(w_stq_done_entry));

// ==============================
// After commit, store operation
// ==============================
bit_extract_lsb #(.WIDTH(STQ_SIZE)) u_bit_cmt_sel (.in(w_sq_commit_req), .out(w_sq_commit_req_oh));
bit_oh_or #(.WIDTH($size(stq_entry_t)), .WORDS(STQ_SIZE)) select_cmt_oh  (.i_oh(w_sq_commit_req_oh), .i_data(w_stq_entries), .o_selected(w_stq_cmt_entry));

always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    // r_cmt_head_idx <= 'h0;
    r_st1_committed_entry <= 'h0;
  end else begin
    // if (w_stq_entries[r_cmt_head_idx].state == STQ_COMMIT) begin
    //   r_cmt_head_idx <= r_cmt_head_idx + 'h1;
    //   r_committed_sq <= w_stq_entries[r_cmt_head_idx];
    // end
    r_st1_committed_entry <= w_stq_cmt_entry;
  end
end // always_ff @ (posedge i_clk, negedge i_reset_n)

assign l1d_rd_if.valid = w_stq_cmt_entry.state == STQ_COMMIT;
assign l1d_rd_if.paddr = {w_stq_cmt_entry.paddr[riscv_pkg::PADDR_W-1:$clog2(DCACHE_DATA_B_W)],
                          {$clog2(DCACHE_DATA_B_W){1'b0}}};

always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_l1d_rd_if_resp <= 'b0;
    l1d_wr_if.valid <= 1'b0;
  end else begin
    r_l1d_rd_if_resp <= l1d_rd_if.valid;
    if (r_l1d_rd_if_resp) begin
      if (l1d_rd_if.hit) begin
        l1d_wr_if.valid <= 1'b1;
        l1d_wr_if.paddr <= r_st1_committed_entry.paddr;
        l1d_wr_if.data  <= {(msrh_conf_pkg::DCACHE_DATA_W / riscv_pkg::XLEN_W){r_st1_committed_entry.rs2_data}};
        l1d_wr_if.be    <= {{(DCACHE_DATA_B_W-8){8'h00}}, 8'hff} << r_st1_committed_entry.paddr[$clog2(DCACHE_DATA_B_W)-1: 0];
      end else begin
        l1d_wr_if.valid <= 1'b0;
      end
    end else begin
      l1d_wr_if.valid <= 1'b0;
    end // else: !if(r_l1d_rd_if_resp)
  end // else: !if(!i_reset_n)
end // always_ff @ (posedge i_clk, negedge i_reset_n)


assign l1d_lrq_stq_miss_if.load = r_l1d_rd_if_resp & l1d_rd_if.miss;
assign l1d_lrq_stq_miss_if.req_payload.paddr = r_st1_committed_entry.paddr;


assign o_done_report.valid   = |w_stq_done_oh;
assign o_done_report.cmt_id  = w_stq_done_entry.cmt_id;
assign o_done_report.grp_id  = w_stq_done_entry.grp_id;
assign o_done_report.exc_vld = 'h0;   // Temporary


`ifdef SIMULATION

function void dump_entry_json(int fp, stq_entry_t entry, int index);

  if (entry.is_valid) begin
    $fwrite(fp, "    \"msrh_stq_entry[%d]\":{", index);
    $fwrite(fp, "valid:%d, ", entry.is_valid);
    $fwrite(fp, "pc_addr:\"0x%0x\", ", entry.inst.pc_addr);
    $fwrite(fp, "inst:\"%08x\", ", entry.inst.inst);

    $fwrite(fp, "cmt_id:%d, ", entry.cmt_id);
    $fwrite(fp, "grp_id:%d, ", entry.grp_id);

    $fwrite(fp, "state:\"%s\", ", entry.state == STQ_INIT               ? "INIT" :
                                           entry.state == STQ_TLB_HAZ            ? "TLB_HAZ" :
                                           entry.state == STQ_READY              ? "READY" :
                                           entry.state == STQ_DONE               ? "DONE" :
                                           entry.state == STQ_COMMIT             ? "COMMIT" :
                                           entry.state == STQ_WAIT_ST_DATA       ? "WAIT_ST_DATA" :
                                           entry.state == STQ_WAIT_LRQ_REFILL    ? "WAIT_LRQ_REFILL" :
                                           entry.state == STQ_COMMIT_L1D_CHECK   ? "COMMIT_L1D_CHECK" :
                                           entry.state == STQ_L1D_UPDATE         ? "L1D_UPDATE" : "x");
    $fwrite(fp, "    },\n");
  end // if (entry.valid)

endfunction // dump_json

logic [MEM_Q_SIZE-1: 0] w_stq_valid;
generate for (genvar s_idx = 0; s_idx < MEM_Q_SIZE; s_idx++) begin
  assign w_stq_valid[s_idx] = w_stq_entries[s_idx].is_valid;
end
endgenerate

function void dump_json(int fp);
  if (|w_stq_valid) begin
    $fwrite(fp, "  \"msrh_stq\":{\n");
    for (int s_idx = 0; s_idx < MEM_Q_SIZE; s_idx++) begin
      dump_entry_json (fp, w_stq_entries[s_idx], s_idx);
    end
    $fwrite(fp, "  },\n");
  end
endfunction // dump_json
`endif // SIMULATION


endmodule // msrh_stq
