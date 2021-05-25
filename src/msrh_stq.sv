module msrh_stq
  import msrh_lsu_pkg::*;
  import decoder_lsu_ctrl_pkg::*;
  (
    input logic i_clk,
    input logic i_reset_n,

    input logic         [msrh_conf_pkg::DISP_SIZE-1:0] i_disp_valid,
    disp_if.slave                                      disp,
    cre_ret_if.slave                                   cre_ret_if,

   /* Forwarding path */
   input msrh_pkg::early_wr_t                 i_early_wr[msrh_pkg::REL_BUS_SIZE],

   // Updates from LSU Pipeline EX1 stage
   input ex1_q_update_t        i_ex1_q_updates[msrh_conf_pkg::LSU_INST_NUM],
   // Updates from LSU Pipeline EX2 stage
   input logic [msrh_conf_pkg::LSU_INST_NUM-1: 0] i_tlb_resolve,
   input ex2_q_update_t        i_ex2_q_updates[msrh_conf_pkg::LSU_INST_NUM],

   // Forwarding checker
   fwd_check_if.slave                        ex2_fwd_check_if[msrh_conf_pkg::LSU_INST_NUM],

   // From STQ to LDQ, resolve notification
   output stq_resolve_t                      o_stq_resolve,

   lsu_replay_if.master stq_replay_if[msrh_conf_pkg::LSU_INST_NUM],

   input logic [msrh_conf_pkg::LSU_INST_NUM-1: 0] i_ex3_done,

   // Commit notification
   input msrh_pkg::commit_blk_t               i_commit,

   l1d_rd_if.master                      l1d_rd_if,
   l1d_lrq_if.master                     l1d_lrq_stq_miss_if,  // Interface of Missed Data for Store

   input lrq_resolve_t     i_lrq_resolve,

   // Write Data to DCache
   l1d_wr_if.master                      l1d_wr_if,

   output                                msrh_pkg::done_rpt_t o_done_report[msrh_conf_pkg::LSU_INST_NUM]
   );

// =========================
// Declarations
// =========================
msrh_pkg::disp_t disp_picked_inst[msrh_conf_pkg::MEM_DISP_SIZE];
logic [msrh_conf_pkg::MEM_DISP_SIZE-1:0] disp_picked_inst_valid;
logic [msrh_conf_pkg::DISP_SIZE-1:0] disp_picked_grp_id[msrh_conf_pkg::MEM_DISP_SIZE];
logic [$clog2(msrh_conf_pkg::STQ_SIZE):0]   w_disp_picked_num;

stq_entry_t w_stq_entries[msrh_conf_pkg::STQ_SIZE];

logic [msrh_conf_pkg::LDQ_SIZE-1: 0] w_rerun_request[msrh_conf_pkg::LSU_INST_NUM];
logic [msrh_conf_pkg::LDQ_SIZE-1: 0] w_rerun_request_oh[msrh_conf_pkg::LSU_INST_NUM];
logic [msrh_conf_pkg::LSU_INST_NUM-1: 0] w_rerun_request_rev_oh[msrh_conf_pkg::STQ_SIZE] ;
logic [msrh_conf_pkg::LSU_INST_NUM-1: 0] w_stq_replay_conflict[msrh_conf_pkg::STQ_SIZE] ;

logic                               r_l1d_rd_if_resp;

// logic [msrh_conf_pkg::STQ_SIZE-1: 0] w_entry_dead_done;
logic [msrh_conf_pkg::STQ_SIZE-1: 0] w_stq_entry_st_finish;

// Forwarding Logic
logic [msrh_conf_pkg::STQ_SIZE-1: 0]             w_ex2_fwd_valid[msrh_conf_pkg::LSU_INST_NUM];
logic [msrh_conf_pkg::STQ_SIZE-1: 0]             w_ex2_stq_hazard[msrh_conf_pkg::LSU_INST_NUM];
logic [ 7: 0]                       w_ex2_fwd_dw[msrh_conf_pkg::LSU_INST_NUM][msrh_conf_pkg::STQ_SIZE];

logic [msrh_conf_pkg::STQ_SIZE-1: 0]             w_resolve_paddr_haz;
logic [msrh_conf_pkg::STQ_SIZE-1: 0]             w_resolve_st_data_haz;

logic                                w_flush_valid;
assign w_flush_valid = i_commit.commit & i_commit.flush_valid & !i_commit.all_dead;

// --------------------------------
// Credit & Return Interface
// --------------------------------
logic                                w_ignore_disp;
logic [$clog2(msrh_conf_pkg::STQ_SIZE): 0] w_credit_return_val;
logic [$clog2(msrh_conf_pkg::STQ_SIZE): 0] w_entry_dead_cnt;

// bit_cnt #(.WIDTH(msrh_conf_pkg::STQ_SIZE)) u_entry_dead_cnt (.in(w_entry_dead_done), .out(w_entry_dead_cnt));

assign w_ignore_disp = w_flush_valid & (|i_disp_valid);
assign w_credit_return_val = ((|w_stq_entry_st_finish) ? 'h1               : 'h0) +
                             /* ((|w_entry_dead_done)     ? w_entry_dead_cnt  : 'h0) + */
                             (w_ignore_disp            ? w_disp_picked_num : 'h0) ;

msrh_credit_return_slave
  #(.MAX_CREDITS(msrh_conf_pkg::STQ_SIZE))
u_credit_return_slave
(
 .i_clk(i_clk),
 .i_reset_n(i_reset_n),

 .i_get_return((|w_stq_entry_st_finish) |/* (|w_entry_dead_done) | */w_ignore_disp),
 .i_return_val(w_credit_return_val),

 .cre_ret_if (cre_ret_if)
 );


//
// Done Selection
//

logic [msrh_conf_pkg::STQ_SIZE-1:0]  w_sq_commit_req;
logic [msrh_conf_pkg::STQ_SIZE-1:0]  w_sq_commit_req_oh;
stq_entry_t w_stq_cmt_entry;
stq_entry_t r_st1_committed_entry;
logic [$clog2(msrh_conf_pkg::STQ_SIZE)-1: 0] r_cmt_head_idx;

logic [msrh_conf_pkg::DCACHE_DATA_W-1: 0]   w_st1_rs2_data_tmp;
logic [DCACHE_DATA_B_W-1: 0]                w_st1_rs2_byte_en_tmp;

// Instruction Pick up from Dispatch
msrh_disp_pickup
  #(
    .PORT_BASE(0),
    .PORT_SIZE(msrh_conf_pkg::MEM_DISP_SIZE)
    )
u_msrh_disp_pickup
  (
   .i_disp_valid (i_disp_valid & {msrh_conf_pkg::DISP_SIZE{w_flush_valid}}),
   .i_disp (disp),

   .o_disp_valid  (disp_picked_inst_valid),
   .o_disp        (disp_picked_inst),
   .o_disp_grp_id (disp_picked_grp_id)
   );

//
// STQ Pointer
//
logic [msrh_conf_pkg::STQ_SIZE-1:0] w_in_ptr_oh;
logic [msrh_conf_pkg::STQ_SIZE-1:0] w_out_ptr_oh;
logic                               w_in_valid;
logic                               w_out_valid;

assign w_in_valid  = |disp_picked_inst_valid;
assign w_out_valid = |w_stq_entry_st_finish;

/* verilator lint_off WIDTH */
bit_cnt #(.WIDTH(msrh_conf_pkg::STQ_SIZE)) cnt_disp_valid(.in({{(msrh_conf_pkg::STQ_SIZE-msrh_conf_pkg::MEM_DISP_SIZE){1'b0}}, disp_picked_inst_valid}), .out(w_disp_picked_num));
inoutptr_var_oh #(.SIZE(msrh_conf_pkg::STQ_SIZE)) u_req_ptr(.i_clk (i_clk), .i_reset_n(i_reset_n),
                                                            .i_rollback(1'b0),
                                                            .i_in_valid (w_in_valid ), .i_in_val (w_disp_picked_num[$clog2(msrh_conf_pkg::STQ_SIZE)-1: 0]), .o_in_ptr_oh (w_in_ptr_oh ),
                                                            .i_out_valid(w_out_valid), .i_out_val({{($clog2(msrh_conf_pkg::LDQ_SIZE)-1){1'b0}}, 1'b1}), .o_out_ptr_oh(w_out_ptr_oh));

generate for (genvar s_idx = 0; s_idx < msrh_conf_pkg::STQ_SIZE; s_idx++) begin : stq_loop
  logic [msrh_conf_pkg::MEM_DISP_SIZE-1: 0]  w_input_valid;
  msrh_pkg::disp_t           w_disp_entry;
  logic [msrh_conf_pkg::DISP_SIZE-1: 0] w_disp_grp_id;
  logic [msrh_conf_pkg::LSU_INST_NUM-1: 0] r_ex2_stq_entries_recv;

  for (genvar i_idx = 0; i_idx < msrh_conf_pkg::MEM_DISP_SIZE; i_idx++) begin : in_loop
    logic [msrh_conf_pkg::LDQ_SIZE-1: 0]  w_entry_ptr_oh;
    bit_rotate_left #(.WIDTH(msrh_conf_pkg::LDQ_SIZE), .VAL(i_idx)) target_bit_rotate (.i_in(w_in_ptr_oh), .o_out(w_entry_ptr_oh));
    assign w_input_valid[i_idx] = disp_picked_inst_valid[i_idx] & !w_flush_valid & (w_entry_ptr_oh[s_idx]);
  end

  bit_oh_or #(.T(msrh_pkg::disp_t), .WORDS(msrh_conf_pkg::MEM_DISP_SIZE)) bit_oh_entry  (.i_oh(w_input_valid), .i_data(disp_picked_inst),   .o_selected(w_disp_entry));
  bit_oh_or #(.T(logic[msrh_conf_pkg::DISP_SIZE-1:0]),     .WORDS(msrh_conf_pkg::MEM_DISP_SIZE)) bit_oh_grp_id (.i_oh(w_input_valid), .i_data(disp_picked_grp_id), .o_selected(w_disp_grp_id));

  // Selection of EX1 Update signal
  ex1_q_update_t w_ex1_q_updates;
  logic [msrh_conf_pkg::LSU_INST_NUM-1: 0] w_ex1_q_valid;
  ex1_update_select u_ex1_update_select (.i_ex1_q_updates(i_ex1_q_updates), .cmt_id(w_stq_entries[s_idx].cmt_id), .grp_id(w_stq_entries[s_idx].grp_id),
                                         .o_ex1_q_valid(w_ex1_q_valid), .o_ex1_q_updates(w_ex1_q_updates));

  // Selection of EX2 Update signal
  ex2_q_update_t w_ex2_q_updates;
  logic w_ex2_q_valid;
  ex2_update_select u_ex2_update_select (.i_ex2_q_updates(i_ex2_q_updates),
                                         .q_index(s_idx[$clog2(msrh_conf_pkg::STQ_SIZE)-1:0]),
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

     // .i_stq_entry_done (w_stq_done_oh[s_idx]),

     .i_commit (i_commit),

     .i_sq_op_accept(w_sq_commit_req_oh[s_idx]),
     .i_sq_l1d_rd_miss     (l1d_rd_if.miss),
     .i_sq_l1d_rd_conflict (l1d_rd_if.conflict),
     .i_sq_lrq_full    (l1d_lrq_stq_miss_if.resp_payload.full    ),
     .i_sq_lrq_conflict(l1d_lrq_stq_miss_if.resp_payload.conflict),
     .i_sq_lrq_index_oh(l1d_lrq_stq_miss_if.resp_payload.lrq_index_oh),

     .i_lrq_resolve (i_lrq_resolve),
     .i_sq_l1d_wr_conflict (l1d_wr_if.conflict),

     .i_ex3_done            (i_ex3_done),
     .i_stq_outptr_valid    (w_out_ptr_oh[s_idx]),
     .o_stq_entry_st_finish (w_stq_entry_st_finish[s_idx])
     );

    for (genvar p_idx = 0; p_idx < msrh_conf_pkg::LSU_INST_NUM; p_idx++) begin : pipe_loop
      assign w_rerun_request[p_idx][s_idx] = w_stq_entries[s_idx].state == STQ_READY &&
                                             w_stq_entries[s_idx].pipe_sel_idx_oh[p_idx];
    end
    assign w_sq_commit_req[s_idx] = (w_stq_entries[s_idx].state == STQ_COMMIT);

    // Forwarding check
    for (genvar p_idx = 0; p_idx < msrh_conf_pkg::LSU_INST_NUM; p_idx++) begin : fwd_loop
      logic  w_entry_older_than_fwd;
      logic  w_same_addr_region;
      logic  w_same_dw;
      logic [ 7: 0] w_entry_dw;
      assign w_entry_dw = gen_dw(w_stq_entries[s_idx].size, w_stq_entries[s_idx].paddr[2:0]);
      assign w_same_dw = is_dw_included(w_stq_entries[s_idx].size, w_stq_entries[s_idx].paddr[2:0],
                                        ex2_fwd_check_if[p_idx].paddr_dw);
      assign w_same_addr_region = w_stq_entries[s_idx].paddr[riscv_pkg::PADDR_W-1:3] == ex2_fwd_check_if[p_idx].paddr;

      assign w_ex2_fwd_valid[p_idx][s_idx] = w_stq_entries[s_idx].is_valid &
                                             w_entry_older_than_fwd &
                                             w_stq_entries[s_idx].paddr_valid &
                                             w_stq_entries[s_idx].rs2_got_data &
                                             w_same_addr_region &
                                             |(w_entry_dw & ex2_fwd_check_if[p_idx].paddr_dw);
      assign w_ex2_fwd_dw[p_idx][s_idx] = w_entry_dw & ex2_fwd_check_if[p_idx].paddr_dw;

      msrh_rough_older_check
      u_rough_older_check
        (
         .i_cmt_id0 (w_stq_entries[s_idx].cmt_id   ),
         .i_grp_id0 (w_stq_entries[s_idx].grp_id   ),
         .i_cmt_id1 (ex2_fwd_check_if[p_idx].cmt_id),
         .i_grp_id1 (ex2_fwd_check_if[p_idx].grp_id),

         .o_0_older_than_1 (w_entry_older_than_fwd)
         );

      assign w_ex2_stq_hazard[p_idx][s_idx] = ex2_fwd_check_if[p_idx].valid &
                                              w_entry_older_than_fwd &
                                              w_stq_entries[s_idx].is_valid &
                                              (w_same_addr_region & ~w_stq_entries[s_idx].rs2_got_data |  // Same region and rs2 not decided
                                               ~w_stq_entries[s_idx].paddr_valid);                        // physical addr not decided
    end // block: fwd_loop

    // STQ Hazard Resolve Notofication
    assign w_resolve_paddr_haz[s_idx] = w_stq_entries[s_idx].is_valid &
                                        (w_stq_entries[s_idx].state == STQ_INIT) &
                                        |w_ex1_q_valid &
                                        ~w_ex1_q_updates.hazard_valid;
    assign w_resolve_st_data_haz[s_idx] = w_stq_entries[s_idx].is_valid &
                                          w_stq_entries[s_idx].rs2_got_data;

    assign w_sq_commit_req_oh[s_idx] = w_sq_commit_req[s_idx] & (w_out_ptr_oh[s_idx]);
  end // block: stq_loop
endgenerate

// ===============
// replay logic
// ===============
generate for (genvar p_idx = 0; p_idx < msrh_conf_pkg::LSU_INST_NUM; p_idx++) begin : pipe_loop
  assign stq_replay_if[p_idx].valid = |w_rerun_request[p_idx];
  stq_entry_t w_stq_replay_entry;

  bit_extract_lsb #(.WIDTH(msrh_conf_pkg::STQ_SIZE)) u_bit_req_sel (.in(w_rerun_request[p_idx]), .out(w_rerun_request_oh[p_idx]));
  bit_oh_or #(.T(stq_entry_t), .WORDS(msrh_conf_pkg::STQ_SIZE)) select_rerun_oh  (.i_oh(w_rerun_request_oh[p_idx]), .i_data(w_stq_entries), .o_selected(w_stq_replay_entry));

  assign stq_replay_if[p_idx].issue    = w_stq_replay_entry.inst;
  assign stq_replay_if[p_idx].index_oh = w_rerun_request_oh[p_idx];

  for (genvar s_idx = 0; s_idx < msrh_conf_pkg::STQ_SIZE; s_idx++) begin : stq_loop
    assign w_rerun_request_rev_oh[s_idx][p_idx] = w_rerun_request_oh[p_idx][s_idx];

    assign w_stq_replay_conflict[s_idx][p_idx] = stq_replay_if[p_idx].conflict & w_rerun_request[p_idx][s_idx];
  end

end // block: pipe_loop
endgenerate

// =========================
// STQ Forwarding Logic
// =========================
generate for (genvar p_idx = 0; p_idx < msrh_conf_pkg::LSU_INST_NUM; p_idx++) begin : fwd_loop
  logic [msrh_conf_pkg::STQ_SIZE-1: 0] w_ex2_fwd_valid_oh;
  stq_entry_t                          w_stq_fwd_entry;
  logic [ 7: 0]                        w_ex2_fwd_dw_selected;

  bit_extract_msb #(.WIDTH(msrh_conf_pkg::STQ_SIZE)) u_bit_req_sel (.in(w_ex2_fwd_valid[p_idx]), .out(w_ex2_fwd_valid_oh));
  bit_oh_or #(.T(stq_entry_t), .WORDS(msrh_conf_pkg::STQ_SIZE)) select_fwd_entry  (.i_oh(w_ex2_fwd_valid_oh), .i_data(w_stq_entries), .o_selected(w_stq_fwd_entry));
  bit_oh_or #(.T(logic[7:0]),  .WORDS(msrh_conf_pkg::STQ_SIZE)) select_fwd_dw     (.i_oh(w_ex2_fwd_valid_oh), .i_data(w_ex2_fwd_dw[p_idx]), .o_selected(w_ex2_fwd_dw_selected));

  assign ex2_fwd_check_if[p_idx].fwd_valid      = |w_ex2_fwd_valid[p_idx];
  assign ex2_fwd_check_if[p_idx].fwd_dw         =  w_ex2_fwd_dw_selected;
  assign ex2_fwd_check_if[p_idx].fwd_data       =  w_stq_fwd_entry.rs2_data;
  assign ex2_fwd_check_if[p_idx].stq_hazard_vld = |w_ex2_stq_hazard[p_idx];
  assign ex2_fwd_check_if[p_idx].stq_hazard_idx =  w_ex2_stq_hazard[p_idx];
end
endgenerate

// =================================
// STQ HAZARD RESOLVE NOTIFICATION
// =================================
assign o_stq_resolve.valid            = (|w_resolve_st_data_haz) | (|w_resolve_paddr_haz);
assign o_stq_resolve.resolve_index_oh = w_resolve_st_data_haz | w_resolve_paddr_haz;

// ===============
// Done Logic
// ===============
generate for (genvar d_idx = 0; d_idx < msrh_conf_pkg::LSU_INST_NUM; d_idx++) begin : done_loop
  logic [msrh_conf_pkg::STQ_SIZE-1:0]  w_stq_done_array;
  stq_entry_t                          w_stq_done_entry;
  logic [msrh_conf_pkg::STQ_SIZE-1:0]  w_stq_done_oh;

  for (genvar s_idx = 0; s_idx < msrh_conf_pkg::STQ_SIZE; s_idx++) begin : q_loop
    assign w_stq_done_array[s_idx] = (w_stq_entries[s_idx].state == STQ_DONE_EX3) &
                                     w_stq_entries[s_idx].pipe_sel_idx_oh[d_idx];
  end
  bit_extract_msb #(.WIDTH(msrh_conf_pkg::STQ_SIZE)) u_bit_done_oh (.in(w_stq_done_array), .out(w_stq_done_oh));
  bit_oh_or #(.T(stq_entry_t), .WORDS(msrh_conf_pkg::STQ_SIZE)) select_rerun_oh  (.i_oh(w_stq_done_oh), .i_data(w_stq_entries), .o_selected(w_stq_done_entry));

  assign o_done_report[d_idx].valid   = |w_stq_done_oh;
  assign o_done_report[d_idx].cmt_id  = w_stq_done_entry.cmt_id;
  assign o_done_report[d_idx].grp_id  = w_stq_done_entry.grp_id;
  assign o_done_report[d_idx].exc_valid = 'h0;   // Temporary

end
endgenerate

// ==============================
// After commit, store operation
// ==============================

// bit_extract_lsb_ptr #(.WIDTH(msrh_conf_pkg::STQ_SIZE)) u_bit_cmt_sel (.in(w_sq_commit_req), .i_ptr(w_out_ptr_oh), .out(w_sq_commit_req_oh));
bit_oh_or #(.T(stq_entry_t), .WORDS(msrh_conf_pkg::STQ_SIZE)) select_cmt_oh  (.i_oh(w_sq_commit_req_oh), .i_data(w_stq_entries), .o_selected(w_stq_cmt_entry));

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

always_comb begin
  case (r_st1_committed_entry.size)
`ifdef RV64
    SIZE_DW : w_st1_rs2_data_tmp = {(msrh_conf_pkg::DCACHE_DATA_W / 64){r_st1_committed_entry.rs2_data[63: 0]}};
`endif // RV64
    SIZE_W  : w_st1_rs2_data_tmp = {(msrh_conf_pkg::DCACHE_DATA_W / 32){r_st1_committed_entry.rs2_data[31: 0]}};
    SIZE_H  : w_st1_rs2_data_tmp = {(msrh_conf_pkg::DCACHE_DATA_W / 16){r_st1_committed_entry.rs2_data[15: 0]}};
    SIZE_B  : w_st1_rs2_data_tmp = {(msrh_conf_pkg::DCACHE_DATA_W /  8){r_st1_committed_entry.rs2_data[ 7: 0]}};
    default : w_st1_rs2_data_tmp = 'hx;
  endcase // case (r_st1_committed_entry.pipe.size)

  case (r_st1_committed_entry.size)
`ifdef RV64
    SIZE_DW : w_st1_rs2_byte_en_tmp = {{(DCACHE_DATA_B_W-8){8'h00}}, 8'hff};
`endif // RV64
    SIZE_W  : w_st1_rs2_byte_en_tmp = {{(DCACHE_DATA_B_W-4){4'h0 }},  4'hf};
    SIZE_H  : w_st1_rs2_byte_en_tmp = {{(DCACHE_DATA_B_W-2){2'b00}},  2'h3};
    SIZE_B  : w_st1_rs2_byte_en_tmp = {{(DCACHE_DATA_B_W-1){1'b0 }},  2'h1};
    default : w_st1_rs2_byte_en_tmp = 'hx;
  endcase // case (r_st1_committed_entry.pipe.size)
end

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
        l1d_wr_if.data  <= w_st1_rs2_data_tmp;
        l1d_wr_if.be    <= w_st1_rs2_byte_en_tmp << r_st1_committed_entry.paddr[$clog2(DCACHE_DATA_B_W)-1: 0];
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


`ifdef SIMULATION
logic [msrh_conf_pkg::STQ_SIZE-1: 0] w_stq_valid;
logic [$clog2(msrh_conf_pkg::STQ_SIZE): 0]      w_entry_valid_cnt;

always_ff @ (negedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
  end else begin
    if (w_disp_picked_num[$clog2(msrh_conf_pkg::STQ_SIZE)]) begin
      $fatal("w_disp_picked_num MSB == 1, too much requests inserted\n");
    end
  end
end

/* verilator lint_off WIDTH */
bit_cnt #(.WIDTH(msrh_conf_pkg::STQ_SIZE)) u_entry_valid_cnt (.in(w_stq_valid), .out(w_entry_valid_cnt));

always_ff @ (negedge i_clk, negedge i_reset_n) begin
  if (i_reset_n) begin
    if (u_credit_return_slave.r_credits != w_entry_valid_cnt) begin
      $fatal(0, "credit and entry number different. r_credits = %d, entry_mask = %x\n",
             u_credit_return_slave.r_credits,
             w_entry_valid_cnt);
    end
  end
end


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
                                  entry.state == STQ_DONE_EX2           ? "DONE_EX2" :
                                  entry.state == STQ_DONE_EX3           ? "DONE_EX3" :
                                  entry.state == STQ_COMMIT             ? "COMMIT" :
                                  entry.state == STQ_WAIT_ST_DATA       ? "WAIT_ST_DATA" :
                                  entry.state == STQ_WAIT_LRQ_REFILL    ? "WAIT_LRQ_REFILL" :
                                  entry.state == STQ_COMMIT_L1D_CHECK   ? "COMMIT_L1D_CHECK" :
                                  entry.state == STQ_L1D_UPDATE         ? "L1D_UPDATE" : "x");
    $fwrite(fp, "    },\n");
  end // if (entry.valid)

endfunction // dump_json

generate for (genvar s_idx = 0; s_idx < msrh_conf_pkg::STQ_SIZE; s_idx++) begin
  assign w_stq_valid[s_idx] = w_stq_entries[s_idx].is_valid;
end
endgenerate

function void dump_json(int fp);
  if (|w_stq_valid) begin
    $fwrite(fp, "  \"msrh_stq\":{\n");
    for (int s_idx = 0; s_idx < msrh_conf_pkg::STQ_SIZE; s_idx++) begin
      dump_entry_json (fp, w_stq_entries[s_idx], s_idx);
    end
    $fwrite(fp, "  },\n");
  end
endfunction // dump_json
`endif // SIMULATION


endmodule // msrh_stq
