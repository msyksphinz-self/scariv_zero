module msrh_stq
  import msrh_lsu_pkg::*;
  import decoder_lsu_ctrl_pkg::*;
  (
    input logic i_clk,
    input logic i_reset_n,

    // ROB notification interface
    rob_info_if.slave                           rob_info_if,

    input logic         [msrh_conf_pkg::DISP_SIZE-1:0] i_disp_valid,
    disp_if.watch                                      disp,
    cre_ret_if.slave                                   cre_ret_if,

   /* Forwarding path */
   input msrh_pkg::early_wr_t                 i_early_wr[msrh_pkg::REL_BUS_SIZE],
   input msrh_pkg::phy_wr_t                   i_phy_wr [msrh_pkg::TGT_BUS_SIZE],
   input msrh_pkg::mispred_t                  i_mispred_lsu[msrh_conf_pkg::LSU_INST_NUM],

   // Updates from LSU Pipeline EX1 stage
   input ex1_q_update_t        i_ex1_q_updates[msrh_conf_pkg::LSU_INST_NUM],
   // Updates from LSU Pipeline EX2 stage
   input logic [msrh_conf_pkg::LSU_INST_NUM-1: 0] i_tlb_resolve,
   input ex2_q_update_t        i_ex2_q_updates[msrh_conf_pkg::LSU_INST_NUM],

   // Forwarding checker
   fwd_check_if.slave                        ex2_fwd_check_if[msrh_conf_pkg::LSU_INST_NUM],

   // STQ Hazard Check
   stq_haz_check_if.slave      stq_haz_check_if[msrh_conf_pkg::LSU_INST_NUM],

   // RMW Ordere Hazard Check
   rmw_order_check_if.slave    rmw_order_check_if[msrh_conf_pkg::LSU_INST_NUM],

   lsu_replay_if.master stq_replay_if[msrh_conf_pkg::LSU_INST_NUM],

   done_if.slave        ex3_done_if[msrh_conf_pkg::LSU_INST_NUM],

   input missu_resolve_t i_missu_resolve,
   input logic         i_missu_is_full,

   // STQ Entry rs2 get Notification
   output stq_resolve_t o_stq_rs2_resolve,

   // Commit notification
   input msrh_pkg::commit_blk_t   i_commit,
   br_upd_if.slave                br_upd_if,

   // Store Buffer Interface
   st_buffer_if.master            st_buffer_if,

   // UC Store Interface
   uc_write_if.master             uc_write_if,

   // Snoop Interface
   stq_snoop_if.slave     stq_snoop_if,

   output msrh_pkg::done_rpt_t      o_done_report[msrh_conf_pkg::LSU_INST_NUM],
   output msrh_pkg::another_flush_t o_another_flush_report[msrh_conf_pkg::LSU_INST_NUM]
   );

// =========================
// Declarations
// =========================
msrh_pkg::disp_t disp_picked_inst[msrh_conf_pkg::MEM_DISP_SIZE];
logic [msrh_conf_pkg::MEM_DISP_SIZE-1:0] disp_picked_inst_valid;
msrh_pkg::grp_id_t disp_picked_grp_id[msrh_conf_pkg::MEM_DISP_SIZE];
logic [$clog2(msrh_conf_pkg::STQ_SIZE):0]   w_disp_picked_num;

stq_entry_t w_stq_entries[msrh_conf_pkg::STQ_SIZE];
logic [msrh_conf_pkg::STQ_SIZE-1:0] w_entry_ready;

logic [msrh_conf_pkg::STQ_SIZE-1: 0] w_rerun_request[msrh_conf_pkg::LSU_INST_NUM];
logic [msrh_conf_pkg::STQ_SIZE-1: 0] w_rerun_request_oh[msrh_conf_pkg::LSU_INST_NUM];
logic [msrh_conf_pkg::LSU_INST_NUM-1: 0] w_rerun_request_rev_oh[msrh_conf_pkg::STQ_SIZE] ;
logic [msrh_conf_pkg::LSU_INST_NUM-1: 0] w_stq_replay_conflict[msrh_conf_pkg::STQ_SIZE] ;

logic [msrh_conf_pkg::LSU_INST_NUM-1: 0] w_pipe_sel_idx_oh[msrh_conf_pkg::MEM_DISP_SIZE];

// logic [msrh_conf_pkg::STQ_SIZE-1: 0] w_entry_dead_done;
logic [msrh_conf_pkg::STQ_SIZE-1: 0] w_stq_entry_st_finish;

// Forwarding Logic
logic [msrh_conf_pkg::STQ_SIZE-1: 0]             w_ex2_fwd_valid[msrh_conf_pkg::LSU_INST_NUM];
logic [ 7: 0]                       w_ex2_fwd_dw[msrh_conf_pkg::LSU_INST_NUM][msrh_conf_pkg::STQ_SIZE];

logic [msrh_conf_pkg::STQ_SIZE-1: 0] w_ex2_rmw_order_haz_valid[msrh_conf_pkg::LSU_INST_NUM];

logic [msrh_conf_pkg::STQ_SIZE-1: 0] w_ex2_stq_haz_valid[msrh_conf_pkg::LSU_INST_NUM];

// Store Buffer Selection
msrh_pkg::grp_id_t            w_stbuf_accepted_disp;
logic [msrh_conf_pkg::STQ_SIZE-1: 0]             w_stbuf_req_accepted[msrh_conf_pkg::DISP_SIZE];

logic [msrh_conf_pkg::STQ_SIZE-1: 0]             w_stq_rs2_get;

logic                                w_flush_valid;
assign w_flush_valid = msrh_pkg::is_flushed_commit(i_commit);

// --------------------------------
// Credit & Return Interface
// --------------------------------
logic                                w_ignore_disp;
logic [$clog2(msrh_conf_pkg::STQ_SIZE): 0] w_credit_return_val;
logic [$clog2(msrh_conf_pkg::STQ_SIZE): 0] w_entry_finish_cnt;

bit_cnt #(.WIDTH(msrh_conf_pkg::STQ_SIZE)) u_entry_finish_cnt (.in(w_stq_entry_st_finish), .out(w_entry_finish_cnt));

assign w_ignore_disp = w_flush_valid & (|i_disp_valid);
assign w_credit_return_val = ((|w_stq_entry_st_finish) ? w_entry_finish_cnt : 'h0) +
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

logic [msrh_conf_pkg::STQ_SIZE-1:0]  w_stbuf_req_valid;
stq_entry_t w_stq_cmt_head_entry;
stq_entry_t r_st1_committed_entry;
logic [$clog2(msrh_conf_pkg::STQ_SIZE)-1: 0] r_cmt_head_idx;

logic [msrh_conf_pkg::DCACHE_DATA_W-1: 0]   w_st1_rs2_data_tmp;
logic [DCACHE_DATA_B_W-1: 0]                w_st1_rs2_byte_en_tmp;

logic [msrh_conf_pkg::STQ_SIZE-1: 0]        w_uc_write_req_valid;


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
logic [msrh_conf_pkg::STQ_SIZE-1:0] w_in_ptr_oh;
logic [msrh_conf_pkg::STQ_SIZE-1:0] w_out_ptr_oh;
logic                               w_in_valid;
logic                               w_out_valid;

assign w_in_valid  = (|disp_picked_inst_valid) & !w_flush_valid;
assign w_out_valid = |w_stq_entry_st_finish;

/* verilator lint_off WIDTH */
bit_cnt #(.WIDTH(msrh_conf_pkg::STQ_SIZE)) cnt_disp_valid(.in({{(msrh_conf_pkg::STQ_SIZE-msrh_conf_pkg::MEM_DISP_SIZE){1'b0}}, disp_picked_inst_valid}), .out(w_disp_picked_num));
inoutptr_var_oh #(.SIZE(msrh_conf_pkg::STQ_SIZE)) u_req_ptr(.i_clk (i_clk), .i_reset_n(i_reset_n),
                                                            .i_rollback(1'b0),
                                                            .i_in_valid (w_in_valid ), .i_in_val (w_disp_picked_num[$clog2(msrh_conf_pkg::STQ_SIZE): 0]), .o_in_ptr_oh (w_in_ptr_oh ),
                                                            .i_out_valid(w_out_valid), .i_out_val(w_entry_finish_cnt), .o_out_ptr_oh(w_out_ptr_oh));

generate for (genvar s_idx = 0; s_idx < msrh_conf_pkg::MEM_DISP_SIZE; s_idx++) begin : disp_idx_loop
  assign w_pipe_sel_idx_oh[s_idx] = 1 << (s_idx % msrh_conf_pkg::LSU_INST_NUM);
end
endgenerate


logic [msrh_conf_pkg::STQ_SIZE-1: 0]                   w_stq_snoop_valid;
logic [msrh_conf_pkg::STQ_SIZE-1: 0]                   w_stq_snoop_hit ;
logic [msrh_conf_pkg::DCACHE_DATA_W-1: 0]              w_stq_snoop_data[msrh_conf_pkg::STQ_SIZE];
logic [msrh_lsu_pkg::DCACHE_DATA_B_W-1: 0]             w_stq_snoop_be  [msrh_conf_pkg::STQ_SIZE];

assign stq_snoop_if.resp_s1_valid = |w_stq_snoop_valid;
bit_or #(.WIDTH(msrh_conf_pkg::DCACHE_DATA_W),  .WORDS(msrh_conf_pkg::STQ_SIZE)) u_snoop_data_or (.i_data(w_stq_snoop_data), .o_selected(stq_snoop_if.resp_s1_data));
bit_or #(.WIDTH(msrh_lsu_pkg::DCACHE_DATA_B_W), .WORDS(msrh_conf_pkg::STQ_SIZE)) u_snoop_be_or   (.i_data(w_stq_snoop_be),   .o_selected(stq_snoop_if.resp_s1_be));


generate for (genvar s_idx = 0; s_idx < msrh_conf_pkg::STQ_SIZE; s_idx++) begin : stq_loop
  logic [msrh_conf_pkg::MEM_DISP_SIZE-1: 0]  w_input_valid;
  msrh_pkg::disp_t           w_disp_entry;
  msrh_pkg::grp_id_t w_disp_grp_id;
  logic [msrh_conf_pkg::LSU_INST_NUM-1: 0] w_disp_pipe_sel_oh;
  logic [msrh_conf_pkg::LSU_INST_NUM-1: 0] r_ex2_stq_entries_recv;
  msrh_pkg::grp_id_t w_stbuf_accept_array;

  stq_snoop_if stq_entry_snoop_if();

  for (genvar i_idx = 0; i_idx < msrh_conf_pkg::MEM_DISP_SIZE; i_idx++) begin : in_loop
    logic [msrh_conf_pkg::STQ_SIZE-1: 0]  w_entry_ptr_oh;
    bit_rotate_left #(.WIDTH(msrh_conf_pkg::STQ_SIZE), .VAL(i_idx)) target_bit_rotate (.i_in(w_in_ptr_oh), .o_out(w_entry_ptr_oh));
    assign w_input_valid[i_idx] = disp_picked_inst_valid[i_idx] & !w_flush_valid & (w_entry_ptr_oh[s_idx]);
  end

  bit_oh_or #(.T(msrh_pkg::disp_t), .WORDS(msrh_conf_pkg::MEM_DISP_SIZE)) bit_oh_entry  (.i_oh(w_input_valid), .i_data(disp_picked_inst),   .o_selected(w_disp_entry));
  bit_oh_or #(.T(logic[msrh_conf_pkg::DISP_SIZE-1:0]),     .WORDS(msrh_conf_pkg::MEM_DISP_SIZE)) bit_oh_grp_id (.i_oh(w_input_valid), .i_data(disp_picked_grp_id), .o_selected(w_disp_grp_id));
  bit_oh_or #(.T(logic[msrh_conf_pkg::LSU_INST_NUM-1: 0]), .WORDS(msrh_conf_pkg::MEM_DISP_SIZE)) bit_oh_pipe_sel (.i_oh(w_input_valid), .i_data(w_pipe_sel_idx_oh), .o_selected(w_disp_pipe_sel_oh));
  // Selection of EX1 Update signal
  ex1_q_update_t w_ex1_q_updates;
  logic [msrh_conf_pkg::LSU_INST_NUM-1: 0] w_ex1_q_valid;
  ex1_update_select u_ex1_update_select (.i_ex1_q_updates(i_ex1_q_updates), .cmt_id(w_stq_entries[s_idx].cmt_id), .grp_id(w_stq_entries[s_idx].grp_id),
                                         .o_ex1_q_valid(w_ex1_q_valid), .o_ex1_q_updates(w_ex1_q_updates));

  // Selection of EX2 Update signal
  ex2_q_update_t w_ex2_q_updates;
  logic [msrh_conf_pkg::LSU_INST_NUM-1: 0] w_ex2_q_valid;
  ex2_update_select u_ex2_update_select (.i_ex2_q_updates(i_ex2_q_updates),
                                         .q_index(s_idx[$clog2(msrh_conf_pkg::STQ_SIZE)-1:0]),
                                         .i_ex2_recv(r_ex2_stq_entries_recv),
                                         .o_ex2_q_valid(w_ex2_q_valid), .o_ex2_q_updates(w_ex2_q_updates));

  logic [msrh_conf_pkg::LSU_INST_NUM-1: 0] r_ex3_q_valid;
  always_ff @ (posedge i_clk, negedge i_reset_n) begin
    if (!i_reset_n) begin
      r_ex3_q_valid <= 'h0;
    end else begin
      r_ex3_q_valid <= w_ex2_q_valid;
    end
  end
  done_if w_ex3_done_sel_if();

  // Selection of EX3 Update signal
  ex3_done_if_select
    #(.ENTRY_SIZE(msrh_conf_pkg::STQ_SIZE))
  u_ex3_done_if_select
    (
     .i_select  (r_ex3_q_valid),
     .slave_if  (ex3_done_if),
     .master_if (w_ex3_done_sel_if)
     );

  // ---------------
  // STQ Snoop If
  // ---------------
  assign stq_entry_snoop_if.req_s0_valid = stq_snoop_if.req_s0_valid;
  assign stq_entry_snoop_if.req_s0_paddr = stq_snoop_if.req_s0_paddr;

  assign w_stq_snoop_valid[s_idx] = stq_entry_snoop_if.resp_s1_valid;
  assign w_stq_snoop_data [s_idx] = stq_entry_snoop_if.resp_s1_data;
  assign w_stq_snoop_be   [s_idx] = stq_entry_snoop_if.resp_s1_be;

  msrh_stq_entry
    #(.entry_index (s_idx))
  u_entry
    (
     .i_clk     (i_clk    ),
     .i_reset_n (i_reset_n),

     .rob_info_if (rob_info_if),

     .i_disp_load       (|w_input_valid    ),
     .i_disp_cmt_id     (disp.cmt_id       ),
     .i_disp_grp_id     (w_disp_grp_id     ),
     .i_disp            (w_disp_entry      ),
     .i_disp_pipe_sel_oh(w_disp_pipe_sel_oh),

     .i_early_wr (i_early_wr),
     .i_phy_wr   (i_phy_wr),
     .i_mispred_lsu (i_mispred_lsu),

     .i_ex1_q_valid   (|w_ex1_q_valid),
     .i_ex1_q_updates (w_ex1_q_updates),

     .i_tlb_resolve (i_tlb_resolve),

     .i_ex2_q_valid  (|w_ex2_q_valid),
     .i_ex2_q_updates(w_ex2_q_updates),

     .o_entry (w_stq_entries[s_idx]),
     .o_entry_ready (w_entry_ready[s_idx]),
     .i_entry_picked (|w_rerun_request_rev_oh[s_idx] & !(|w_stq_replay_conflict[s_idx])),

     .i_missu_resolve (i_missu_resolve),
     .i_missu_is_full (i_missu_is_full),

     .i_commit (i_commit),
     .br_upd_if (br_upd_if),

     .o_stbuf_req_valid (w_stbuf_req_valid[s_idx]),
     .i_stbuf_accept    (|w_stbuf_accept_array & (st_buffer_if.resp != msrh_lsu_pkg::ST_BUF_FULL)),

     .o_uc_write_req_valid (w_uc_write_req_valid[s_idx]),
     .i_uc_write_accept    (uc_write_if.ready),

     // Snoop Interface
     .stq_snoop_if (stq_entry_snoop_if),

     .i_st_buffer_empty (st_buffer_if.is_empty),

     .ex3_done_if           (w_ex3_done_sel_if),
     .i_stq_outptr_valid    (w_out_ptr_oh[s_idx]),
     .o_stq_entry_st_finish (w_stq_entry_st_finish[s_idx])
     );

    assign w_stq_rs2_get[s_idx] = w_stq_entries[s_idx].is_valid &
                                  (w_stq_entries[s_idx].is_rs2_get |
                                   (w_stq_entries[s_idx].state == STQ_DEAD));
    for (genvar d_idx = 0; d_idx < msrh_conf_pkg::DISP_SIZE; d_idx++) begin : stbuf_acc_loop
      assign w_stbuf_accept_array[d_idx] = w_stbuf_req_accepted[d_idx][s_idx];
    end

    for (genvar p_idx = 0; p_idx < msrh_conf_pkg::LSU_INST_NUM; p_idx++) begin : pipe_loop
      assign w_rerun_request[p_idx][s_idx] = w_entry_ready[s_idx] & w_stq_entries[s_idx].pipe_sel_idx_oh[p_idx];
    end

    // Forwarding check
    for (genvar p_idx = 0; p_idx < msrh_conf_pkg::LSU_INST_NUM; p_idx++) begin : fwd_loop
      logic  w_entry_older_than_fwd;
      logic  w_same_addr_region;
      logic  w_same_dw;
      logic [ 7: 0] w_entry_dw;
      assign w_entry_dw = gen_dw(w_stq_entries[s_idx].size, w_stq_entries[s_idx].paddr[2:0]);
      assign w_same_dw = is_dw_included(w_stq_entries[s_idx].size, w_stq_entries[s_idx].paddr[2:0],
                                        ex2_fwd_check_if[p_idx].paddr_dw);
      assign w_same_addr_region = w_stq_entries   [s_idx].paddr[riscv_pkg::PADDR_W-1:$clog2(msrh_pkg::ALEN_W/8)] ==
                                  ex2_fwd_check_if[p_idx].paddr[riscv_pkg::PADDR_W-1:$clog2(msrh_pkg::ALEN_W/8)];

      assign w_ex2_fwd_valid[p_idx][s_idx] = w_stq_entries[s_idx].is_valid &
                                             (w_stq_entries[s_idx].state != STQ_DEAD) &
                                             (w_entry_older_than_fwd | (w_stq_entries[s_idx].state == STQ_COMMIT)) &
                                             w_stq_entries[s_idx].paddr_valid &
                                             w_stq_entries[s_idx].inst.rd_regs[1].ready &
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

    end // block: fwd_loop


  // RMW Order Hazard Check
  for (genvar p_idx = 0; p_idx < msrh_conf_pkg::LSU_INST_NUM; p_idx++) begin : rmw_order_haz_loop
  logic pipe_is_younger_than_rmw;

    assign pipe_is_younger_than_rmw = msrh_pkg::id0_is_older_than_id1 (w_stq_entries[s_idx].cmt_id,
                                                                       w_stq_entries[s_idx].grp_id,
                                                                       rmw_order_check_if[p_idx].ex2_cmt_id,
                                                                       rmw_order_check_if[p_idx].ex2_grp_id);
    assign w_ex2_rmw_order_haz_valid[p_idx][s_idx] = w_stq_entries[s_idx].is_valid &
                                                     w_stq_entries[s_idx].is_rmw &
                                                     rmw_order_check_if[p_idx].ex2_valid &
                                                     (pipe_is_younger_than_rmw | w_stq_entries[s_idx].is_committed);
  end // block: rmw_order_haz_loop

  // STQ Hazard Check
  for (genvar p_idx = 0; p_idx < msrh_conf_pkg::LSU_INST_NUM; p_idx++) begin : stq_nonfwd_haz_loop
    logic pipe_is_younger_than_stq;
    logic w_same_addr_region;

    assign pipe_is_younger_than_stq = msrh_pkg::id0_is_older_than_id1 (w_stq_entries[s_idx].cmt_id,
                                                                       w_stq_entries[s_idx].grp_id,
                                                                       stq_haz_check_if[p_idx].ex2_cmt_id,
                                                                       stq_haz_check_if[p_idx].ex2_grp_id);
    assign w_same_addr_region = w_stq_entries   [s_idx].paddr    [riscv_pkg::PADDR_W-1:$clog2(msrh_pkg::ALEN_W/8)] ==
                                stq_haz_check_if[p_idx].ex2_paddr[riscv_pkg::PADDR_W-1:$clog2(msrh_pkg::ALEN_W/8)];

    assign w_ex2_stq_haz_valid[p_idx][s_idx] = w_stq_entries[s_idx].is_valid &
                                               w_stq_entries[s_idx].paddr_valid &
                                               !w_stq_entries[s_idx].inst.rd_regs[1].ready &
                                               stq_haz_check_if[p_idx].ex2_valid &
                                               w_same_addr_region &
                                               pipe_is_younger_than_stq;
  end // block: rmw_order_haz_loop


end // block: stq_loop
endgenerate

// RMW Order Hazard Check Logci
generate for (genvar p_idx = 0; p_idx < msrh_conf_pkg::LSU_INST_NUM; p_idx++) begin : rmw_haz_resp_loop
  assign rmw_order_check_if[p_idx].ex2_stq_haz_vld = |w_ex2_rmw_order_haz_valid[p_idx];
end
endgenerate

// STQ Hazard Check Logcic
generate for (genvar p_idx = 0; p_idx < msrh_conf_pkg::LSU_INST_NUM; p_idx++) begin : stq_nonfwd_haz_resp_loop
  assign stq_haz_check_if[p_idx].ex2_haz_valid = |w_ex2_stq_haz_valid[p_idx];
  assign stq_haz_check_if[p_idx].ex2_haz_index =  w_ex2_stq_haz_valid[p_idx];
end
endgenerate


// ===============
// replay logic
// ===============
generate for (genvar p_idx = 0; p_idx < msrh_conf_pkg::LSU_INST_NUM; p_idx++) begin : pipe_loop
  assign stq_replay_if[p_idx].valid = |w_rerun_request[p_idx];
  stq_entry_t w_stq_replay_entry;

  bit_extract_lsb_ptr_oh #(.WIDTH(msrh_conf_pkg::STQ_SIZE)) u_bit_req_sel (.in(w_rerun_request[p_idx]), .i_ptr_oh(w_out_ptr_oh), .out(w_rerun_request_oh[p_idx]));
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
msrh_pkg::alen_t w_aligned_rs2_data_array[msrh_conf_pkg::STQ_SIZE];
generate for (genvar s_idx = 0; s_idx < msrh_conf_pkg::STQ_SIZE; s_idx++) begin : stq_rs2_loop
  assign w_aligned_rs2_data_array[s_idx] = w_stq_entries[s_idx].rs2_data << {w_stq_entries[s_idx].paddr[$clog2(msrh_pkg::ALEN_W/8)-1:0], 3'b000};
end
endgenerate

generate for (genvar p_idx = 0; p_idx < msrh_conf_pkg::LSU_INST_NUM; p_idx++) begin : fwd_loop

  for (genvar b_idx = 0; b_idx < msrh_pkg::ALEN_W/8; b_idx++) begin : byte_loop
    msrh_pkg::alen_t                     w_stq_fwd_rs2_data;
    logic [ 7: 0]                        w_ex2_fwd_dw_selected;
    logic [msrh_conf_pkg::STQ_SIZE-1: 0] w_ex2_fwd_valid_oh;
    logic [msrh_conf_pkg::STQ_SIZE-1: 0] w_ex2_fwd_strb_valid;
    for (genvar s_idx = 0; s_idx < msrh_conf_pkg::STQ_SIZE; s_idx++) begin : stq_loop
      assign w_ex2_fwd_strb_valid[s_idx] = w_ex2_fwd_dw[p_idx][s_idx][b_idx] & w_ex2_fwd_valid[p_idx][s_idx];
    end
    bit_extract_msb_ptr_oh #(.WIDTH(msrh_conf_pkg::STQ_SIZE)) u_bit_req_sel (.in(w_ex2_fwd_strb_valid), .i_ptr_oh(w_out_ptr_oh), .out(w_ex2_fwd_valid_oh));
    bit_oh_or #(.T(msrh_pkg::alen_t), .WORDS(msrh_conf_pkg::STQ_SIZE)) select_fwd_entry  (.i_oh(w_ex2_fwd_valid_oh), .i_data(w_aligned_rs2_data_array), .o_selected(w_stq_fwd_rs2_data));

    assign ex2_fwd_check_if[p_idx].fwd_dw  [b_idx]        = |w_ex2_fwd_strb_valid;
    assign ex2_fwd_check_if[p_idx].fwd_data[b_idx*8 +: 8] =  w_stq_fwd_rs2_data[b_idx*8+:8];
  end // block: byte_loop

  assign ex2_fwd_check_if[p_idx].fwd_valid      = |w_ex2_fwd_valid[p_idx];
end // block: fwd_loop
endgenerate

// =========================
// STQ Hazard Resolve Logic
// =========================
always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    o_stq_rs2_resolve <= 'h0;
  end else begin
    o_stq_rs2_resolve.index <= w_stq_rs2_get;
  end
end

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
  assign o_done_report[d_idx].except_valid = w_stq_done_entry.except_valid;
  assign o_done_report[d_idx].except_type  = w_stq_done_entry.except_type;
  assign o_done_report[d_idx].except_tval  = {{(riscv_pkg::XLEN_W-riscv_pkg::VADDR_W){w_stq_done_entry.vaddr[riscv_pkg::VADDR_W-1]}},
                                              w_stq_done_entry.vaddr};

  assign o_another_flush_report[d_idx].valid  = w_stq_done_entry.another_flush_valid;
  assign o_another_flush_report[d_idx].cmt_id = w_stq_done_entry.another_flush_cmt_id;
  assign o_another_flush_report[d_idx].grp_id = w_stq_done_entry.another_flush_grp_id;


`ifdef SIMULATION
  // Kanata
  import "DPI-C" function void log_stage
    (
     input longint id,
     input string  stage
     );

  always_ff @ (negedge i_clk, negedge i_reset_n) begin
    if (i_reset_n) begin
      if (o_done_report[d_idx].valid) begin
        log_stage (w_stq_done_entry.kanata_id, "DO");
      end
    end
  end
`endif // SIMULATION

end
endgenerate

// ==============================
// After commit, store operation
// ==============================

/* verilator lint_off UNOPTFLAT */
msrh_pkg::grp_id_t w_sq_commit_ready_issue;
bit_oh_or
  #(.T(stq_entry_t), .WORDS(msrh_conf_pkg::STQ_SIZE))
select_cmt_oh
  (
   .i_oh(w_out_ptr_oh),
   .i_data(w_stq_entries),
   .o_selected(w_stq_cmt_head_entry)
   );

logic [msrh_lsu_pkg::ST_BUF_WIDTH/8-1:0] w_st_buffer_strb[msrh_conf_pkg::DISP_SIZE];
logic [msrh_lsu_pkg::ST_BUF_WIDTH-1:0]   w_st_buffer_data[msrh_conf_pkg::DISP_SIZE];

generate for (genvar d_idx = 0; d_idx < msrh_conf_pkg::DISP_SIZE; d_idx++) begin : stb_loop
  logic [msrh_conf_pkg::STQ_SIZE-1: 0] w_shifted_out_ptr_oh;
  logic                                w_sq_commit_valid;
  bit_rotate_left #(.WIDTH(msrh_conf_pkg::STQ_SIZE), .VAL(d_idx)) u_ptr_rotate(.i_in(w_out_ptr_oh), .o_out(w_shifted_out_ptr_oh));
  assign w_sq_commit_valid = |(w_stbuf_req_valid & w_shifted_out_ptr_oh);

  if (d_idx == 0) begin
    assign w_sq_commit_ready_issue[d_idx] = w_sq_commit_valid;
  end else begin

    assign w_sq_commit_ready_issue[d_idx] = w_sq_commit_valid &
                                            w_sq_commit_ready_issue[d_idx-1] &
                                            !w_stq_cmt_head_entry.is_rmw &
                                            !w_stq_cmt_entry.is_rmw &
                                            (w_stq_cmt_head_entry.paddr[riscv_pkg::PADDR_W-1:$clog2(msrh_lsu_pkg::ST_BUF_WIDTH/8)] ==
                                             w_stq_cmt_entry.paddr     [riscv_pkg::PADDR_W-1:$clog2(msrh_lsu_pkg::ST_BUF_WIDTH/8)]);
  end // else: !if(d_idx == 0)

  stq_entry_t w_stq_cmt_entry;
  bit_oh_or
    #(.T(stq_entry_t), .WORDS(msrh_conf_pkg::STQ_SIZE))
  select_cmt_oh
    (
     .i_oh(w_shifted_out_ptr_oh),
     .i_data(w_stq_entries),
     .o_selected(w_stq_cmt_entry)
     );

  logic [msrh_lsu_pkg::ST_BUF_WIDTH / 8-1:0] w_strb_origin;
  always_comb begin
    if (w_sq_commit_valid) begin
      case (w_stq_cmt_entry.size)
        decoder_lsu_ctrl_pkg::SIZE_DW : w_strb_origin = 'h0ff;
        decoder_lsu_ctrl_pkg::SIZE_W  : w_strb_origin = 'h00f;
        decoder_lsu_ctrl_pkg::SIZE_H  : w_strb_origin = 'h003;
        decoder_lsu_ctrl_pkg::SIZE_B  : w_strb_origin = 'h001;
        default                       : w_strb_origin = 'h0;
      endcase // case (w_stq_cmt_entry.size)
    end else begin
      w_strb_origin = 'h0;
    end // else: !if(w_sq_commit_valid)
    w_st_buffer_strb[d_idx] = w_strb_origin << w_stq_cmt_entry.paddr[$clog2(msrh_lsu_pkg::ST_BUF_WIDTH/8)-1: 0];
    w_st_buffer_data[d_idx] = w_stq_cmt_entry.rs2_data << {w_stq_cmt_entry.paddr[$clog2(msrh_lsu_pkg::ST_BUF_WIDTH/8)-1: 0], 3'b000};
  end

  assign w_stbuf_req_accepted[d_idx] = w_shifted_out_ptr_oh & {msrh_conf_pkg::STQ_SIZE{w_stbuf_accepted_disp[d_idx]}};

end // block: stb_loop
endgenerate

// ready to store_buffer
// 0010111 --> inv -> 1101000 --> lower lsb --> 1111000 --> inv --> 0000111
msrh_pkg::grp_id_t w_sq_stb_ready_inv;
bit_tree_lsb #(.WIDTH(msrh_conf_pkg::DISP_SIZE)) select_stb_bit (.in(~w_sq_commit_ready_issue), .out(w_sq_stb_ready_inv));
assign w_stbuf_accepted_disp = ~w_sq_stb_ready_inv;

// Make Store Buffer Request
assign st_buffer_if.valid = |w_stbuf_accepted_disp;
assign st_buffer_if.paddr = w_stq_cmt_head_entry.paddr;

generate for(genvar b_idx = 0; b_idx < msrh_lsu_pkg::ST_BUF_WIDTH/8; b_idx++) begin : loop_st_buf_strb
  msrh_pkg::grp_id_t w_strb_array;
  for (genvar d_idx = 0; d_idx < msrh_conf_pkg::DISP_SIZE; d_idx++) begin : stb_disp_loop
    assign w_strb_array[d_idx] = w_st_buffer_strb[d_idx][b_idx] & w_stbuf_accepted_disp[d_idx];
  end
  assign st_buffer_if.strb[b_idx] = |w_strb_array;

  msrh_pkg::grp_id_t w_strb_array_msb;
  bit_extract_msb #(.WIDTH(msrh_conf_pkg::DISP_SIZE)) extract_msb_strb (.in(w_strb_array), .out(w_strb_array_msb));

  /* verilator lint_off UNOPTFLAT */
  logic [7: 0] w_data_byte_array[msrh_conf_pkg::DISP_SIZE+1];
  assign w_data_byte_array[0] = w_st_buffer_data[0][b_idx*8 +: 8];
  for (genvar d2_idx = 0; d2_idx < msrh_conf_pkg::DISP_SIZE; d2_idx++) begin : st_buf_disp_loop
    assign w_data_byte_array[d2_idx+1] = w_strb_array_msb[d2_idx] ? w_st_buffer_data[d2_idx][b_idx*8 +: 8] : w_data_byte_array[d2_idx];
  end
  assign st_buffer_if.data[b_idx*8 +: 8] = w_data_byte_array[msrh_conf_pkg::DISP_SIZE];
end
endgenerate
assign st_buffer_if.is_rmw = w_stq_cmt_head_entry.is_rmw;
assign st_buffer_if.rmwop  = w_stq_cmt_head_entry.rmwop;
assign st_buffer_if.is_amo = w_stq_cmt_head_entry.is_amo;
`ifdef SIMULATION
assign st_buffer_if.cmt_id = w_stq_cmt_head_entry.cmt_id;
assign st_buffer_if.grp_id = w_stq_cmt_head_entry.grp_id;
`endif //SIMULATION

// ---------------------------------
// After Commit, UC-Write Operation
// ---------------------------------
stq_entry_t w_uc_write_entry_sel;
bit_oh_or #(.T(stq_entry_t), .WORDS(msrh_conf_pkg::STQ_SIZE)) select_uc_write_entry  (.i_oh(w_uc_write_req_valid), .i_data(w_stq_entries), .o_selected(w_uc_write_entry_sel));
always_comb begin
  uc_write_if.valid = |w_uc_write_req_valid;
  uc_write_if.paddr = w_uc_write_entry_sel.paddr;
  uc_write_if.data  = w_uc_write_entry_sel.rs2_data;
  uc_write_if.size  = w_uc_write_entry_sel.size;
end


`ifdef SIMULATION
logic [msrh_conf_pkg::STQ_SIZE-1: 0] w_stq_valid;
logic [$clog2(msrh_conf_pkg::STQ_SIZE): 0]      w_entry_valid_cnt;

always_ff @ (negedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
  end else begin
    if (w_disp_picked_num[$clog2(msrh_conf_pkg::STQ_SIZE)]) begin
      $fatal(0, "w_disp_picked_num MSB == 1, too much requests inserted\n");
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

    $fwrite(fp, "state:\"");
    unique case(entry.state)
      STQ_INIT             : $fwrite(fp, "INIT");
      STQ_TLB_HAZ          : $fwrite(fp, "TLB_HAZ");
      STQ_ISSUE_WAIT       : $fwrite(fp, "ISSUE_WAIT");
      STQ_DONE_EX2         : $fwrite(fp, "DONE_EX2");
      STQ_COMMIT           : $fwrite(fp, "COMMIT");
      STQ_WAIT_ST_DATA     : $fwrite(fp, "WAIT_ST_DATA");
      STQ_DEAD             : $fwrite(fp, "DEAD");
      STQ_WAIT_COMMIT      : $fwrite(fp, "WAIT_COMMIT");
      STQ_DONE_EX3         : $fwrite(fp, "DONE_EX3");
      STQ_ISSUED           : $fwrite(fp, "ISSUED");
      STQ_OLDEST_HAZ       : $fwrite(fp, "OLDEST_HAZ");
      STQ_MISSU_CONFLICT   : $fwrite(fp, "STQ_MISSU_CONFLICT");
      STQ_MISSU_EVICT_HAZ  : $fwrite(fp, "STQ_MISSU_EVICT_HAZ");
      STQ_MISSU_FULL       : $fwrite(fp, "STQ_MISSU_FULL");
      STQ_WAIT_OLDEST      : $fwrite(fp, "STQ_WAIT_OLDEST");
      STQ_WAIT_STBUF       : $fwrite(fp, "STQ_WAIT_STBUF");
      default              : $fatal(0, "State Log lacked. %d\n", entry.state);
    endcase // unique case (entry.state)
    $fwrite(fp, "\"");
    $fwrite(fp, "},\n");
  end // if (entry.valid)

endfunction // dump_json

generate for (genvar s_idx = 0; s_idx < msrh_conf_pkg::STQ_SIZE; s_idx++) begin
  assign w_stq_valid[s_idx] = w_stq_entries[s_idx].is_valid;
end
endgenerate

logic [63: 0] r_cycle_count;
logic [63: 0] r_stq_max_period;
logic [63: 0] r_stq_entry_count;

always_ff @ (negedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_stq_max_period  <= 'h0;
    r_stq_entry_count <= 'h0;
    r_cycle_count  <= 'h0;
  end else begin
    r_cycle_count <= r_cycle_count + 'h1;
    if (r_cycle_count % sim_pkg::COUNT_UNIT == sim_pkg::COUNT_UNIT-1) begin
      r_stq_max_period  <= 'h0;
      r_stq_entry_count <= 'h0;
    end else begin
      if (|w_stq_valid) begin
        if (&w_stq_valid) begin
          r_stq_max_period  <= r_stq_max_period + 'h1;
        end
        r_stq_entry_count <= r_stq_entry_count + $countones(w_stq_valid);
      end
    end // else: !if(r_cycle_count % sim_pkg::COUNT_UNIT == sim_pkg::COUNT_UNIT-1)
  end // else: !if(!i_reset_n)
end // always_ff @ (negedge i_clk, negedge i_reset_n)

function void dump_perf (int fp);
  $fwrite(fp, "  \"stq\" : {");
  $fwrite(fp, "  \"max_period\" : %5d, ", r_stq_max_period);
  $fwrite(fp, "  \"average count\" : %5f},\n", r_stq_entry_count / 1000.0);
endfunction // dump_perf

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
