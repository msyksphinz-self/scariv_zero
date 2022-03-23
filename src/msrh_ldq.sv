module msrh_ldq
  import msrh_lsu_pkg::*;
(
   input logic                           i_clk,
   input logic                           i_reset_n,

   input msrh_pkg::grp_id_t i_disp_valid,
   disp_if.watch                              disp,
   cre_ret_if.slave                           cre_ret_if,

   /* Forwarding path */
   input msrh_pkg::early_wr_t                 i_early_wr[msrh_pkg::REL_BUS_SIZE],
   input msrh_pkg::phy_wr_t                   i_phy_wr [msrh_pkg::TGT_BUS_SIZE],
   input msrh_pkg::mispred_t                  i_mispred_lsu[msrh_conf_pkg::LSU_INST_NUM],

   // Updates from LSU Pipeline EX1 stage
   input ex1_q_update_t        i_ex1_q_updates[msrh_conf_pkg::LSU_INST_NUM],
   // Updates from LSU Pipeline EX2 stage
   input logic [msrh_conf_pkg::LSU_INST_NUM-1: 0] i_tlb_resolve,
   input ex2_q_update_t        i_ex2_q_updates[msrh_conf_pkg::LSU_INST_NUM],

   // Hazard check for STQ -> LDQ
   ldq_haz_check_if.slave      ldq_haz_check_if[msrh_conf_pkg::LSU_INST_NUM],

   lsu_replay_if.master ldq_replay_if[msrh_conf_pkg::LSU_INST_NUM],

   input lrq_resolve_t     i_lrq_resolve,
   input logic             i_lrq_is_full,

   // Commit notification
   input msrh_pkg::commit_blk_t i_commit,
   br_upd_if.slave              br_upd_if,

   done_if.slave ex3_done_if[msrh_conf_pkg::LSU_INST_NUM],

   output msrh_pkg::done_rpt_t o_done_report[msrh_conf_pkg::LSU_INST_NUM]
   );

ldq_entry_t w_ldq_entries[msrh_conf_pkg::LDQ_SIZE];

logic [msrh_conf_pkg::LDQ_SIZE-1:0] w_entry_ready;

msrh_pkg::disp_t disp_picked_inst[msrh_conf_pkg::MEM_DISP_SIZE];
logic [msrh_conf_pkg::MEM_DISP_SIZE-1:0] disp_picked_inst_valid;
msrh_pkg::grp_id_t disp_picked_grp_id[msrh_conf_pkg::MEM_DISP_SIZE];

logic [msrh_conf_pkg::LDQ_SIZE-1: 0] w_run_request[msrh_conf_pkg::LSU_INST_NUM];
logic [msrh_conf_pkg::LDQ_SIZE-1: 0] w_run_request_oh[msrh_conf_pkg::LSU_INST_NUM];
logic [msrh_conf_pkg::LSU_INST_NUM-1: 0] w_run_request_rev_oh[msrh_conf_pkg::LDQ_SIZE] ;
logic [msrh_conf_pkg::LSU_INST_NUM-1: 0] w_ldq_replay_conflict[msrh_conf_pkg::LDQ_SIZE] ;

logic [msrh_conf_pkg::LSU_INST_NUM-1: 0] w_pipe_sel_idx_oh[msrh_conf_pkg::MEM_DISP_SIZE];

logic [msrh_conf_pkg::LDQ_SIZE-1:0]      w_entry_complete;

logic [$clog2(msrh_conf_pkg::LDQ_SIZE):0]   w_disp_picked_num;

logic [msrh_conf_pkg::LDQ_SIZE-1: 0]        w_ex2_ldq_stq_haz_vld[msrh_conf_pkg::LSU_INST_NUM];
logic [msrh_conf_pkg::LDQ_SIZE-1: 0]        w_ex2_ldq_stq_haz_vld_oh[msrh_conf_pkg::LSU_INST_NUM];

logic                                w_flush_valid;
assign w_flush_valid = msrh_pkg::is_flushed_commit(i_commit);

// --------------------------------
// Credit & Return Interface
// --------------------------------
// logic                                w_ignore_disp;
logic [$clog2(msrh_conf_pkg::LDQ_SIZE): 0] w_credit_return_val;
logic [$clog2(msrh_conf_pkg::LDQ_SIZE): 0] w_entry_dead_cnt;
logic [$clog2(msrh_conf_pkg::LDQ_SIZE): 0] w_entry_complete_cnt;

bit_cnt #(.WIDTH(msrh_conf_pkg::LDQ_SIZE)) u_entry_complete_cnt (.in(w_entry_complete), .out(w_entry_complete_cnt));

// assign w_ignore_disp = w_flush_valid & (|i_disp_valid);
assign w_credit_return_val = ((|w_entry_complete) ? w_entry_complete_cnt : 'h0) /* +
                             (w_ignore_disp       ? w_disp_picked_num    : 'h0)*/ ;

msrh_credit_return_slave
  #(.MAX_CREDITS(msrh_conf_pkg::LDQ_SIZE))
u_credit_return_slave
(
 .i_clk(i_clk),
 .i_reset_n(i_reset_n),

 .i_get_return((|w_entry_complete) /* | w_ignore_disp*/),
 .i_return_val(w_credit_return_val),

 .cre_ret_if (cre_ret_if)
 );

//
// Done Selection
//
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
// LDQ Pointer
//
logic [msrh_conf_pkg::LDQ_SIZE-1:0]        w_in_ptr_oh;
logic [msrh_conf_pkg::LDQ_SIZE-1:0]        w_out_ptr_oh;
logic                                      w_in_valid;
logic                                      w_out_valid;

assign w_in_valid  = |disp_picked_inst_valid;
assign w_out_valid = |w_entry_complete;

/* verilator lint_off WIDTH */
bit_cnt #(.WIDTH(msrh_conf_pkg::LDQ_SIZE)) cnt_disp_valid(.in({{(msrh_conf_pkg::LDQ_SIZE-msrh_conf_pkg::MEM_DISP_SIZE){1'b0}}, disp_picked_inst_valid}), .out(w_disp_picked_num));
inoutptr_var_oh #(.SIZE(msrh_conf_pkg::LDQ_SIZE))
u_req_ptr(.i_clk (i_clk), .i_reset_n(i_reset_n),
          .i_rollback(1'b0),
          .i_in_valid (w_in_valid ), .i_in_val (w_disp_picked_num[$clog2(msrh_conf_pkg::LDQ_SIZE): 0]), .o_in_ptr_oh (w_in_ptr_oh ),
          .i_out_valid(w_out_valid), .i_out_val(w_entry_complete_cnt), .o_out_ptr_oh(w_out_ptr_oh));


generate for (genvar s_idx = 0; s_idx < msrh_conf_pkg::MEM_DISP_SIZE; s_idx++) begin : disp_idx_loop
  assign w_pipe_sel_idx_oh[s_idx] = 1 << (s_idx % msrh_conf_pkg::LSU_INST_NUM);
end
endgenerate

generate for (genvar l_idx = 0; l_idx < msrh_conf_pkg::LDQ_SIZE; l_idx++) begin : ldq_loop
  logic [msrh_conf_pkg::MEM_DISP_SIZE-1: 0]  w_input_valid;
  msrh_pkg::disp_t           w_disp_entry;
  msrh_pkg::grp_id_t         w_disp_grp_id;
  logic [msrh_conf_pkg::LSU_INST_NUM-1: 0] w_disp_pipe_sel_oh;
  logic [msrh_conf_pkg::LSU_INST_NUM-1: 0] w_ex2_ldq_entries_recv;

  for (genvar i_idx = 0; i_idx < msrh_conf_pkg::MEM_DISP_SIZE; i_idx++) begin : in_loop
    logic [msrh_conf_pkg::LDQ_SIZE-1: 0]  w_entry_ptr_oh;
    bit_rotate_left #(.WIDTH(msrh_conf_pkg::LDQ_SIZE), .VAL(i_idx)) target_bit_rotate (.i_in(w_in_ptr_oh), .o_out(w_entry_ptr_oh));
    assign w_input_valid[i_idx] = disp_picked_inst_valid[i_idx] & (w_entry_ptr_oh[l_idx]);
  end

  bit_oh_or #(.T(msrh_pkg::disp_t), .WORDS(msrh_conf_pkg::MEM_DISP_SIZE)) bit_oh_entry  (.i_oh(w_input_valid), .i_data(disp_picked_inst),   .o_selected(w_disp_entry));
  bit_oh_or #(.T(logic[msrh_conf_pkg::DISP_SIZE-1:0]), .WORDS(msrh_conf_pkg::MEM_DISP_SIZE)) bit_oh_grp_id (.i_oh(w_input_valid), .i_data(disp_picked_grp_id), .o_selected(w_disp_grp_id));
  bit_oh_or #(.T(logic[msrh_conf_pkg::LSU_INST_NUM-1: 0]), .WORDS(msrh_conf_pkg::MEM_DISP_SIZE)) bit_oh_pipe_sel (.i_oh(w_input_valid), .i_data(w_pipe_sel_idx_oh), .o_selected(w_disp_pipe_sel_oh));

  // Selection of EX1 Update signal
  ex1_q_update_t w_ex1_q_updates;
  logic [msrh_conf_pkg::LSU_INST_NUM-1: 0] w_ex1_q_valid;
  ex1_update_select u_ex1_update_select (.i_ex1_q_updates(i_ex1_q_updates), .cmt_id(w_ldq_entries[l_idx].cmt_id), .grp_id(w_ldq_entries[l_idx].grp_id),
                                         .o_ex1_q_valid(w_ex1_q_valid), .o_ex1_q_updates(w_ex1_q_updates));

  // Selection of EX1 Update signal
  ex2_q_update_t w_ex2_q_updates;
  logic [msrh_conf_pkg::LSU_INST_NUM-1: 0] w_ex2_q_valid;
  ex2_update_select u_ex2_update_select (.i_ex2_q_updates(i_ex2_q_updates),
                                         .q_index(l_idx[$clog2(msrh_conf_pkg::LDQ_SIZE)-1:0]),
                                         .i_ex2_recv(w_ex2_ldq_entries_recv),
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
    #(.ENTRY_SIZE(msrh_conf_pkg::LDQ_SIZE))
  u_ex3_done_if_select
    (
     .i_select  (r_ex3_q_valid),
     .slave_if  (ex3_done_if),
     .master_if (w_ex3_done_sel_if)
     );

  msrh_ldq_entry
  u_msrh_ldq_entry
    (
     .i_clk     (i_clk    ),
     .i_reset_n (i_reset_n),

     .i_disp_load   (|w_input_valid),
     .i_disp_cmt_id (disp.cmt_id),
     .i_disp_grp_id (w_disp_grp_id),
     .i_disp        (w_disp_entry),
     .i_disp_pipe_sel_oh(w_disp_pipe_sel_oh),

     .i_early_wr (i_early_wr),
     .i_phy_wr   (i_phy_wr),
     .i_mispred_lsu (i_mispred_lsu),

     .i_ex1_q_valid   (|w_ex1_q_valid),
     .i_ex1_q_updates (w_ex1_q_updates),

     .i_tlb_resolve (i_tlb_resolve),

     .i_ex2_q_valid  (|w_ex2_q_valid),
     .i_ex2_q_updates(w_ex2_q_updates),

     .o_entry (w_ldq_entries[l_idx]),
     .o_entry_ready (w_entry_ready[l_idx]),
     .o_ex2_ldq_entries_recv(w_ex2_ldq_entries_recv),

     .i_entry_picked (|w_run_request_rev_oh[l_idx] & !(|w_ldq_replay_conflict[l_idx])),

     .i_lrq_resolve (i_lrq_resolve),
     .i_lrq_is_full (i_lrq_is_full),

     .i_commit (i_commit),
     .br_upd_if (br_upd_if),

     .ex3_done_if    (w_ex3_done_sel_if),

     .i_ldq_outptr_valid (w_out_ptr_oh[l_idx]),
     .o_entry_finish (w_entry_complete[l_idx])
     );

  // request pickup logic
  for (genvar p_idx = 0; p_idx < msrh_conf_pkg::LSU_INST_NUM; p_idx++) begin : pipe_loop
    assign w_run_request[p_idx][l_idx] = w_entry_ready[l_idx] & w_ldq_entries[l_idx].pipe_sel_idx_oh[p_idx];
  end


  // STQ -> LDQ Hazard check
  for (genvar p_idx = 0; p_idx < msrh_conf_pkg::LSU_INST_NUM; p_idx++) begin : st_ld_haz_loop
    logic ld_is_younger_than_st;
    msrh_rough_older_check
    st_pipe_ldq_older_check
      (
       .i_cmt_id0 (ldq_haz_check_if[p_idx].ex2_cmt_id),
       .i_grp_id0 (ldq_haz_check_if[p_idx].ex2_grp_id),

       .i_cmt_id1 (w_ldq_entries[l_idx].cmt_id),
       .i_grp_id1 (w_ldq_entries[l_idx].grp_id),

       .o_0_older_than_1 (ld_is_younger_than_st)
       );

    logic   w_ex2_same_dw;
    assign w_ex2_same_dw = |(msrh_lsu_pkg::gen_dw(ldq_haz_check_if[p_idx].ex2_size, ldq_haz_check_if[p_idx].ex2_paddr[2:0]) &
                             msrh_lsu_pkg::gen_dw(w_ldq_entries[l_idx].size, w_ldq_entries[l_idx].paddr[2:0]));
    assign w_ex2_ldq_stq_haz_vld[p_idx][l_idx] = ldq_haz_check_if[p_idx].ex2_valid &
                                                 w_ldq_entries[l_idx].is_valid &
                                                 ld_is_younger_than_st &
                                                 w_ldq_entries[l_idx].is_get_data &
                                                 (ldq_haz_check_if[p_idx].ex2_paddr[riscv_pkg::PADDR_W-1: 3] == w_ldq_entries[l_idx].paddr[riscv_pkg::PADDR_W-1: 3]) & w_ex2_same_dw;
  end // block: st_ld_haz_loop
end
endgenerate



// request logic
generate for (genvar p_idx = 0; p_idx < msrh_conf_pkg::LSU_INST_NUM; p_idx++) begin : pipe_loop
  assign ldq_replay_if[p_idx].valid = |w_run_request[p_idx];
  ldq_entry_t w_ldq_replay_entry;

  bit_extract_lsb_ptr_oh #(.WIDTH(msrh_conf_pkg::LDQ_SIZE)) u_bit_req_sel (.in(w_run_request[p_idx]), .i_ptr_oh(w_out_ptr_oh), .out(w_run_request_oh[p_idx]));
  bit_oh_or #(.T(ldq_entry_t), .WORDS(msrh_conf_pkg::LDQ_SIZE)) select_rerun_oh  (.i_oh(w_run_request_oh[p_idx]), .i_data(w_ldq_entries), .o_selected(w_ldq_replay_entry));

  assign ldq_replay_if[p_idx].issue = w_ldq_replay_entry.inst;

  assign ldq_replay_if[p_idx].index_oh = w_run_request_oh[p_idx];

  for (genvar l_idx = 0; l_idx < msrh_conf_pkg::LDQ_SIZE; l_idx++) begin : ldq_loop
    assign w_run_request_rev_oh[l_idx][p_idx] = w_run_request_oh[p_idx][l_idx];

    assign w_ldq_replay_conflict[l_idx][p_idx] = ldq_replay_if[p_idx].conflict & w_run_request[p_idx][l_idx];
  end
end
endgenerate

// ===============
// done logic
// ===============
generate for (genvar d_idx = 0; d_idx < msrh_conf_pkg::LSU_INST_NUM; d_idx++) begin : done_loop
  logic [msrh_conf_pkg::LDQ_SIZE-1:0]      w_ldq_done_array;
  ldq_entry_t                              w_ldq_done_entry;
  logic [msrh_conf_pkg::LDQ_SIZE-1: 0]     w_ldq_done_oh;

  for (genvar l_idx = 0; l_idx < msrh_conf_pkg::LDQ_SIZE; l_idx++) begin : q_loop
    assign w_ldq_done_array[l_idx] = (w_ldq_entries[l_idx].state == LDQ_EX3_DONE) &
                                     w_ldq_entries[l_idx].pipe_sel_idx_oh[d_idx];
  end
  bit_extract_msb #(.WIDTH(msrh_conf_pkg::LDQ_SIZE)) u_bit_done_oh (.in(w_ldq_done_array), .out(w_ldq_done_oh));
  bit_oh_or #(.T(ldq_entry_t), .WORDS(msrh_conf_pkg::LDQ_SIZE)) select_done_oh  (.i_oh(w_ldq_done_oh), .i_data(w_ldq_entries), .o_selected(w_ldq_done_entry));

  assign o_done_report[d_idx].valid   = |w_ldq_done_array;
  assign o_done_report[d_idx].cmt_id  = w_ldq_done_entry.cmt_id;
  assign o_done_report[d_idx].grp_id  = w_ldq_done_entry.grp_id;
  assign o_done_report[d_idx].except_valid = w_ldq_done_entry.except_valid;
  assign o_done_report[d_idx].except_type  = w_ldq_done_entry.except_type;
  assign o_done_report[d_idx].except_tval  = w_ldq_done_entry.vaddr;

end
endgenerate


// ==================
// LDQ Flush Hazard
// ==================
generate for (genvar p_idx = 0; p_idx < msrh_conf_pkg::LSU_INST_NUM; p_idx++) begin : ldq_stq_haz_loop
  msrh_entry_selector
    #(
      .ENTRY_SIZE (msrh_conf_pkg::LDQ_SIZE)
      )
  u_entry_selector
    (
     .i_oh_ptr       (w_out_ptr_oh),
     .i_entry_valids (w_ex2_ldq_stq_haz_vld[p_idx]),
     .o_entry_valid  (w_ex2_ldq_stq_haz_vld_oh[p_idx])
     );

  ldq_entry_t w_sel_ldq_entry;

  bit_oh_or
    #(
      .T     (ldq_entry_t),
      .WORDS (msrh_conf_pkg::LDQ_SIZE)
      )
  u_flush_sel
    (
     .i_oh   (w_ex2_ldq_stq_haz_vld_oh[p_idx]),
     .i_data (w_ldq_entries),
     .o_selected(w_sel_ldq_entry)
     );

  always_ff @ (posedge i_clk, negedge i_reset_n) begin
    if (!i_reset_n) begin
      ldq_haz_check_if[p_idx].ex3_haz_valid <= 1'b0;
    end else begin
      ldq_haz_check_if[p_idx].ex3_haz_valid  <= |w_ex2_ldq_stq_haz_vld[p_idx];
      ldq_haz_check_if[p_idx].ex3_haz_cmt_id <= w_sel_ldq_entry.cmt_id;
      ldq_haz_check_if[p_idx].ex3_haz_grp_id <= w_sel_ldq_entry.grp_id;
    end
  end

end
endgenerate


`ifdef SIMULATION
// credit / return management assertion
logic [msrh_conf_pkg::LDQ_SIZE-1: 0] w_ldq_valid;
logic [$clog2(msrh_conf_pkg::LDQ_SIZE): 0]      w_entry_valid_cnt;

always_ff @ (negedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
  end else begin
    if (w_disp_picked_num[$clog2(msrh_conf_pkg::LDQ_SIZE)]) begin
      $fatal(0, "w_disp_picked_num MSB == 1, too much requests inserted\n");
    end
  end
end


/* verilator lint_off WIDTH */
bit_cnt #(.WIDTH(msrh_conf_pkg::LDQ_SIZE)) u_entry_valid_cnt (.in(w_ldq_valid), .out(w_entry_valid_cnt));

always_ff @ (negedge i_clk, negedge i_reset_n) begin
  if (i_reset_n) begin
    if (u_credit_return_slave.r_credits != w_entry_valid_cnt) begin
      $fatal(0, "credit and entry number different. r_credits = %d, entry_mask = %x\n",
             u_credit_return_slave.r_credits,
             w_entry_valid_cnt);
    end
    if (w_entry_valid_cnt == 'h0 &&
        (w_in_ptr_oh != w_out_ptr_oh)) begin
      $fatal(0, "When valids=0, Must in_ptr_oh == in_ptr_oh. in_ptr_oh(%x) == out_ptr_oh(%x)\n",
             w_entry_valid_cnt,
             w_in_ptr_oh, w_out_ptr_oh);
    end
  end
end

function void dump_entry_json(int fp, ldq_entry_t entry, int index);

  if (entry.is_valid) begin
    $fwrite(fp, "    \"msrh_ldq_entry[%d]\":{", index);
    $fwrite(fp, "valid:%d, ", entry.is_valid);
    $fwrite(fp, "pc_addr:\"0x%0x\", ", entry.inst.pc_addr);
    $fwrite(fp, "inst:\"%08x\", ", entry.inst.inst);

    $fwrite(fp, "cmt_id:%d, ", entry.cmt_id);
    $fwrite(fp, "grp_id:%d, ", entry.grp_id);

    $fwrite(fp, "state:\"");
    unique case (entry.state)
      LDQ_INIT            : $fwrite(fp, "LDQ_INIT");
      LDQ_EX2_RUN         : $fwrite(fp, "LDQ_EX2_RUN");
      LDQ_LRQ_CONFLICT    : $fwrite(fp, "LDQ_LRQ_CONFLICT");
      LDQ_TLB_HAZ         : $fwrite(fp, "LDQ_TLB_HAZ");
      LDQ_ISSUE_WAIT      : $fwrite(fp, "LDQ_ISSUE_WAIT");
      LDQ_EX3_DONE        : $fwrite(fp, "LDQ_EX3_DONE");
      LDQ_WAIT_COMMIT     : $fwrite(fp, "LDQ_WAIT_COMMIT");
      LDQ_WAIT_ENTRY_CLR  : $fwrite(fp, "LDQ_WAIT_ENTRY_CLR");
      LDQ_ISSUED          : $fwrite(fp, "LDQ_ISSUED");
      LDQ_LRQ_EVICT_HAZ   : $fwrite(fp, "LDQ_LRQ_EVICT_HAZ");
      LDQ_LRQ_FULL        : $fwrite(fp, "LDQ_LRQ_FULL");
      default             : $fatal(0, "State Log lacked. %d\n", entry.state);
    endcase // unique case (entry.state)
    $fwrite(fp, "\"");
    $fwrite(fp, "    },\n");
  end // if (entry.valid)

endfunction // dump_json

generate for (genvar l_idx = 0; l_idx < msrh_conf_pkg::LDQ_SIZE; l_idx++) begin
  assign w_ldq_valid[l_idx] = w_ldq_entries[l_idx].is_valid;
end
endgenerate

function void dump_json(int fp);
  if (|w_ldq_valid) begin
    $fwrite(fp, "  \"msrh_ldq\":{\n");
    for (int l_idx = 0; l_idx < msrh_conf_pkg::LDQ_SIZE; l_idx++) begin
      dump_entry_json (fp, w_ldq_entries[l_idx], l_idx);
    end
    $fwrite(fp, "  },\n");
  end
endfunction // dump_json
`endif // SIMULATION

endmodule // msrh_ldq

module ex1_update_select
  import msrh_lsu_pkg::*;
  (
   input ex1_q_update_t i_ex1_q_updates[msrh_conf_pkg::LSU_INST_NUM],
   input msrh_pkg::cmt_id_t cmt_id,
   input msrh_pkg::grp_id_t grp_id,
   output [msrh_conf_pkg::LSU_INST_NUM-1: 0]   o_ex1_q_valid,
   output                                 ex1_q_update_t o_ex1_q_updates
   );

logic [msrh_conf_pkg::LSU_INST_NUM-1: 0] w_ex1_update_match;

for (genvar p_idx = 0; p_idx < msrh_conf_pkg::LSU_INST_NUM; p_idx++) begin : ex1_update_loop
  assign o_ex1_q_valid[p_idx] = i_ex1_q_updates[p_idx].update &&
                                i_ex1_q_updates[p_idx].cmt_id == cmt_id &&
                                i_ex1_q_updates[p_idx].grp_id == grp_id;
end

bit_oh_or #(.T(ex1_q_update_t), .WORDS(msrh_conf_pkg::LSU_INST_NUM)) bit_oh_update (.i_oh(o_ex1_q_valid), .i_data(i_ex1_q_updates), .o_selected(o_ex1_q_updates));

endmodule // ex1_update_select


module ex2_update_select
  import msrh_lsu_pkg::*;
  (
   input ex2_q_update_t i_ex2_q_updates[msrh_conf_pkg::LSU_INST_NUM],
   input logic [$clog2(msrh_conf_pkg::LDQ_SIZE)-1: 0] q_index,
   input logic [msrh_conf_pkg::LSU_INST_NUM-1: 0]     i_ex2_recv,
   output logic [msrh_conf_pkg::LSU_INST_NUM-1: 0]    o_ex2_q_valid,
   output                                             ex2_q_update_t o_ex2_q_updates
   );

logic [msrh_conf_pkg::LSU_INST_NUM-1: 0] w_ex2_update_match;

generate for (genvar p_idx = 0; p_idx < msrh_conf_pkg::LSU_INST_NUM; p_idx++) begin : ex2_update_loop
  assign w_ex2_update_match[p_idx] = (i_ex2_q_updates[p_idx].update &&
                                      i_ex2_q_updates[p_idx].index_oh[q_index]) |
                                     i_ex2_recv[p_idx];
end
endgenerate

assign o_ex2_q_valid = w_ex2_update_match;
bit_oh_or #(.T(ex2_q_update_t), .WORDS(msrh_conf_pkg::LSU_INST_NUM)) bit_oh_update (.i_oh(w_ex2_update_match), .i_data(i_ex2_q_updates), .o_selected(o_ex2_q_updates));

endmodule // ex2_update_select

module ex3_done_if_select
  import msrh_lsu_pkg::*;
#(
  parameter ENTRY_SIZE = 32
  )
(
 input logic [msrh_conf_pkg::LSU_INST_NUM-1: 0] i_select,
 done_if.slave        slave_if [msrh_conf_pkg::LSU_INST_NUM],
 done_if.master       master_if
 );

typedef struct packed {
  logic                                done;
  logic [ENTRY_SIZE-1: 0]              index_oh;
  logic                                except_valid;
  msrh_pkg::except_t                   except_type;
  // For flushing another instruction
  logic                                another_flush_valid;
  msrh_pkg::cmt_id_t       another_flush_cmt_id;
  msrh_pkg::grp_id_t another_flush_grp_id;
} done_if_t;

done_if_t w_done_array [msrh_conf_pkg::LSU_INST_NUM];
done_if_t w_done_selected;

generate for (genvar i=0; i < msrh_conf_pkg::LSU_INST_NUM; i++) begin
  assign w_done_array[i].done                 = slave_if[i].done                ;
  assign w_done_array[i].index_oh             = slave_if[i].index_oh            ;
  assign w_done_array[i].except_valid         = slave_if[i].except_valid        ;
  assign w_done_array[i].except_type          = slave_if[i].except_type         ;
  assign w_done_array[i].another_flush_valid  = slave_if[i].another_flush_valid ;
  assign w_done_array[i].another_flush_cmt_id = slave_if[i].another_flush_cmt_id;
  assign w_done_array[i].another_flush_grp_id = slave_if[i].another_flush_grp_id;
end
endgenerate

bit_oh_or
  #(
    .T(done_if_t),
    .WORDS(msrh_conf_pkg::LSU_INST_NUM)
    )
bit_oh_update
  (
   .i_oh(i_select),
   .i_data(w_done_array),
   .o_selected(w_done_selected)
   );

assign master_if.done                 = w_done_selected.done                ;
assign master_if.index_oh             = w_done_selected.index_oh            ;
assign master_if.except_valid         = w_done_selected.except_valid        ;
assign master_if.except_type          = w_done_selected.except_type         ;
assign master_if.another_flush_valid  = w_done_selected.another_flush_valid ;
assign master_if.another_flush_cmt_id = w_done_selected.another_flush_cmt_id;
assign master_if.another_flush_grp_id = w_done_selected.another_flush_grp_id;

endmodule // ex3_done_if_select
