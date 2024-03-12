// ------------------------------------------------------------------------
// NAME : scariv_ldq
// TYPE : module
// ------------------------------------------------------------------------
// LSU Load Queue
// ------------------------------------------------------------------------
//
// ------------------------------------------------------------------------

module scariv_ldq
  import scariv_lsu_pkg::*;
(
   input logic                           i_clk,
   input logic                           i_reset_n,

   // ROB notification interface
   rob_info_if.slave                          rob_info_if,

   input scariv_pkg::grp_id_t i_disp_valid,
   scariv_front_if.watch      disp,
   cre_ret_if.slave           cre_ret_if,

   // Hazard check for STQ -> LDQ
   ldq_haz_check_if.slave      ldq_haz_check_if[scariv_conf_pkg::LSU_INST_NUM],
   // Vector Store --> Scalar Load disambiguation check
   scalar_ldq_haz_check_if.slave scalar_ldq_haz_check_if,

   input missu_resolve_t     i_missu_resolve,
   input logic             i_missu_is_full,

   // Updates from LSU Pipeline EX2 stage
   ldq_upd_if.slave  ldq_upd_if[scariv_conf_pkg::LSU_INST_NUM],

   // Commit notification
   commit_if.monitor commit_if,
   br_upd_if.slave              br_upd_if,

   // Store Buffer Interface
   st_buffer_if.monitor         st_buffer_if,

   // UC Store Interface
   uc_write_if.monitor          uc_write_if,

   input stq_resolve_t          i_stq_rs2_resolve
   );

ldq_entry_t w_ldq_entries[scariv_conf_pkg::LDQ_SIZE];

logic [scariv_conf_pkg::LDQ_SIZE-1:0] w_entry_ready;

scariv_pkg::disp_t disp_picked_inst[scariv_conf_pkg::MEM_DISP_SIZE];
logic [scariv_conf_pkg::MEM_DISP_SIZE-1:0] disp_picked_inst_valid;
scariv_pkg::grp_id_t disp_picked_grp_id[scariv_conf_pkg::MEM_DISP_SIZE];

// logic [scariv_conf_pkg::LDQ_SIZE-1: 0] w_run_request[scariv_conf_pkg::LSU_INST_NUM];
// logic [scariv_conf_pkg::LDQ_SIZE-1: 0] w_run_request_oh[scariv_conf_pkg::LSU_INST_NUM];
// logic [scariv_conf_pkg::LSU_INST_NUM-1: 0] w_run_request_rev_oh[scariv_conf_pkg::LDQ_SIZE] ;
// logic [scariv_conf_pkg::LSU_INST_NUM-1: 0] w_ldq_replay_conflict[scariv_conf_pkg::LDQ_SIZE] ;

logic [scariv_conf_pkg::LSU_INST_NUM-1: 0] w_pipe_sel_idx_oh[scariv_conf_pkg::MEM_DISP_SIZE];

logic [scariv_conf_pkg::LDQ_SIZE-1:0]      w_entry_complete;

logic [$clog2(scariv_conf_pkg::LDQ_SIZE):0]   w_disp_picked_num;

logic [scariv_conf_pkg::LDQ_SIZE-1: 0]        w_ex2_ldq_stq_haz_vld[scariv_conf_pkg::LSU_INST_NUM];
logic [scariv_conf_pkg::LDQ_SIZE-1: 0]        w_ex2_ldq_stq_haz_vld_oh[scariv_conf_pkg::LSU_INST_NUM];


logic [scariv_conf_pkg::LDQ_SIZE-1: 0]        w_vstore_sload_haz_vld;


logic                                w_flush_valid;
assign w_flush_valid = scariv_pkg::is_flushed_commit(commit_if.commit_valid, commit_if.payload);

// --------------------------------
// Credit & Return Interface
// --------------------------------
// logic                                w_ignore_disp;
logic [$clog2(scariv_conf_pkg::LDQ_SIZE): 0] w_credit_return_val;
logic [$clog2(scariv_conf_pkg::LDQ_SIZE): 0] w_entry_dead_cnt;
logic [$clog2(scariv_conf_pkg::LDQ_SIZE): 0] w_entry_complete_cnt;

bit_cnt #(.WIDTH(scariv_conf_pkg::LDQ_SIZE)) u_entry_complete_cnt (.in(w_entry_complete), .out(w_entry_complete_cnt));

// assign w_ignore_disp = w_flush_valid & (|i_disp_valid);
assign w_credit_return_val = ((|w_entry_complete) ? w_entry_complete_cnt : 'h0) /* +
                             (w_ignore_disp       ? w_disp_picked_num    : 'h0)*/ ;

scariv_credit_return_slave
  #(.MAX_CREDITS(scariv_conf_pkg::LDQ_SIZE))
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
scariv_disp_pickup
  #(
    .PORT_BASE(0),
    .PORT_SIZE(scariv_conf_pkg::MEM_DISP_SIZE)
    )
u_scariv_disp_pickup
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
logic [scariv_conf_pkg::LDQ_SIZE-1:0]        w_in_ptr_oh;
logic [scariv_conf_pkg::LDQ_SIZE-1:0]        w_out_ptr_oh;
logic                                      w_in_valid;
logic                                      w_out_valid;

assign w_in_valid  = |disp_picked_inst_valid;
assign w_out_valid = |w_entry_complete;

/* verilator lint_off WIDTH */
bit_cnt #(.WIDTH(scariv_conf_pkg::LDQ_SIZE)) cnt_disp_valid(.in({{(scariv_conf_pkg::LDQ_SIZE-scariv_conf_pkg::MEM_DISP_SIZE){1'b0}}, disp_picked_inst_valid}), .out(w_disp_picked_num));
inoutptr_var_oh #(.SIZE(scariv_conf_pkg::LDQ_SIZE))
u_req_ptr(.i_clk (i_clk), .i_reset_n(i_reset_n),
          .i_rollback(1'b0),
          .i_in_valid (w_in_valid ), .i_in_val (w_disp_picked_num[$clog2(scariv_conf_pkg::LDQ_SIZE): 0]), .o_in_ptr_oh (w_in_ptr_oh ),
          .i_out_valid(w_out_valid), .i_out_val(w_entry_complete_cnt), .o_out_ptr_oh(w_out_ptr_oh));


generate for (genvar s_idx = 0; s_idx < scariv_conf_pkg::MEM_DISP_SIZE; s_idx++) begin : disp_idx_loop
  assign w_pipe_sel_idx_oh[s_idx] = 1 << (s_idx % scariv_conf_pkg::LSU_INST_NUM);
end
endgenerate

generate for (genvar l_idx = 0; l_idx < scariv_conf_pkg::LDQ_SIZE; l_idx++) begin : ldq_loop
  logic [scariv_conf_pkg::MEM_DISP_SIZE-1: 0]  w_input_valid;
  scariv_pkg::disp_t           w_disp_entry;
  scariv_pkg::grp_id_t         w_disp_grp_id;
  logic [scariv_conf_pkg::LSU_INST_NUM-1: 0] w_disp_pipe_sel_oh;

  for (genvar i_idx = 0; i_idx < scariv_conf_pkg::MEM_DISP_SIZE; i_idx++) begin : in_loop
    logic [scariv_conf_pkg::LDQ_SIZE-1: 0]  w_entry_ptr_oh;
    bit_rotate_left #(.WIDTH(scariv_conf_pkg::LDQ_SIZE), .VAL(i_idx)) target_bit_rotate (.i_in(w_in_ptr_oh), .o_out(w_entry_ptr_oh));
    assign w_input_valid[i_idx] = disp_picked_inst_valid[i_idx] & (w_entry_ptr_oh[l_idx]);
  end

  bit_oh_or #(.T(scariv_pkg::disp_t), .WORDS(scariv_conf_pkg::MEM_DISP_SIZE)) bit_oh_entry  (.i_oh(w_input_valid), .i_data(disp_picked_inst),   .o_selected(w_disp_entry));
  bit_oh_or #(.T(logic[scariv_conf_pkg::DISP_SIZE-1:0]), .WORDS(scariv_conf_pkg::MEM_DISP_SIZE)) bit_oh_grp_id (.i_oh(w_input_valid), .i_data(disp_picked_grp_id), .o_selected(w_disp_grp_id));
  bit_oh_or #(.T(logic[scariv_conf_pkg::LSU_INST_NUM-1: 0]), .WORDS(scariv_conf_pkg::MEM_DISP_SIZE)) bit_oh_pipe_sel (.i_oh(w_input_valid), .i_data(w_pipe_sel_idx_oh), .o_selected(w_disp_pipe_sel_oh));

  // Selection of EX3 Update signal
  ldq_ex2_update_t w_ex2_q_updates;
  logic        w_ex2_q_valid;
  ldq_ex2_upd_select u_ldq_ex2_upd_select (.ldq_upd_if(ldq_upd_if), .i_cmt_id(w_ldq_entries[l_idx].inst.cmt_id), .i_grp_id(w_ldq_entries[l_idx].inst.grp_id),
                                           .o_ex2_q_valid(w_ex2_q_valid), .o_ex2_q_updates(w_ex2_q_updates));


  logic          w_entry_flush;
  logic          w_commit_flush;
  logic          w_br_flush;
  assign w_commit_flush = scariv_pkg::is_flushed_commit(commit_if.commit_valid, commit_if.payload) & w_ldq_entries[l_idx].is_valid;
  assign w_br_flush     = scariv_pkg::is_br_flush_target(w_ldq_entries[l_idx].inst.cmt_id, w_ldq_entries[l_idx].inst.grp_id, br_upd_if.cmt_id, br_upd_if.grp_id,
                                                         br_upd_if.dead, br_upd_if.mispredict) & br_upd_if.update & w_ldq_entries[l_idx].is_valid;
  assign w_entry_flush  = w_commit_flush | w_br_flush;

  scariv_ldq_entry
    #(.entry_index (l_idx))
  u_entry
    (
     .i_clk     (i_clk    ),
     .i_reset_n (i_reset_n),

     .rob_info_if   (rob_info_if),

     .i_disp_load   (|w_input_valid),
     .i_disp_cmt_id (disp.payload.cmt_id),
     .i_disp_grp_id (w_disp_grp_id),
     .i_disp        (w_disp_entry),
     .i_disp_pipe_sel_oh(w_disp_pipe_sel_oh),

     .o_entry (w_ldq_entries[l_idx]),
     .o_entry_ready (w_entry_ready[l_idx]),

     .i_flush_valid (w_entry_flush),

     .i_entry_picked  (1'b0),

     .i_ex2_q_valid   (w_ex2_q_valid  ),
     .i_ex2_q_updates (w_ex2_q_updates),

     .i_missu_resolve (i_missu_resolve),
     .i_missu_is_full (i_missu_is_full),

     .i_st_buffer_empty (st_buffer_if.is_empty),
     .i_st_requester_empty (uc_write_if.is_empty),

     .i_stq_rs2_resolve (i_stq_rs2_resolve),

     .commit_if (commit_if),
     .br_upd_if (br_upd_if),

     .i_ldq_outptr_valid (w_out_ptr_oh[l_idx]),
     .o_entry_finish (w_entry_complete[l_idx])
     );

  // // request pickup logic
  // for (genvar p_idx = 0; p_idx < scariv_conf_pkg::LSU_INST_NUM; p_idx++) begin : pipe_loop
  //   assign w_run_request[p_idx][l_idx] = w_entry_ready[l_idx] & w_ldq_entries[l_idx].pipe_sel_idx_oh[p_idx];
  // end


  // STQ -> LDQ Hazard check
  for (genvar p_idx = 0; p_idx < scariv_conf_pkg::LSU_INST_NUM; p_idx++) begin : st_ld_haz_loop
    logic ld_is_younger_than_st;
    scariv_rough_older_check
    st_pipe_ldq_older_check
      (
       .i_cmt_id0 (ldq_haz_check_if[p_idx].ex2_cmt_id),
       .i_grp_id0 (ldq_haz_check_if[p_idx].ex2_grp_id),

       .i_cmt_id1 (w_ldq_entries[l_idx].inst.cmt_id),
       .i_grp_id1 (w_ldq_entries[l_idx].inst.grp_id),

       .o_0_older_than_1 (ld_is_younger_than_st)
       );

    logic   w_ex2_same_dw;
    assign w_ex2_same_dw = |(scariv_lsu_pkg::gen_dw(ldq_haz_check_if[p_idx].ex2_size, ldq_haz_check_if[p_idx].ex2_paddr[2:0]) &
                             scariv_lsu_pkg::gen_dw(w_ldq_entries[l_idx].size, w_ldq_entries[l_idx].addr[2:0]));
    assign w_ex2_ldq_stq_haz_vld[p_idx][l_idx] = ldq_haz_check_if[p_idx].ex2_valid &
                                                 !(w_ldq_entries[l_idx].dead | w_entry_flush) &
                                                 w_ldq_entries[l_idx].is_valid &
                                                 ld_is_younger_than_st &
                                                 w_ldq_entries[l_idx].is_get_data &
                                                 (ldq_haz_check_if[p_idx].ex2_paddr[riscv_pkg::PADDR_W-1: 3] == w_ldq_entries[l_idx].addr[riscv_pkg::PADDR_W-1: 3]) & w_ex2_same_dw;
  end // block: st_ld_haz_loop

  // Vector Store --> Scalar Load, memory disambiguation check
  logic       w_vstore_sload_same_dlen;
  logic       sload_is_younger_than_vstore;
  scariv_rough_older_check
  vst_sld_older_check
    (
     .i_cmt_id0 (scalar_ldq_haz_check_if.cmt_id),
     .i_grp_id0 (scalar_ldq_haz_check_if.grp_id),

     .i_cmt_id1 (w_ldq_entries[l_idx].inst.cmt_id),
     .i_grp_id1 (w_ldq_entries[l_idx].inst.grp_id),

     .o_0_older_than_1 (sload_is_younger_than_vstore)
     );
  assign w_vstore_sload_same_dlen = scalar_ldq_haz_check_if.paddr[riscv_pkg::PADDR_W-1: $clog2(scariv_vec_pkg::DLENB)] ==
                                    w_ldq_entries[l_idx].addr[riscv_pkg::PADDR_W-1: $clog2(scariv_vec_pkg::DLENB)];
  assign w_vstore_sload_haz_vld[l_idx] = scalar_ldq_haz_check_if.valid &
                                         !w_ldq_entries[l_idx].dead &
                                         w_ldq_entries[l_idx].is_valid &
                                         sload_is_younger_than_vstore &
                                         w_ldq_entries[l_idx].is_get_data &
                                         w_vstore_sload_same_dlen;

end endgenerate // block: ldq_loop



// ==================
// LDQ Flush Hazard
// ==================
generate for (genvar p_idx = 0; p_idx < scariv_conf_pkg::LSU_INST_NUM; p_idx++) begin : ldq_stq_haz_loop
  scariv_entry_selector
    #(
      .ENTRY_SIZE (scariv_conf_pkg::LDQ_SIZE)
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
      .WORDS (scariv_conf_pkg::LDQ_SIZE)
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
      ldq_haz_check_if[p_idx].ex3_haz_cmt_id <= w_sel_ldq_entry.inst.cmt_id;
      ldq_haz_check_if[p_idx].ex3_haz_grp_id <= w_sel_ldq_entry.inst.grp_id;
    end
  end

end
endgenerate


// ==================
// Vstore --> sload Flush Hazard
// ==================
generate if (scariv_vec_pkg::VLEN_W != 0) begin : vlsu_haz_check
  logic [scariv_conf_pkg::LDQ_SIZE-1: 0] w_vstore_sload_haz_vld_oh;

  scariv_entry_selector
    #(
      .ENTRY_SIZE (scariv_conf_pkg::LDQ_SIZE)
      )
  u_entry_selector
    (
     .i_oh_ptr       (w_out_ptr_oh),
     .i_entry_valids (w_vstore_sload_haz_vld),
     .o_entry_valid  (w_vstore_sload_haz_vld_oh)
     );

  ldq_entry_t w_sel_ldq_entry;

  bit_oh_or
    #(
      .T     (ldq_entry_t),
      .WORDS (scariv_conf_pkg::LDQ_SIZE)
      )
  u_flush_sel
    (
     .i_oh   (w_vstore_sload_haz_vld_oh),
     .i_data (w_ldq_entries),
     .o_selected(w_sel_ldq_entry)
     );

  always_comb begin
    scalar_ldq_haz_check_if.haz_valid  = |w_vstore_sload_haz_vld;
    scalar_ldq_haz_check_if.haz_cmt_id = w_sel_ldq_entry.inst.cmt_id;
    scalar_ldq_haz_check_if.haz_grp_id = w_sel_ldq_entry.inst.grp_id;
  end

end endgenerate // block: vlsu_haz_check


`ifdef SIMULATION
// credit / return management assertion
logic [scariv_conf_pkg::LDQ_SIZE-1: 0] w_ldq_valid;
logic [$clog2(scariv_conf_pkg::LDQ_SIZE): 0]      w_entry_valid_cnt;

always_ff @ (negedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
  end else begin
    if (w_disp_picked_num[$clog2(scariv_conf_pkg::LDQ_SIZE)]) begin
      $fatal(0, "w_disp_picked_num MSB == 1, too much requests inserted\n");
    end
  end
end


/* verilator lint_off WIDTH */
bit_cnt #(.WIDTH(scariv_conf_pkg::LDQ_SIZE)) u_entry_valid_cnt (.in(w_ldq_valid), .out(w_entry_valid_cnt));

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
    $fwrite(fp, "    \"scariv_ldq_entry[%d]\":{", index);
    $fwrite(fp, "valid:%d, ", entry.is_valid);
    $fwrite(fp, "pc_addr:\"0x%0x\", ", entry.inst.sim_pc_addr);
    $fwrite(fp, "inst:\"%08x\", ", entry.inst.sim_inst);

    $fwrite(fp, "cmt_id:%d, ", entry.inst.cmt_id);
    $fwrite(fp, "grp_id:%d, ", entry.inst.grp_id);

    // $fwrite(fp, "state:\"");
    // unique case (entry.state)
    //   LDQ_INIT            : $fwrite(fp, "LDQ_INIT");
    //   LDQ_EX2_RUN         : $fwrite(fp, "LDQ_EX2_RUN");
    //   LDQ_TLB_HAZ         : $fwrite(fp, "LDQ_TLB_HAZ");
    //   LDQ_ISSUE_WAIT      : $fwrite(fp, "LDQ_ISSUE_WAIT");
    //   LDQ_EX3_DONE        : $fwrite(fp, "LDQ_EX3_DONE");
    //   LDQ_WAIT_COMMIT     : $fwrite(fp, "LDQ_WAIT_COMMIT");
    //   LDQ_WAIT_ENTRY_CLR  : $fwrite(fp, "LDQ_WAIT_ENTRY_CLR");
    //   LDQ_ISSUED          : $fwrite(fp, "LDQ_ISSUED");
    //   LDQ_MISSU_EVICT_HAZ : $fwrite(fp, "LDQ_MISSU_EVICT_HAZ");
    //   LDQ_MISSU_FULL      : $fwrite(fp, "LDQ_MISSU_FULL");
    //   LDQ_WAIT_OLDEST     : $fwrite(fp, "LDQ_WAIT_OLDEST");
    //   LDQ_NONFWD_HAZ_WAIT : $fwrite(fp, "LDQ_NONFWD_HAZ_WAIT");
    //   default             : $fatal(0, "State Log lacked. %d\n", entry.state);
    // endcase // unique case (entry.state)
    $fwrite(fp, "\"");
    $fwrite(fp, "    },\n");
  end // if (entry.valid)

endfunction // dump_json

generate for (genvar l_idx = 0; l_idx < scariv_conf_pkg::LDQ_SIZE; l_idx++) begin
  assign w_ldq_valid[l_idx] = w_ldq_entries[l_idx].is_valid;
end
endgenerate

function void dump_json(int fp);
  if (|w_ldq_valid) begin
    $fwrite(fp, "  \"scariv_ldq\":{\n");
    for (int l_idx = 0; l_idx < scariv_conf_pkg::LDQ_SIZE; l_idx++) begin
      dump_entry_json (fp, w_ldq_entries[l_idx], l_idx);
    end
    $fwrite(fp, "  },\n");
  end
endfunction // dump_json

logic [63: 0] r_cycle_count;
logic [63: 0] r_ldq_max_period;
logic [63: 0] r_ldq_entry_count;

always_ff @ (negedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_ldq_max_period  <= 'h0;
    r_ldq_entry_count <= 'h0;
    r_cycle_count  <= 'h0;
  end else begin
    r_cycle_count <= r_cycle_count + 'h1;
    if (r_cycle_count % sim_pkg::COUNT_UNIT == sim_pkg::COUNT_UNIT-1) begin
      r_ldq_max_period  <= 'h0;
      r_ldq_entry_count <= 'h0;
    end else begin
      if (|w_ldq_valid) begin
        if (&w_ldq_valid) begin
          r_ldq_max_period  <= r_ldq_max_period + 'h1;
        end
        r_ldq_entry_count <= r_ldq_entry_count + $countones(w_ldq_valid);
      end
    end // else: !if(r_cycle_count % sim_pkg::COUNT_UNIT == sim_pkg::COUNT_UNIT-1)
  end // else: !if(!i_reset_n)
end // always_ff @ (negedge i_clk, negedge i_reset_n)

function void dump_perf (int fp);
  $fwrite(fp, "  \"ldq\" : {");
  $fwrite(fp, "  \"max_period\" : %5d, ", r_ldq_max_period);
  $fwrite(fp, "  \"average count\" : %5f},\n", r_ldq_entry_count / 1000.0);
endfunction // dump_perf
`endif // SIMULATION

endmodule // scariv_ldq

module ldq_ex2_upd_select
  import scariv_lsu_pkg::*;
  (
   ldq_upd_if.slave           ldq_upd_if[scariv_conf_pkg::LSU_INST_NUM],
   input scariv_pkg::cmt_id_t i_cmt_id,
   input scariv_pkg::grp_id_t i_grp_id,
   output logic               o_ex2_q_valid,
   output ldq_ex2_update_t        o_ex2_q_updates
   );

logic [scariv_conf_pkg::LSU_INST_NUM-1: 0] w_ex2_update_match;
ldq_ex2_update_t w_ex2_payloads[scariv_conf_pkg::LSU_INST_NUM];

generate for (genvar p_idx = 0; p_idx < scariv_conf_pkg::LSU_INST_NUM; p_idx++) begin : ex2_update_loop
  assign w_ex2_update_match[p_idx] = (ldq_upd_if[p_idx].ex2_update &&
                                      ldq_upd_if[p_idx].ex2_payload.cmt_id == i_cmt_id &&
                                      ldq_upd_if[p_idx].ex2_payload.grp_id == i_grp_id);
  assign w_ex2_payloads[p_idx] = ldq_upd_if[p_idx].ex2_payload;
end endgenerate

assign o_ex2_q_valid = |w_ex2_update_match;
bit_oh_or #(.T(ldq_ex2_update_t), .WORDS(scariv_conf_pkg::LSU_INST_NUM)) bit_oh_update (.i_oh(w_ex2_update_match), .i_data(w_ex2_payloads), .o_selected(o_ex2_q_updates));

endmodule // ldq_ex2_upd_select
