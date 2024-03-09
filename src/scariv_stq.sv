// ------------------------------------------------------------------------
// NAME : scariv_stq
// TYPE : module
// ------------------------------------------------------------------------
// Store Queue
// ------------------------------------------------------------------------
// ------------------------------------------------------------------------

module scariv_stq
  import scariv_lsu_pkg::*;
  import decoder_lsu_ctrl_pkg::*;
  (
    input logic i_clk,
    input logic i_reset_n,

    // ROB notification interface
    rob_info_if.slave                           rob_info_if,

    input logic         [scariv_conf_pkg::DISP_SIZE-1:0] i_disp_valid,
    scariv_front_if.watch                                      disp,
    cre_ret_if.slave                                   cre_ret_if,

   /* Forwarding path */
   early_wr_if.slave    early_wr_in_if[scariv_pkg::REL_BUS_SIZE],
   lsu_mispred_if.slave mispred_in_if [scariv_conf_pkg::LSU_INST_NUM],
   phy_wr_if.slave      phy_wr_in_if  [scariv_pkg::TGT_BUS_SIZE],

   // Store Data Read Interface
   regread_if.master   int_rs2_regread[scariv_conf_pkg::STQ_REGRD_PORT_NUM],
   regread_if.master   fp_rs2_regread [scariv_conf_pkg::STQ_REGRD_PORT_NUM],

   stq_upd_if.slave stq_upd_if[scariv_conf_pkg::LSU_INST_NUM],

   // Forwarding checker
   fwd_check_if.slave ex2_fwd_check_if[scariv_conf_pkg::LSU_INST_NUM],

   // STQ Hazard Check
   stq_haz_check_if.slave  stq_haz_check_if[scariv_conf_pkg::LSU_INST_NUM],

   // RMW Ordere Hazard Check
   rmw_order_check_if.slave  rmw_order_check_if[scariv_conf_pkg::LSU_INST_NUM],

   input logic           i_missu_is_empty,

   output logic          o_stq_rmw_existed,

   // STQ Entry rs2 get Notification
   output stq_resolve_t o_stq_rs2_resolve,

   // Commit notification
   commit_if.monitor   commit_if,
   br_upd_if.slave                br_upd_if,

   // Store Buffer Interface
   st_buffer_if.master            st_buffer_if,

   // UC Store Interface
   uc_write_if.master             uc_write_if,

   // Snoop Interface
   stq_snoop_if.slave     stq_snoop_if
);

// =========================
// Declarations
// =========================

localparam STQ_W = $clog2(scariv_conf_pkg::STQ_SIZE);
typedef logic [STQ_W-1: 0] stqsize_t;

localparam ST_BUF_MERGE_ENTRY_SIZE = 2;

scariv_pkg::disp_t disp_picked_inst[scariv_conf_pkg::MEM_DISP_SIZE];
logic [scariv_conf_pkg::MEM_DISP_SIZE-1:0] disp_picked_inst_valid;
scariv_pkg::grp_id_t disp_picked_grp_id[scariv_conf_pkg::MEM_DISP_SIZE];
logic [$clog2(scariv_conf_pkg::STQ_SIZE):0]   w_disp_picked_num;
stq_entry_t w_stq_entry_in[scariv_conf_pkg::MEM_DISP_SIZE];
// Only used in Detailed Forwarding Mode:
scariv_pkg::alen_t r_rs2_data_array[scariv_conf_pkg::STQ_SIZE];


stq_entry_t w_stq_entries[scariv_conf_pkg::STQ_SIZE];
logic [scariv_conf_pkg::STQ_SIZE-1: 0]        w_stq_valid;

logic [scariv_conf_pkg::LSU_INST_NUM-1: 0] w_pipe_sel_idx_oh[scariv_conf_pkg::MEM_DISP_SIZE];

logic [scariv_conf_pkg::STQ_SIZE-1: 0] w_rs2_phy_read_valids   [scariv_conf_pkg::STQ_REGRD_PORT_NUM-1: 0];
logic [scariv_conf_pkg::STQ_SIZE-1: 0] w_rs2_phy_read_valids_oh[scariv_conf_pkg::STQ_REGRD_PORT_NUM-1: 0];

logic [scariv_conf_pkg::STQ_SIZE-1: 0] w_rs2_rel_read_valids   [scariv_conf_pkg::STQ_REGRD_PORT_NUM-1: 0];
logic [scariv_conf_pkg::STQ_SIZE-1: 0] w_rs2_rel_read_valids_oh[scariv_conf_pkg::STQ_REGRD_PORT_NUM-1: 0];

logic              w_ex1_rs2_rel_data_valid  [scariv_conf_pkg::STQ_REGRD_PORT_NUM-1: 0];
stqsize_t          w_ex1_rs2_rel_stq_ptr     [scariv_conf_pkg::STQ_REGRD_PORT_NUM-1: 0];
logic              w_ex1_rs2_rel_mispredicted[scariv_conf_pkg::STQ_REGRD_PORT_NUM-1: 0];
scariv_pkg::alen_t w_ex1_rs2_rel_data        [scariv_conf_pkg::STQ_REGRD_PORT_NUM-1: 0];

logic              w_ex1_rs2_phy_data_valid  [scariv_conf_pkg::STQ_REGRD_PORT_NUM-1: 0];
stqsize_t          w_ex1_rs2_phy_stq_ptr     [scariv_conf_pkg::STQ_REGRD_PORT_NUM-1: 0];
scariv_pkg::alen_t w_ex1_rs2_phy_data        [scariv_conf_pkg::STQ_REGRD_PORT_NUM-1: 0];

// Coarse Forwarding Mode: Forwarding Distributed RAM read
stqsize_t          w_ex2_fwd_valid_ptr    [scariv_conf_pkg::LSU_INST_NUM];
scariv_pkg::alen_t w_ex2_stq_fwd_rs2_data [scariv_conf_pkg::LSU_INST_NUM];
// Read stora data from distributed RAM
stqsize_t          w_stbuf_rs2_out_ptr [ST_BUF_MERGE_ENTRY_SIZE];
scariv_pkg::alen_t w_stq_stbuf_rs2_data[ST_BUF_MERGE_ENTRY_SIZE];

logic [scariv_conf_pkg::STQ_SIZE-1: 0] w_stq_rmw_existed;
assign o_stq_rmw_existed = |w_stq_rmw_existed;

// logic [scariv_conf_pkg::STQ_SIZE-1: 0] w_entry_dead_done;
logic [scariv_conf_pkg::STQ_SIZE-1: 0] w_stq_entry_st_finish;

// Forwarding Logic
logic [scariv_conf_pkg::STQ_SIZE-1: 0]             w_ex2_fwd_valid[scariv_conf_pkg::LSU_INST_NUM];
logic [ 7: 0]                       w_ex2_fwd_dw[scariv_conf_pkg::LSU_INST_NUM][scariv_conf_pkg::STQ_SIZE];

logic [scariv_conf_pkg::STQ_SIZE-1: 0] w_ex2_rmw_order_haz_valid[scariv_conf_pkg::LSU_INST_NUM];

logic [scariv_conf_pkg::STQ_SIZE-1: 0] w_ex2_stq_haz_valid[scariv_conf_pkg::LSU_INST_NUM];

// Store Buffer Selection
logic [ST_BUF_MERGE_ENTRY_SIZE-1: 0]   w_stbuf_accepted_disp;
logic [scariv_conf_pkg::STQ_SIZE-1: 0] w_stbuf_req_accepted[scariv_conf_pkg::DISP_SIZE];

logic [scariv_conf_pkg::STQ_SIZE-1: 0] w_stq_rs2_get;

logic                                w_flush_valid;
assign w_flush_valid = commit_if.is_flushed_commit();

// --------------------------------
// Credit & Return Interface
// --------------------------------
logic                                w_ignore_disp;
logic [$clog2(scariv_conf_pkg::STQ_SIZE): 0] w_credit_return_val;
logic [$clog2(scariv_conf_pkg::STQ_SIZE): 0] w_entry_finish_cnt;

bit_cnt #(.WIDTH(scariv_conf_pkg::STQ_SIZE)) u_entry_finish_cnt (.in(w_stq_entry_st_finish), .out(w_entry_finish_cnt));

assign w_ignore_disp = w_flush_valid & (|i_disp_valid);
assign w_credit_return_val = ((|w_stq_entry_st_finish) ? w_entry_finish_cnt : 'h0) +
                             (w_ignore_disp            ? w_disp_picked_num : 'h0) ;

scariv_credit_return_slave
  #(.MAX_CREDITS(scariv_conf_pkg::STQ_SIZE))
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

logic [scariv_conf_pkg::STQ_SIZE-1:0]  w_stbuf_req_valid;
stq_entry_t w_stq_cmt_head_entry;
stq_entry_t r_st1_committed_entry;
stqsize_t r_cmt_head_idx;

logic [scariv_conf_pkg::DCACHE_DATA_W-1: 0]   w_st1_rs2_data_tmp;
logic [DCACHE_DATA_B_W-1: 0]                w_st1_rs2_byte_en_tmp;

logic [scariv_conf_pkg::STQ_SIZE-1: 0]        w_uc_write_req_valid;


// Instruction Pick up from Dispatch
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

generate for (genvar idx = 0; idx < scariv_conf_pkg::MEM_DISP_SIZE; idx++) begin : in_port_loop
  scariv_pkg::rnid_t                                 w_rs2_rnid;
  scariv_pkg::reg_t                                  w_rs2_type;

  logic                                              w_rs2_phy_hit;
  logic                                              w_rs2_rel_hit;
  scariv_pkg::rel_bus_idx_t                          w_rs2_rel_index;
  logic                                              w_rs2_may_mispred;

  assign w_rs2_rnid = disp_picked_inst[idx].rd_regs[1].rnid;
  assign w_rs2_type = disp_picked_inst[idx].rd_regs[1].typ;

  // Early Wakeup Signal detection
  select_early_wr_bus_oh rs_rel_select_oh (.i_entry_rnid (w_rs2_rnid), .i_entry_type (w_rs2_type), .early_wr_if (early_wr_in_if),
                                           .o_valid   (w_rs2_rel_hit), .o_hit_index (w_rs2_rel_index), .o_may_mispred (w_rs2_may_mispred));
  select_phy_wr_bus #(.BUS_SIZE(scariv_pkg::TGT_BUS_SIZE))
  rs2_phy_select (.i_entry_rnid (w_rs2_rnid), .i_entry_type (w_rs2_type), .phy_wr_if (phy_wr_in_if), .o_valid (w_rs2_phy_hit));

  assign w_stq_entry_in[idx] = assign_stq_disp(disp_picked_inst[idx], w_rs2_rel_hit, w_rs2_rel_index, w_rs2_phy_hit);

end endgenerate // block: in_port_loop


//
// STQ Pointer
//
logic [scariv_conf_pkg::STQ_SIZE-1:0] w_in_ptr_oh;
logic [scariv_conf_pkg::STQ_SIZE-1:0] w_out_ptr_oh;
logic                               w_in_valid;
logic                               w_out_valid;

assign w_in_valid  = (|disp_picked_inst_valid) & !w_flush_valid;
assign w_out_valid = |w_stq_entry_st_finish;

/* verilator lint_off WIDTH */
bit_cnt #(.WIDTH(scariv_conf_pkg::STQ_SIZE)) cnt_disp_valid(.in({{(scariv_conf_pkg::STQ_SIZE-scariv_conf_pkg::MEM_DISP_SIZE){1'b0}}, disp_picked_inst_valid}), .out(w_disp_picked_num));
inoutptr_var_oh #(.SIZE(scariv_conf_pkg::STQ_SIZE)) u_req_ptr(.i_clk (i_clk), .i_reset_n(i_reset_n),
                                                            .i_rollback(1'b0),
                                                            .i_in_valid (w_in_valid ), .i_in_val (w_disp_picked_num[$clog2(scariv_conf_pkg::STQ_SIZE): 0]), .o_in_ptr_oh (w_in_ptr_oh ),
                                                            .i_out_valid(w_out_valid), .i_out_val(w_entry_finish_cnt), .o_out_ptr_oh(w_out_ptr_oh));

generate for (genvar s_idx = 0; s_idx < scariv_conf_pkg::MEM_DISP_SIZE; s_idx++) begin : disp_idx_loop
  assign w_pipe_sel_idx_oh[s_idx] = 1 << (s_idx % scariv_conf_pkg::LSU_INST_NUM);
end
endgenerate

stqsize_t w_out_ptr_idx;
bit_encoder #(.WIDTH(scariv_conf_pkg::STQ_SIZE)) u_uc_encoder_ptr (.i_in(w_out_ptr_oh), .o_out(w_out_ptr_idx));

// logic [scariv_conf_pkg::STQ_SIZE-1: 0]                   w_stq_snoop_valid;
// logic [scariv_conf_pkg::DCACHE_DATA_W-1: 0]              w_stq_snoop_data[scariv_conf_pkg::STQ_SIZE];
// logic [scariv_lsu_pkg::DCACHE_DATA_B_W-1: 0]             w_stq_snoop_be  [scariv_conf_pkg::STQ_SIZE];
//
// logic [scariv_conf_pkg::STQ_SIZE-1: 0]                   w_stq_snoop_resp_s0_valid;
// logic [scariv_conf_pkg::DCACHE_DATA_W-1: 0]              w_stq_snoop_resp_s0_data;
// logic [scariv_lsu_pkg::DCACHE_DATA_B_W-1: 0]             w_stq_snoop_resp_s0_be;

// assign w_stq_snoop_resp_s0_valid = |w_stq_snoop_valid;
// bit_or #(.WIDTH(scariv_conf_pkg::DCACHE_DATA_W),  .WORDS(scariv_conf_pkg::STQ_SIZE)) u_snoop_data_or (.i_data(w_stq_snoop_data), .o_selected(w_stq_snoop_resp_s0_data));
// bit_or #(.WIDTH(scariv_lsu_pkg::DCACHE_DATA_B_W), .WORDS(scariv_conf_pkg::STQ_SIZE)) u_snoop_be_or   (.i_data(w_stq_snoop_be),   .o_selected(w_stq_snoop_resp_s0_be));
//
always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    stq_snoop_if.resp_s1_valid <= 1'b0;
  end else begin
    stq_snoop_if.resp_s1_valid <= stq_snoop_if.req_s0_valid;
    stq_snoop_if.resp_s1_data  <= 'h0;
    stq_snoop_if.resp_s1_be    <= 'h0;
  end
end

generate for (genvar s_idx = 0; s_idx < scariv_conf_pkg::STQ_SIZE; s_idx++) begin : stq_loop
  /* verilator lint_off SELRANGE */
  localparam rs2_regrd_port_idx = scariv_conf_pkg::STQ_REGRD_PORT_NUM == 1 ? 'h0 : s_idx;

  logic [scariv_conf_pkg::MEM_DISP_SIZE-1: 0]  w_input_valid;
  stq_entry_t          w_load_stq_entry;
  scariv_pkg::grp_id_t w_disp_grp_id;
  logic [scariv_conf_pkg::LSU_INST_NUM-1: 0] w_disp_pipe_sel_oh;
  scariv_pkg::grp_id_t w_stbuf_accept_array;

  // stq_snoop_if stq_entry_snoop_if();

  for (genvar i_idx = 0; i_idx < scariv_conf_pkg::MEM_DISP_SIZE; i_idx++) begin : in_loop
    logic [scariv_conf_pkg::STQ_SIZE-1: 0]  w_entry_ptr_oh;
    bit_rotate_left #(.WIDTH(scariv_conf_pkg::STQ_SIZE), .VAL(i_idx)) target_bit_rotate (.i_in(w_in_ptr_oh), .o_out(w_entry_ptr_oh));
    assign w_input_valid[i_idx] = disp_picked_inst_valid[i_idx] & !w_flush_valid & (w_entry_ptr_oh[s_idx]);
  end

  bit_oh_or #(.T(stq_entry_t), .WORDS(scariv_conf_pkg::MEM_DISP_SIZE)) bit_oh_entry  (.i_oh(w_input_valid), .i_data(w_stq_entry_in),   .o_selected(w_load_stq_entry));
  bit_oh_or #(.T(logic[scariv_conf_pkg::DISP_SIZE-1:0]),     .WORDS(scariv_conf_pkg::MEM_DISP_SIZE)) bit_oh_grp_id   (.i_oh(w_input_valid), .i_data(disp_picked_grp_id), .o_selected(w_disp_grp_id));
  bit_oh_or #(.T(logic[scariv_conf_pkg::LSU_INST_NUM-1: 0]), .WORDS(scariv_conf_pkg::MEM_DISP_SIZE)) bit_oh_pipe_sel (.i_oh(w_input_valid), .i_data(w_pipe_sel_idx_oh), .o_selected(w_disp_pipe_sel_oh));

  // Selection of EX2 Update signal
  stq_ex1_update_t w_ex1_q_updates;
  logic        w_ex1_q_valid;
  stq_ex1_upd_select u_stq_ex1_upd_select (.stq_upd_if(stq_upd_if), .i_cmt_id(w_stq_entries[s_idx].inst.cmt_id), .i_grp_id(w_stq_entries[s_idx].inst.grp_id),
                                           .o_ex1_q_valid(w_ex1_q_valid), .o_ex1_q_updates(w_ex1_q_updates));

  stq_ex2_update_t w_ex2_q_updates;
  logic        w_ex2_q_valid;
  stq_ex2_upd_select u_stq_ex2_upd_select (.stq_upd_if(stq_upd_if), .i_cmt_id(w_stq_entries[s_idx].inst.cmt_id), .i_grp_id(w_stq_entries[s_idx].inst.grp_id),
                                           .o_ex2_q_valid(w_ex2_q_valid), .o_ex2_q_updates(w_ex2_q_updates));

  scariv_stq_entry
    #(.entry_index (s_idx))
  u_entry
    (
     .i_clk     (i_clk    ),
     .i_reset_n (i_reset_n),

     .rob_info_if (rob_info_if),

     .i_disp_load       (|w_input_valid    ),
     .i_disp_cmt_id     (disp.payload.cmt_id),
     .i_disp_grp_id     (w_disp_grp_id     ),
     .i_disp_stq_entry  (w_load_stq_entry  ),
     .i_disp_pipe_sel_oh(w_disp_pipe_sel_oh),

     .early_wr_in_if (early_wr_in_if),
     .phy_wr_in_if   (phy_wr_in_if  ),

     .i_ex1_q_valid  (|w_ex1_q_valid),
     .i_ex1_q_updates(w_ex1_q_updates),

     .i_ex2_q_valid  (|w_ex2_q_valid),
     .i_ex2_q_updates(w_ex2_q_updates),

     .i_rs2_rel_read_accepted (w_rs2_rel_read_valids_oh[rs2_regrd_port_idx][s_idx]),
     .i_rs2_rel_data          (w_ex1_rs2_rel_data          [rs2_regrd_port_idx]),
     .i_rs2_rel_mispredicted  (w_ex1_rs2_rel_mispredicted  [rs2_regrd_port_idx]),

     .i_rs2_phy_read_accepted (w_rs2_phy_read_valids_oh[rs2_regrd_port_idx][s_idx]),
     .i_rs2_phy_data          (w_ex1_rs2_phy_data          [rs2_regrd_port_idx]),

     .o_entry    (w_stq_entries   [s_idx]),

     .i_missu_is_empty(i_missu_is_empty),

     .commit_if (commit_if),
     .br_upd_if (br_upd_if),

     .o_stbuf_req_valid (w_stbuf_req_valid[s_idx]),
     .i_stbuf_accept    (|w_stbuf_accept_array & (st_buffer_if.resp != scariv_lsu_pkg::ST_BUF_FULL)),

     .o_uc_write_req_valid (w_uc_write_req_valid[s_idx]),
     .i_uc_write_accept    (uc_write_if.ready),

     // Snoop Interface
     // .stq_snoop_if (stq_entry_snoop_if),

     .i_st_buffer_empty (st_buffer_if.is_empty),

     .i_stq_outptr_valid    (w_out_ptr_oh[s_idx]),
     .o_stq_entry_st_finish (w_stq_entry_st_finish[s_idx])
     );

  assign w_stq_valid[s_idx] = w_stq_entries[s_idx].is_valid;

  // If rs2 operand is already ready, store data is fetch directly
  for (genvar r_idx = 0; r_idx < scariv_conf_pkg::STQ_REGRD_PORT_NUM; r_idx++) begin : stq_regread_loop
    assign w_rs2_rel_read_valids[r_idx][s_idx] = (rs2_regrd_port_idx == r_idx) &
                                                 w_stq_entries[s_idx].is_valid &
                                                 !w_stq_entries[s_idx].dead &
                                                 !w_stq_entries[s_idx].is_rs2_get & !w_stq_entries[s_idx].rs2_rel_read_accepted &
                                                 w_stq_entries[s_idx].inst.rd_reg.valid &
                                                 w_stq_entries[s_idx].inst.rd_reg.predict_ready[0];

    assign w_rs2_phy_read_valids[r_idx][s_idx] = (rs2_regrd_port_idx == r_idx) &
                                                 w_stq_entries[s_idx].is_valid &
                                                 !w_stq_entries[s_idx].dead &
                                                 !w_stq_entries[s_idx].is_rs2_get & !w_stq_entries[s_idx].rs2_phy_read_accepted &
                                                 w_stq_entries[s_idx].inst.rd_reg.valid &
                                                 w_stq_entries[s_idx].inst.rd_reg.ready;
  end

  assign w_stq_rs2_get[s_idx] = w_stq_entries[s_idx].is_valid &
                                (w_stq_entries[s_idx].is_rs2_get | w_stq_entries[s_idx].dead);

  for (genvar d_idx = 0; d_idx < scariv_conf_pkg::DISP_SIZE; d_idx++) begin : stbuf_acc_loop
    assign w_stbuf_accept_array[d_idx] = w_stbuf_req_accepted[d_idx][s_idx];
  end

  // -----------------
  // Forwarding check
  // -----------------
  if (scariv_conf_pkg::DETAIL_STLD_FWD) begin : detail_stld_fwd
    for (genvar p_idx = 0; p_idx < scariv_conf_pkg::LSU_INST_NUM; p_idx++) begin : fwd_loop
      logic  w_entry_older_than_fwd;
      logic  w_same_addr_region;
      logic  w_same_dw;
      logic [ 7: 0] w_entry_dw;
      assign w_entry_dw = gen_dw(w_stq_entries[s_idx].size, w_stq_entries[s_idx].addr[2:0]);
      assign w_same_dw = is_dw_included(w_stq_entries[s_idx].size, w_stq_entries[s_idx].addr[2:0],
                                        ex2_fwd_check_if[p_idx].paddr_dw);
      assign w_same_addr_region = w_stq_entries   [s_idx].addr [riscv_pkg::PADDR_W-1:$clog2(scariv_pkg::ALEN_W/8)] ==
                                  ex2_fwd_check_if[p_idx].paddr[riscv_pkg::PADDR_W-1:$clog2(scariv_pkg::ALEN_W/8)];

      assign w_ex2_fwd_valid[p_idx][s_idx] = w_stq_entries[s_idx].is_valid &
                                             !w_stq_entries[s_idx].dead &
                                             (w_entry_older_than_fwd | w_stq_entries[s_idx].is_committed) &
                                             w_stq_entries[s_idx].paddr_valid & w_stq_entries[s_idx].is_rs2_get &
                                             w_same_addr_region &
                                             |(w_entry_dw & ex2_fwd_check_if[p_idx].paddr_dw);
      assign w_ex2_fwd_dw[p_idx][s_idx] = w_entry_dw & ex2_fwd_check_if[p_idx].paddr_dw;

      assign w_entry_older_than_fwd = scariv_pkg::id0_is_older_than_id1 (w_stq_entries[s_idx].inst.cmt_id,
                                                                         w_stq_entries[s_idx].inst.grp_id,
                                                                         ex2_fwd_check_if[p_idx].cmt_id,
                                                                         ex2_fwd_check_if[p_idx].grp_id);
    end // block: fwd_loop
  end else begin : coarse_stld_fwd // block: detail_stld_fwd
    for (genvar p_idx = 0; p_idx < scariv_conf_pkg::LSU_INST_NUM; p_idx++) begin : fwd_loop
      logic  w_entry_older_than_fwd;
      logic  w_same_addr_region;
      logic  w_is_strb_hit;
      assign w_same_addr_region = w_stq_entries   [s_idx].addr [riscv_pkg::PADDR_W-1:$clog2(scariv_pkg::ALEN_W/8)] ==
                                  ex2_fwd_check_if[p_idx].paddr[riscv_pkg::PADDR_W-1:$clog2(scariv_pkg::ALEN_W/8)];

      assign w_entry_older_than_fwd = scariv_pkg::id0_is_older_than_id1 (w_stq_entries[s_idx].inst.cmt_id,
                                                                         w_stq_entries[s_idx].inst.grp_id,
                                                                         ex2_fwd_check_if[p_idx].cmt_id,
                                                                         ex2_fwd_check_if[p_idx].grp_id);
      assign w_is_strb_hit = is_strb_hit(w_stq_entries[s_idx].size, w_stq_entries[s_idx].addr[2:0],
                                         ex2_fwd_check_if[p_idx].paddr_dw);
      assign w_ex2_fwd_valid[p_idx][s_idx] = w_stq_entries[s_idx].is_valid &
                                             !w_stq_entries[s_idx].dead &
                                             (w_entry_older_than_fwd | w_stq_entries[s_idx].is_committed) &
                                             w_stq_entries[s_idx].paddr_valid & w_stq_entries[s_idx].is_rs2_get &
                                             w_same_addr_region & w_is_strb_hit;
    end // block: fwd_loop
  end // block: coarse_stld_fwd

  // RMW Order Hazard Check
  for (genvar p_idx = 0; p_idx < scariv_conf_pkg::LSU_INST_NUM; p_idx++) begin : rmw_order_haz_loop
  logic pipe_is_younger_than_rmw;

    assign pipe_is_younger_than_rmw = scariv_pkg::id0_is_older_than_id1 (w_stq_entries[s_idx].inst.cmt_id,
                                                                         w_stq_entries[s_idx].inst.grp_id,
                                                                         rmw_order_check_if[p_idx].ex2_cmt_id,
                                                                         rmw_order_check_if[p_idx].ex2_grp_id);
    assign w_ex2_rmw_order_haz_valid[p_idx][s_idx] = w_stq_entries[s_idx].is_valid &
                                                     w_stq_entries[s_idx].inst.is_rmw &
                                                     rmw_order_check_if[p_idx].ex2_valid &
                                                     (pipe_is_younger_than_rmw | w_stq_entries[s_idx].is_committed);
  end // block: rmw_order_haz_loop

  // STQ Hazard Check
  for (genvar p_idx = 0; p_idx < scariv_conf_pkg::LSU_INST_NUM; p_idx++) begin : stq_nonfwd_haz_loop
    logic pipe_is_younger_than_stq;
    logic w_same_addr_region;

    assign pipe_is_younger_than_stq = scariv_pkg::id0_is_older_than_id1 (w_stq_entries[s_idx].inst.cmt_id,
                                                                       w_stq_entries[s_idx].inst.grp_id,
                                                                       stq_haz_check_if[p_idx].ex2_cmt_id,
                                                                       stq_haz_check_if[p_idx].ex2_grp_id);
    assign w_same_addr_region = w_stq_entries   [s_idx].addr     [riscv_pkg::PADDR_W-1:$clog2(scariv_pkg::ALEN_W/8)] ==
                                stq_haz_check_if[p_idx].ex2_paddr[riscv_pkg::PADDR_W-1:$clog2(scariv_pkg::ALEN_W/8)];

    assign w_ex2_stq_haz_valid[p_idx][s_idx] = w_stq_entries[s_idx].is_valid &
                                               !w_stq_entries[s_idx].dead &
                                               w_stq_entries[s_idx].paddr_valid &
                                               !w_stq_entries[s_idx].is_rs2_get &
                                               stq_haz_check_if[p_idx].ex2_valid &
                                               w_same_addr_region &
                                               pipe_is_younger_than_stq;
  end // block: rmw_order_haz_loop

  assign w_stq_rmw_existed[s_idx] = w_stq_entries[s_idx].is_valid & w_stq_entries[s_idx].inst.is_rmw;
end endgenerate

// -------------------------
// STQ rs2 data management
// -------------------------
generate if (scariv_conf_pkg::DETAIL_STLD_FWD) begin : detail_rs2_cam

  for (genvar s_idx = 0; s_idx < scariv_conf_pkg::STQ_SIZE; s_idx++) begin: rs2_loop

    localparam rs2_regrd_port_idx = scariv_conf_pkg::STQ_REGRD_PORT_NUM == 1 ? 'h0 : s_idx[$clog2(scariv_conf_pkg::STQ_REGRD_PORT_NUM)-1: 0];

    scariv_pkg::alen_t w_rs2_data_next;
    always_ff @ (posedge i_clk) begin
      r_rs2_data_array[s_idx] <= w_rs2_data_next;
    end

    always_comb begin
      w_rs2_data_next = r_rs2_data_array[s_idx];

      if (w_stq_entries[s_idx].inst.rd_reg.predict_ready[1] &
          w_rs2_rel_read_valids_oh[rs2_regrd_port_idx][s_idx] &
          ~w_ex1_rs2_rel_mispredicted  [rs2_regrd_port_idx]) begin
        w_rs2_data_next = w_ex1_rs2_rel_data[rs2_regrd_port_idx];
      end

      if (w_stq_entries[s_idx].rs2_phy_read_accepted) begin
        w_rs2_data_next = w_ex1_rs2_phy_data[rs2_regrd_port_idx];
      end
    end // always_comb
  end // block: rs2_loop

end else begin : coarse_rs2_ram // block: detail_rs2_cam

  logic[scariv_conf_pkg::STQ_REGRD_PORT_NUM*2-1: 0] w_wr_valid  ;
  stqsize_t          w_wr_addr   [scariv_conf_pkg::STQ_REGRD_PORT_NUM*2];
  scariv_pkg::alen_t w_wr_data   [scariv_conf_pkg::STQ_REGRD_PORT_NUM*2];

  stqsize_t          w_rd_addr   [scariv_conf_pkg::LSU_INST_NUM + 2];
  scariv_pkg::alen_t w_rd_data   [scariv_conf_pkg::LSU_INST_NUM + 2];

  for (genvar r_idx = 0; r_idx < scariv_conf_pkg::STQ_REGRD_PORT_NUM; r_idx++) begin : stq_regwrite_loop
    assign w_wr_valid[r_idx*2+0] = w_ex1_rs2_rel_data_valid[r_idx] & ~w_ex1_rs2_rel_mispredicted[r_idx];
    assign w_wr_addr [r_idx*2+0] = w_ex1_rs2_rel_stq_ptr   [r_idx];
    assign w_wr_data [r_idx*2+0] = w_ex1_rs2_rel_data      [r_idx];
    assign w_wr_valid[r_idx*2+1] = w_ex1_rs2_phy_data_valid[r_idx];
    assign w_wr_addr [r_idx*2+1] = w_ex1_rs2_phy_stq_ptr   [r_idx];
    assign w_wr_data [r_idx*2+1] = w_ex1_rs2_phy_data      [r_idx];
  end

  for (genvar r_idx = 0; r_idx < scariv_conf_pkg::LSU_INST_NUM; r_idx++) begin : stq_regrd_fwd_loop
    assign w_rd_addr         [r_idx] = w_ex2_fwd_valid_ptr[r_idx];
    assign w_ex2_stq_fwd_rs2_data[r_idx] = w_rd_data[r_idx];
  end
  for (genvar r_idx = 0; r_idx < ST_BUF_MERGE_ENTRY_SIZE; r_idx++) begin : stq_regrd_stbuffer_loop
    assign w_rd_addr           [scariv_conf_pkg::LSU_INST_NUM + r_idx] = w_stbuf_rs2_out_ptr[r_idx];
    assign w_stq_stbuf_rs2_data[r_idx]                                 = w_rd_data[scariv_conf_pkg::LSU_INST_NUM + r_idx];
  end

  distributed_mp_ram
    #(
      .WR_PORTS (scariv_conf_pkg::STQ_REGRD_PORT_NUM * 2),  // Release Path / PhyWrite Path
      .RD_PORTS (scariv_conf_pkg::LSU_INST_NUM + 2),  // Forwarding + STQ->STBuffer
      .WIDTH    ($bits(scariv_pkg::alen_t)),
      .WORDS    (scariv_conf_pkg::STQ_SIZE)
      )
  u_rs2_dataram
    (
     .i_clk     (i_clk    ),
     .i_reset_n (i_reset_n),

     .i_wr      (w_wr_valid ),
     .i_wr_addr (w_wr_addr  ),
     .i_wr_data (w_wr_data  ),

     .i_rd_addr (w_rd_addr ),
     .o_rd_data (w_rd_data )
     );
end endgenerate // block: coarse_rs2_ram


// ST data read selection
generate for (genvar r_idx = 0; r_idx < scariv_conf_pkg::STQ_REGRD_PORT_NUM; r_idx++) begin : stq_regread_loop
  stq_entry_t w_phy_req_entry;
  bit_extract_lsb_ptr_oh #(.WIDTH(scariv_conf_pkg::STQ_SIZE))     u_bit_rs2_phy_req_sel (.in(w_rs2_phy_read_valids[r_idx]), .i_ptr_oh(w_out_ptr_oh), .out(w_rs2_phy_read_valids_oh[r_idx]));
  bit_oh_or #(.T(stq_entry_t), .WORDS(scariv_conf_pkg::STQ_SIZE)) u_select_rs2_phy_req_entry  (.i_oh(w_rs2_phy_read_valids_oh[r_idx]), .i_data(w_stq_entries), .o_selected(w_phy_req_entry));

  stq_entry_t w_rel_req_entry;
  bit_extract_lsb_ptr_oh #(.WIDTH(scariv_conf_pkg::STQ_SIZE))     u_bit_rs2_rel_req_sel (.in(w_rs2_rel_read_valids[r_idx]), .i_ptr_oh(w_out_ptr_oh), .out(w_rs2_rel_read_valids_oh[r_idx]));
  bit_oh_or #(.T(stq_entry_t), .WORDS(scariv_conf_pkg::STQ_SIZE)) u_select_rs2_rel_req_entry  (.i_oh(w_rs2_rel_read_valids_oh[r_idx]), .i_data(w_stq_entries), .o_selected(w_rel_req_entry));

  // instance
  scariv_stq_rs2_rel_pipe
  u_rs2_rel_pipe
    (
     .i_clk     (i_clk    ),
     .i_reset_n (i_reset_n),

     .i_ex0_rel_valid    (|w_rs2_rel_read_valids[r_idx]           ),
     .i_ex0_rel_idx      (w_rel_req_entry.inst.rd_reg.early_index ),
     .i_ex0_rnid         (w_rel_req_entry.inst.rd_reg.rnid        ),
     .i_ex0_type         (w_rel_req_entry.inst.rd_reg.typ         ),
     .o_ex1_rel_valid    (w_ex1_rs2_rel_data_valid  [r_idx]),
     .o_ex1_rel_data     (w_ex1_rs2_rel_data        [r_idx]),
     .o_ex1_mispredicted (w_ex1_rs2_rel_mispredicted[r_idx]),

     .i_ex0_stq_valid    (w_rs2_rel_read_valids_oh  [r_idx]),
     .o_ex1_stq_ptr      (w_ex1_rs2_rel_stq_ptr     [r_idx]),

     .mispred_in_if (mispred_in_if),
     .phy_wr_in_if  (phy_wr_in_if )
     );

  scariv_stq_rs2_phy_pipe
  u_rs2_phy_pipe
    (
     .i_clk     (i_clk    ),
     .i_reset_n (i_reset_n),

     .i_ex0_phy_rd_valid (|w_rs2_phy_read_valids[r_idx]    ),
     .i_ex0_phy_rnid     (w_phy_req_entry.inst.rd_reg.rnid ),
     .i_ex0_phy_type     (w_phy_req_entry.inst.rd_reg.typ  ),

     .o_ex1_phy_valid    (w_ex1_rs2_phy_data_valid[r_idx]),
     .o_ex1_phy_data     (w_ex1_rs2_phy_data      [r_idx]),

     .i_ex0_stq_valid   (w_rs2_phy_read_valids_oh [r_idx]),
     .o_ex1_stq_ptr     (w_ex1_rs2_phy_stq_ptr    [r_idx]),

     .int_rs2_regread (int_rs2_regread[r_idx]),
     .fp_rs2_regread  (fp_rs2_regread [r_idx])
     );

end endgenerate


// RMW Order Hazard Check Logci
generate for (genvar p_idx = 0; p_idx < scariv_conf_pkg::LSU_INST_NUM; p_idx++) begin : rmw_haz_resp_loop
  assign rmw_order_check_if[p_idx].ex2_stq_haz_vld = |w_ex2_rmw_order_haz_valid[p_idx];
end
endgenerate

// STQ Hazard Check Logcic
generate for (genvar p_idx = 0; p_idx < scariv_conf_pkg::LSU_INST_NUM; p_idx++) begin : stq_nonfwd_haz_resp_loop
  assign stq_haz_check_if[p_idx].ex2_haz_valid = |w_ex2_stq_haz_valid[p_idx];
  assign stq_haz_check_if[p_idx].ex2_haz_index =  w_ex2_stq_haz_valid[p_idx];
end
endgenerate


// =========================
// STQ Forwarding Logic
// =========================
generate if (scariv_conf_pkg::DETAIL_STLD_FWD) begin : detail_stld_fwd

  scariv_pkg::alen_t w_aligned_rs2_data_array[scariv_conf_pkg::STQ_SIZE];
  for (genvar s_idx = 0; s_idx < scariv_conf_pkg::STQ_SIZE; s_idx++) begin : stq_rs2_loop
    if (scariv_pkg::ALEN_W == 64) begin
      assign w_aligned_rs2_data_array[s_idx] = scariv_lsu_pkg::align_8byte(r_rs2_data_array[s_idx], w_stq_entries[s_idx].addr[$clog2(scariv_pkg::ALEN_W/8)-1:0]);
    end else begin
      assign w_aligned_rs2_data_array[s_idx] = scariv_lsu_pkg::align_4byte(r_rs2_data_array[s_idx], w_stq_entries[s_idx].addr[$clog2(scariv_pkg::ALEN_W/8)-1:0]);
    end
  end

  for (genvar p_idx = 0; p_idx < scariv_conf_pkg::LSU_INST_NUM; p_idx++) begin : fwd_loop
    for (genvar b_idx = 0; b_idx < scariv_pkg::ALEN_W/8; b_idx++) begin : byte_loop
      scariv_pkg::alen_t                     w_stq_fwd_rs2_data;
      logic [ 7: 0]                          w_ex2_fwd_dw_selected;
      logic [scariv_conf_pkg::STQ_SIZE-1: 0] w_ex2_fwd_valid_oh;
      logic [scariv_conf_pkg::STQ_SIZE-1: 0] w_ex2_fwd_strb_valid;
      for (genvar s_idx = 0; s_idx < scariv_conf_pkg::STQ_SIZE; s_idx++) begin : stq_loop
        assign w_ex2_fwd_strb_valid[s_idx] = w_ex2_fwd_dw[p_idx][s_idx][b_idx] & w_ex2_fwd_valid[p_idx][s_idx];
      end
      bit_extract_msb_ptr_oh #(.WIDTH(scariv_conf_pkg::STQ_SIZE)) u_bit_req_sel (.in(w_ex2_fwd_strb_valid), .i_ptr_oh(w_out_ptr_oh), .out(w_ex2_fwd_valid_oh));
      bit_oh_or #(.T(scariv_pkg::alen_t), .WORDS(scariv_conf_pkg::STQ_SIZE)) select_fwd_entry  (.i_oh(w_ex2_fwd_valid_oh), .i_data(w_aligned_rs2_data_array), .o_selected(w_stq_fwd_rs2_data));

      assign ex2_fwd_check_if[p_idx].fwd_dw  [b_idx]        = |w_ex2_fwd_strb_valid;
      assign ex2_fwd_check_if[p_idx].fwd_data[b_idx*8 +: 8] =  w_stq_fwd_rs2_data[b_idx*8+:8];
    end // block: byte_loop

    assign ex2_fwd_check_if[p_idx].fwd_valid      = |w_ex2_fwd_valid[p_idx];

    assign ex2_fwd_check_if[p_idx].fwd_miss_valid = 1'b0;  // Forward Miss is not happen in DETALED_FWD mode.

  end // block: fwd_loop

end else begin : coarse_stld_fwd // block: detail_stld_fwd

  for (genvar p_idx = 0; p_idx < scariv_conf_pkg::LSU_INST_NUM; p_idx++) begin : fwd_loop
    logic [scariv_conf_pkg::STQ_SIZE-1: 0] w_ex2_fwd_valid_oh;
    scariv_pkg::alen_t                     w_stq_fwd_rs2_data;

    bit_extract_msb_ptr_oh #(.WIDTH(scariv_conf_pkg::STQ_SIZE)) u_bit_req_sel (.in(w_ex2_fwd_valid[p_idx]), .i_ptr_oh(w_out_ptr_oh), .out(w_ex2_fwd_valid_oh));
    bit_encoder #(.WIDTH(scariv_conf_pkg::STQ_SIZE)) u_encoder_ptr (.i_in(w_ex2_fwd_valid_oh), .o_out(w_ex2_fwd_valid_ptr[p_idx]));
    if (scariv_pkg::ALEN_W == 64) begin
      assign w_stq_fwd_rs2_data = scariv_lsu_pkg::align_8byte(w_ex2_stq_fwd_rs2_data[p_idx], w_stq_entries[w_ex2_fwd_valid_ptr[p_idx]].addr[$clog2(scariv_pkg::ALEN_W/8)-1:0]);
    end else begin
      assign w_stq_fwd_rs2_data = scariv_lsu_pkg::align_4byte(w_ex2_stq_fwd_rs2_data[p_idx], w_stq_entries[w_ex2_fwd_valid_ptr[p_idx]].addr[$clog2(scariv_pkg::ALEN_W/8)-1:0]);
    end
    assign ex2_fwd_check_if[p_idx].fwd_dw    = {8{|w_ex2_fwd_valid[p_idx]}} & gen_dw(w_stq_entries[w_ex2_fwd_valid_ptr[p_idx]].size, w_stq_entries[w_ex2_fwd_valid_ptr[p_idx]].addr[2:0]);
    assign ex2_fwd_check_if[p_idx].fwd_data  =  w_stq_fwd_rs2_data;
    assign ex2_fwd_check_if[p_idx].fwd_valid = |w_ex2_fwd_valid[p_idx];

    assign ex2_fwd_check_if[p_idx].fwd_miss_valid     = ((w_ex2_fwd_valid[p_idx] & (w_ex2_fwd_valid[p_idx] - 1)) != 'h0) &
                                                        !is_dw_included(w_stq_entries[w_ex2_fwd_valid_ptr[p_idx]].size,
                                                                        w_stq_entries[w_ex2_fwd_valid_ptr[p_idx]].addr[2:0],
                                                                        ex2_fwd_check_if[p_idx].paddr_dw);
    assign ex2_fwd_check_if[p_idx].fwd_miss_haz_index = w_ex2_fwd_valid_ptr[p_idx];
  end // block: fwd_loop
end endgenerate

// =========================
// STQ Hazard Resolve Logic
// =========================
always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    o_stq_rs2_resolve <= 'h0;
  end else begin
    o_stq_rs2_resolve.index <= w_stq_rs2_get | ~w_stq_valid;  // RS2 get or STQ entry is finished => resolve
  end
end

// ==============================
// After commit, store operation
// ==============================
assign w_stq_cmt_head_entry = w_stq_entries[w_out_ptr_idx];

/* verilator lint_off UNOPTFLAT */
scariv_pkg::grp_id_t w_sq_commit_ready_issue;
scariv_pkg::grp_id_t w_sq_is_rmw;

logic [scariv_lsu_pkg::ST_BUF_WIDTH/8-1:0] w_st_buffer_strb[ST_BUF_MERGE_ENTRY_SIZE];
logic [scariv_lsu_pkg::ST_BUF_WIDTH-1:0]   w_st_buffer_data[ST_BUF_MERGE_ENTRY_SIZE];

generate for (genvar d_idx = 0; d_idx < ST_BUF_MERGE_ENTRY_SIZE; d_idx++) begin : stbuf_loop
  logic [scariv_conf_pkg::STQ_SIZE-1: 0] w_shifted_out_ptr_oh;
  logic                                w_sq_commit_valid;
  bit_rotate_left #(.WIDTH(scariv_conf_pkg::STQ_SIZE), .VAL(d_idx)) u_ptr_rotate(.i_in(w_out_ptr_oh), .o_out(w_shifted_out_ptr_oh));
  assign w_sq_commit_valid = |(w_stbuf_req_valid & w_shifted_out_ptr_oh);
  assign w_sq_is_rmw[d_idx]= |(w_stq_rmw_existed & w_shifted_out_ptr_oh);

  if (d_idx == 0) begin
    assign w_sq_commit_ready_issue[d_idx] = w_sq_commit_valid;
  end else begin

    assign w_sq_commit_ready_issue[d_idx] = w_sq_commit_valid &
                                            w_sq_commit_ready_issue[d_idx-1] & ~w_sq_is_rmw[d_idx-1] &
                                            (w_stq_cmt_head_entry.addr[riscv_pkg::PADDR_W-1:$clog2(scariv_lsu_pkg::ST_BUF_WIDTH/8)] ==
                                             w_stq_cmt_entry.addr     [riscv_pkg::PADDR_W-1:$clog2(scariv_lsu_pkg::ST_BUF_WIDTH/8)]);
  end // else: !if(d_idx == 0)

  bit_encoder #(.WIDTH(scariv_conf_pkg::STQ_SIZE)) u_encoder_ptr (.i_in(w_shifted_out_ptr_oh), .o_out(w_stbuf_rs2_out_ptr[d_idx]));
  stq_entry_t w_stq_cmt_entry;
  assign w_stq_cmt_entry = w_stq_entries[w_stbuf_rs2_out_ptr[d_idx]];

  logic [scariv_lsu_pkg::ST_BUF_WIDTH / 8-1:0] w_strb_origin;
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
    w_st_buffer_strb[d_idx] = w_strb_origin << w_stq_cmt_entry.addr[$clog2(scariv_lsu_pkg::ST_BUF_WIDTH/8)-1: 0];
    if (scariv_conf_pkg::DETAIL_STLD_FWD) begin
      w_st_buffer_data[d_idx] = r_rs2_data_array[w_stbuf_rs2_out_ptr[d_idx]] << {w_stq_cmt_entry.addr[$clog2(scariv_lsu_pkg::ST_BUF_WIDTH/8)-1: 0], 3'b000};
    end else begin
      w_st_buffer_data[d_idx] = w_stq_stbuf_rs2_data[d_idx] << {w_stq_cmt_entry.addr[$clog2(scariv_lsu_pkg::ST_BUF_WIDTH/8)-1: 0], 3'b000};
    end
  end

  assign w_stbuf_req_accepted[d_idx] = w_shifted_out_ptr_oh & {scariv_conf_pkg::STQ_SIZE{w_stbuf_accepted_disp[d_idx]}};

end // block: stbuf_loop
endgenerate

// ready to store_buffer
// 0010111 --> inv -> 1101000 --> lower lsb --> 1111000 --> inv --> 0000111
scariv_pkg::grp_id_t w_sq_stb_ready_inv;
bit_tree_lsb #(.WIDTH(ST_BUF_MERGE_ENTRY_SIZE)) select_stb_bit (.in(~w_sq_commit_ready_issue), .out(w_sq_stb_ready_inv));
assign w_stbuf_accepted_disp = ~w_sq_stb_ready_inv;

// Make Store Buffer Request
assign st_buffer_if.valid = |w_stbuf_accepted_disp;
assign st_buffer_if.paddr = w_stq_cmt_head_entry.addr;

generate for(genvar b_idx = 0; b_idx < scariv_lsu_pkg::ST_BUF_WIDTH/8; b_idx++) begin : loop_st_buf_strb
  scariv_pkg::grp_id_t w_strb_array;
  for (genvar d_idx = 0; d_idx < ST_BUF_MERGE_ENTRY_SIZE; d_idx++) begin : stb_disp_loop
    assign w_strb_array[d_idx] = w_st_buffer_strb[d_idx][b_idx] & w_stbuf_accepted_disp[d_idx];
  end
  assign st_buffer_if.strb[b_idx] = |w_strb_array;

  scariv_pkg::grp_id_t w_strb_array_msb;
  bit_extract_msb #(.WIDTH(ST_BUF_MERGE_ENTRY_SIZE)) extract_msb_strb (.in(w_strb_array), .out(w_strb_array_msb));

  /* verilator lint_off UNOPTFLAT */
  logic [7: 0] w_data_byte_array[ST_BUF_MERGE_ENTRY_SIZE+1];
  assign w_data_byte_array[0] = w_st_buffer_data[0][b_idx*8 +: 8];
  for (genvar d2_idx = 0; d2_idx < ST_BUF_MERGE_ENTRY_SIZE; d2_idx++) begin : st_buf_disp_loop
    assign w_data_byte_array[d2_idx+1] = w_strb_array_msb[d2_idx] ? w_st_buffer_data[d2_idx][b_idx*8 +: 8] : w_data_byte_array[d2_idx];
  end
  assign st_buffer_if.data[b_idx*8 +: 8] = w_data_byte_array[ST_BUF_MERGE_ENTRY_SIZE];
end endgenerate // block: loop_st_buf_strb

assign st_buffer_if.is_rmw = w_stq_cmt_head_entry.inst.is_rmw;
assign st_buffer_if.rmwop  = w_stq_cmt_head_entry.rmwop;
assign st_buffer_if.size   = w_stq_cmt_head_entry.size;
`ifdef SIMULATION
assign st_buffer_if.cmt_id = w_stq_cmt_head_entry.inst.cmt_id;
assign st_buffer_if.grp_id = w_stq_cmt_head_entry.inst.grp_id;
`endif //SIMULATION

// ---------------------------------
// After Commit, UC-Write Operation
// ---------------------------------
stq_entry_t w_uc_write_entry_sel;
assign w_uc_write_entry_sel = w_stq_entries[w_out_ptr_idx];

always_comb begin
  uc_write_if.valid = |w_uc_write_req_valid;
  uc_write_if.paddr = w_uc_write_entry_sel.addr;
  uc_write_if.data  = w_stq_stbuf_rs2_data[0];
  uc_write_if.size  = w_uc_write_entry_sel.size;
end

function automatic stq_entry_t assign_stq_disp (scariv_pkg::disp_t in,
                                                logic rs2_rel_hit, scariv_pkg::rel_bus_idx_t rs2_rel_index,
                                                logic rs2_phy_hit);
  stq_entry_t ret;

  ret = 'h0;

  ret.is_valid  = 1'b1;

  ret.inst.is_rmw = in.subcat == decoder_inst_cat_pkg::INST_SUBCAT_RMW;

  ret.inst.rd_reg.valid         = in.rd_regs[1].valid;
  ret.inst.rd_reg.typ           = in.rd_regs[1].typ;
  ret.inst.rd_reg.regidx        = in.rd_regs[1].regidx;
  ret.inst.rd_reg.rnid          = in.rd_regs[1].rnid;
  ret.inst.rd_reg.ready         = in.rd_regs[1].ready | rs2_phy_hit;
  ret.inst.rd_reg.predict_ready[0] = rs2_rel_hit;
  ret.inst.rd_reg.predict_ready[1] = 1'b0;
  ret.inst.rd_reg.early_index      = rs2_rel_index;

  ret.rs2_rel_read_accepted = 1'b0;
  ret.rs2_phy_read_accepted = 1'b0;
  ret.is_rs2_get = 1'b0;

`ifdef SIMULATION
  ret.inst.sim_inst   = in.inst;
  ret.inst.sim_cat    = in.cat;

  ret.kanata_id = in.kanata_id;
`endif // SIMULATION

  return ret;
endfunction // assign_stq_disp


`ifdef SIMULATION
logic [$clog2(scariv_conf_pkg::STQ_SIZE): 0]      w_entry_valid_cnt;

always_ff @ (negedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
  end else begin
    if (w_disp_picked_num[$clog2(scariv_conf_pkg::STQ_SIZE)]) begin
      $fatal(0, "w_disp_picked_num MSB == 1, too much requests inserted\n");
    end
  end
end

/* verilator lint_off WIDTH */
bit_cnt #(.WIDTH(scariv_conf_pkg::STQ_SIZE)) u_entry_valid_cnt (.in(w_stq_valid), .out(w_entry_valid_cnt));

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
    $fwrite(fp, "    \"scariv_stq_entry[%d]\":{", index);
    $fwrite(fp, "valid:%d, ", entry.is_valid);
    $fwrite(fp, "pc_addr:\"0x%0x\", ", entry.inst.sim_pc_addr);
    $fwrite(fp, "inst:\"%08x\", ", entry.inst.sim_inst);

    $fwrite(fp, "cmt_id:%d, ", entry.inst.cmt_id);
    $fwrite(fp, "grp_id:%d, ", entry.inst.grp_id);

    $fwrite(fp, "\"");
    $fwrite(fp, "},\n");
  end // if (entry.valid)

endfunction // dump_json


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
    $fwrite(fp, "  \"scariv_stq\":{\n");
    for (int s_idx = 0; s_idx < scariv_conf_pkg::STQ_SIZE; s_idx++) begin
      dump_entry_json (fp, w_stq_entries[s_idx], s_idx);
    end
    $fwrite(fp, "  },\n");
  end
endfunction // dump_json
`endif // SIMULATION


endmodule // scariv_stq

module stq_ex1_upd_select
  import scariv_lsu_pkg::*;
  (
   stq_upd_if.slave           stq_upd_if[scariv_conf_pkg::LSU_INST_NUM],
   input scariv_pkg::cmt_id_t i_cmt_id,
   input scariv_pkg::grp_id_t i_grp_id,
   output logic               o_ex1_q_valid,
   output stq_ex1_update_t    o_ex1_q_updates
   );

logic [scariv_conf_pkg::LSU_INST_NUM-1: 0] w_ex1_update_match;
stq_ex1_update_t w_ex1_payloads[scariv_conf_pkg::LSU_INST_NUM];

generate for (genvar p_idx = 0; p_idx < scariv_conf_pkg::LSU_INST_NUM; p_idx++) begin : ex2_update_loop
  assign w_ex1_update_match[p_idx] = (stq_upd_if[p_idx].ex1_update &&
                                      stq_upd_if[p_idx].ex1_payload.cmt_id == i_cmt_id &&
                                      stq_upd_if[p_idx].ex1_payload.grp_id == i_grp_id);
  assign w_ex1_payloads[p_idx] = stq_upd_if[p_idx].ex1_payload;
end endgenerate

assign o_ex1_q_valid = |w_ex1_update_match;
bit_oh_or #(.T(stq_ex1_update_t), .WORDS(scariv_conf_pkg::LSU_INST_NUM)) bit_oh_update (.i_oh(w_ex1_update_match), .i_data(w_ex1_payloads), .o_selected(o_ex1_q_updates));

endmodule // stq_ex1_upd_select


module stq_ex2_upd_select
  import scariv_lsu_pkg::*;
  (
   stq_upd_if.slave           stq_upd_if[scariv_conf_pkg::LSU_INST_NUM],
   input scariv_pkg::cmt_id_t i_cmt_id,
   input scariv_pkg::grp_id_t i_grp_id,
   output logic               o_ex2_q_valid,
   output stq_ex2_update_t    o_ex2_q_updates
   );

logic [scariv_conf_pkg::LSU_INST_NUM-1: 0] w_ex2_update_match;
stq_ex2_update_t w_ex2_payloads[scariv_conf_pkg::LSU_INST_NUM];

generate for (genvar p_idx = 0; p_idx < scariv_conf_pkg::LSU_INST_NUM; p_idx++) begin : ex2_update_loop
  assign w_ex2_update_match[p_idx] = (stq_upd_if[p_idx].ex2_update &&
                                      stq_upd_if[p_idx].ex2_payload.cmt_id == i_cmt_id &&
                                      stq_upd_if[p_idx].ex2_payload.grp_id == i_grp_id);
  assign w_ex2_payloads[p_idx] = stq_upd_if[p_idx].ex2_payload;
end endgenerate

assign o_ex2_q_valid = |w_ex2_update_match;
bit_oh_or #(.T(stq_ex2_update_t), .WORDS(scariv_conf_pkg::LSU_INST_NUM)) bit_oh_update (.i_oh(w_ex2_update_match), .i_data(w_ex2_payloads), .o_selected(o_ex2_q_updates));

endmodule // stq_ex2_upd_select
