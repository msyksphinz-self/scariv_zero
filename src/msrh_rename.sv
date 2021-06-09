module msrh_rename
  import msrh_pkg::*;
  (
   input logic i_clk,
   input logic i_reset_n,

   disp_if.slave iq_disp,
   input logic [msrh_pkg::CMT_ID_W-1:0] i_sc_new_cmt_id,

   input msrh_pkg::phy_wr_t i_phy_wr[msrh_pkg::TGT_BUS_SIZE],
   disp_if.master           sc_disp,

   // Committer Rename ID update
   input msrh_pkg::commit_blk_t   i_commit,
   input msrh_pkg::cmt_rnid_upd_t i_commit_rnid_update,

   // -------------------------------
   // Credit Return Update interface
   // -------------------------------
   cre_ret_if.master rob_cre_ret_if,
   cre_ret_if.master alu_cre_ret_if[msrh_conf_pkg::ALU_INST_NUM],
   // cre_ret_if.master lsu_cre_ret_if[msrh_conf_pkg::LSU_INST_NUM],
   cre_ret_if.master ldq_cre_ret_if,
   cre_ret_if.master stq_cre_ret_if,
   cre_ret_if.master csu_cre_ret_if,
   cre_ret_if.master bru_cre_ret_if
   );

logic    w_iq_fire;

logic [RNID_W-1: 0]        w_rd_rnid[msrh_conf_pkg::DISP_SIZE];
logic [RNID_W-1: 0]        w_rd_old_rnid[msrh_conf_pkg::DISP_SIZE];

logic [msrh_conf_pkg::DISP_SIZE * 2-1: 0] w_archreg_valid;
logic [ 4: 0]                             w_archreg[msrh_conf_pkg::DISP_SIZE * 2];
logic [RNID_W-1: 0]                       w_rnid[msrh_conf_pkg::DISP_SIZE * 2];

logic [ 4: 0]                             w_update_arch_id [msrh_conf_pkg::DISP_SIZE];
logic [RNID_W-1: 0]                       w_update_rnid    [msrh_conf_pkg::DISP_SIZE];

disp_t [msrh_conf_pkg::DISP_SIZE-1:0] w_disp_inst;

logic [RNID_W-1: 0]                       rs1_rnid_fwd[msrh_conf_pkg::DISP_SIZE];
logic [RNID_W-1: 0]                       rs2_rnid_fwd[msrh_conf_pkg::DISP_SIZE];
logic [RNID_W-1: 0]                       rd_old_rnid_fwd[msrh_conf_pkg::DISP_SIZE];

logic [msrh_conf_pkg::DISP_SIZE * 2-1: 0] w_active;

logic                                     w_commit_rnid_restore_valid;
logic                                     w_commit_flush_rnid_restore_valid;
logic [msrh_conf_pkg::DISP_SIZE-1: 0]     w_commit_rd_valid;
logic                                     w_commit_except_valid;
logic [msrh_conf_pkg::DISP_SIZE-1: 0]     w_commit_except_rd_valid;
logic [ 4: 0]                             w_commit_rd_regidx[msrh_conf_pkg::DISP_SIZE];
logic [RNID_W-1: 0]                       w_commit_rd_rnid[msrh_conf_pkg::DISP_SIZE];

logic [msrh_conf_pkg::DISP_SIZE-1: 0]     w_rd_valids;
logic [ 4: 0]                             w_rd_regidx[msrh_conf_pkg::DISP_SIZE];
logic [msrh_conf_pkg::DISP_SIZE-1: 0]     w_rd_data;

// Current rename map information to stack
logic                                     w_restore_valid;
logic [RNID_W-1: 0]                       w_rn_list[32];
logic [RNID_W-1: 0]                       w_restore_rn_list[32];
logic [RNID_W-1: 0]                       w_restore_queue_list[32];
logic [RNID_W-1: 0]                       w_restore_commit_map_list[32];

logic                                     w_flush_valid;

// -----------------------------
// Credits / Return Interface
// -----------------------------
// logic [msrh_conf_pkg::DISP_SIZE-1: 0] w_inst_is_arith;
// logic [msrh_conf_pkg::DISP_SIZE-1: 0] w_inst_is_ld;
// logic [msrh_conf_pkg::DISP_SIZE-1: 0] w_inst_is_st;
// logic [msrh_conf_pkg::DISP_SIZE-1: 0] w_inst_is_br;
// logic [msrh_conf_pkg::DISP_SIZE-1: 0] w_inst_is_csu;
//
// logic [$clog2(msrh_conf_pkg::DISP_SIZE): 0] w_inst_cnt_arith;
// logic [$clog2(msrh_conf_pkg::DISP_SIZE): 0] w_inst_cnt_ld;
// logic [$clog2(msrh_conf_pkg::DISP_SIZE): 0] w_inst_cnt_st;
// logic [$clog2(msrh_conf_pkg::DISP_SIZE): 0] w_inst_cnt_br;
// logic [$clog2(msrh_conf_pkg::DISP_SIZE): 0] w_inst_cnt_csu;

logic                                               w_rob_no_credits_remained;
logic [msrh_conf_pkg::ALU_INST_NUM-1: 0]            w_alu_no_credits_remained;
logic [msrh_conf_pkg::LSU_INST_NUM-1: 0]            w_lsu_no_credits_remained;
logic                                               w_ldq_no_credits_remained;
logic                                               w_stq_no_credits_remained;
logic                                               w_csu_no_credits_remained;
logic                                               w_bru_no_credits_remained;

assign iq_disp.ready = !(i_commit_rnid_update.commit & (i_commit.flush_valid | i_commit.all_dead)) &
                       !(w_rob_no_credits_remained |
                         (|w_alu_no_credits_remained) |
                         (|w_lsu_no_credits_remained) |
                         w_ldq_no_credits_remained |
                         w_stq_no_credits_remained |
                         w_csu_no_credits_remained |
                         w_bru_no_credits_remained);


//                                          Freelist      RenameMap
// normal commit inst                    => old ID push / no update
// dead instruction                      => new ID push / no update
// normal exception                      => new ID push / restore
// silent flush (actually normally exit) => old ID push / no update

generate for (genvar d_idx = 0; d_idx < msrh_conf_pkg::DISP_SIZE; d_idx++) begin : free_loop
  logic [RNID_W-1: 0] w_rd_rnid_tmp;

  logic                 w_push_freelist;
  logic                 except_flush_valid;
  logic [RNID_W-1: 0]   w_push_freelist_id;

  // When instruction commit normally, return old RNID
  // even thouhg instruction is dead, newly allocated RNID should be return
  assign w_push_freelist = i_commit_rnid_update.commit &
                           i_commit_rnid_update.rnid_valid[d_idx] &
                           (i_commit_rnid_update.rd_regidx[d_idx] != 'h0);
  // Pushed ID, normal commit inst                    => old ID
  //            dead instruction                      => new ID
  //            normal exception                      => new ID
  //            silent flush (actually normally exit) => old ID
  assign except_flush_valid = i_commit_rnid_update.commit &
                              i_commit_rnid_update.except_valid[d_idx] &
                              (i_commit_rnid_update.except_type != msrh_pkg::SILENT_FLUSH);

  always_comb begin
    if (i_commit_rnid_update.commit &
        !i_commit_rnid_update.all_dead &
        !(i_commit_rnid_update.dead_id[d_idx] | except_flush_valid)) begin
      // old ID push
      w_push_freelist_id = i_commit_rnid_update.old_rnid[d_idx];
    end else begin
      w_push_freelist_id = i_commit_rnid_update.rd_rnid[d_idx];
    end
  end

  msrh_freelist
    #(
      .SIZE (FLIST_SIZE),
      .WIDTH (RNID_W),
      .INIT (FLIST_SIZE * d_idx + 32)
      )
  u_freelist
    (
    .i_clk     (i_clk ),
    .i_reset_n (i_reset_n),

    .i_push(w_push_freelist),
    .i_push_id(w_push_freelist_id),

    .i_pop(w_iq_fire &
           iq_disp.inst[d_idx].valid &
           iq_disp.inst[d_idx].rd_valid &
           (iq_disp.inst[d_idx].rd_regidx != 'h0)),
    .o_pop_id(w_rd_rnid_tmp)
  );
  assign w_rd_rnid[d_idx] = iq_disp.inst[d_idx].rd_regidx != 'h0 ? w_rd_rnid_tmp : 'h0;
end
endgenerate


generate for (genvar d_idx = 0; d_idx < msrh_conf_pkg::DISP_SIZE; d_idx++) begin : src_rd_loop
  assign w_archreg_valid [d_idx*2 + 0] = iq_disp.inst[d_idx].rs1_valid;
  assign w_archreg_valid [d_idx*2 + 1] = iq_disp.inst[d_idx].rs2_valid;

  assign w_archreg [d_idx*2 + 0] = iq_disp.inst[d_idx].rs1_regidx;
  assign w_archreg [d_idx*2 + 1] = iq_disp.inst[d_idx].rs2_regidx;

  assign w_update_arch_id[d_idx] = w_rd_regidx[d_idx];
  assign w_update_rnid   [d_idx] = w_rd_rnid[d_idx];

end
endgenerate

assign w_commit_rnid_restore_valid = i_commit_rnid_update.commit &
                                     i_commit_rnid_update.is_br_included;
// assign w_commit_flush_rnid_restore_valid = i_commit.commit &
//                                            i_commit.flush_valid & !i_commit.all_dead;
//
assign w_commit_rd_valid = ({msrh_conf_pkg::DISP_SIZE{w_commit_rnid_restore_valid & i_commit_rnid_update.upd_pc_valid}} | w_commit_except_rd_valid) &
                           i_commit_rnid_update.rnid_valid & ~i_commit_rnid_update.dead_id;

assign w_commit_except_valid = i_commit.commit & (|i_commit.except_valid) & !i_commit.all_dead;

assign w_restore_valid = (|w_commit_except_valid)  |                        // Exception : Restore from CommitMap
                         w_commit_rnid_restore_valid & i_commit_rnid_update.upd_pc_valid; // Speculation Miss : Restore from Br Queue
assign w_restore_rn_list = (|w_commit_except_valid) ? w_restore_commit_map_list :
                           w_restore_queue_list;

generate for (genvar d_idx = 0; d_idx < msrh_conf_pkg::DISP_SIZE; d_idx++) begin : cmt_rd_loop
  assign w_commit_rd_regidx[d_idx] = i_commit_rnid_update.rd_regidx[d_idx];
  assign w_commit_rd_rnid[d_idx]   = i_commit_rnid_update.rd_rnid[d_idx];

  assign w_commit_except_rd_valid[d_idx] = (i_commit.commit & i_commit.except_valid[d_idx] & (i_commit.except_type == msrh_pkg::SILENT_FLUSH)) |
                                           (w_commit_except_valid & i_commit.grp_id[d_idx] & !i_commit.dead_id[d_idx] &
                                            ((i_commit.except_valid[d_idx] & (i_commit.except_type != msrh_pkg::SILENT_FLUSH)) ? 1'b0 : 1'b1));
end
endgenerate

msrh_rename_map u_msrh_rename_map
  (
   .i_clk     (i_clk),
   .i_reset_n (i_reset_n),

   .i_arch_valid (w_archreg_valid),
   .i_arch_id    (w_archreg),
   .o_rnid       (w_rnid),

   .i_rd_regidx   (w_rd_regidx),
   .o_rd_old_rnid (w_rd_old_rnid),

   .i_update         (w_rd_valids),
   .i_update_arch_id (w_update_arch_id),
   .i_update_rnid    (w_update_rnid   ),

   .i_restore_from_queue (w_restore_valid  ),
   .i_restore_rn_list    (w_restore_rn_list),

   .i_commit_rd_valid (w_commit_rd_valid),
   .i_commit_rd_regidx(w_commit_rd_regidx),
   .i_commit_rd_rnid  (w_commit_rd_rnid),

   .o_rn_list (w_rn_list)
   );


generate for (genvar d_idx = 0; d_idx < msrh_conf_pkg::DISP_SIZE; d_idx++) begin : rd_loop
  assign w_rd_valids[d_idx] =  w_iq_fire & iq_disp.inst[d_idx].rd_valid;
  assign w_rd_regidx[d_idx] =  iq_disp.inst[d_idx].rd_regidx;
  assign w_rd_data  [d_idx] = !iq_disp.inst[d_idx].rd_valid;
end
endgenerate

assign w_iq_fire = ~w_flush_valid & iq_disp.valid & iq_disp.ready;

always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    sc_disp.valid <= 'h0;
    sc_disp.pc_addr <= 'h0;
    sc_disp.is_br_included <= 1'b0;
    // sc_disp.cat <= 'h0;
    sc_disp.inst <= 'h0;
  end else begin
    sc_disp.valid          <= w_iq_fire;
    sc_disp.pc_addr        <= iq_disp.pc_addr;
    sc_disp.is_br_included <= iq_disp.is_br_included;
    sc_disp.inst           <= w_disp_inst;
    sc_disp.tlb_except_valid <= iq_disp.tlb_except_valid;
    sc_disp.tlb_except_cause <= iq_disp.tlb_except_cause;
  end // else: !if(!i_reset_n)
end // always_ff @ (posedge i_clk, negedge i_reset_n)

assign sc_disp.cmt_id = i_sc_new_cmt_id;

generate for (genvar d_idx = 0; d_idx < msrh_conf_pkg::DISP_SIZE; d_idx++) begin : src_rn_loop
  /* verilator lint_off UNOPTFLAT */
  logic [RNID_W-1: 0] rs1_rnid_tmp[msrh_conf_pkg::DISP_SIZE];
  logic [msrh_conf_pkg::DISP_SIZE-1: 0] rs1_rnid_tmp_valid;

  logic [RNID_W-1: 0] rs2_rnid_tmp[msrh_conf_pkg::DISP_SIZE];
  logic [msrh_conf_pkg::DISP_SIZE-1: 0] rs2_rnid_tmp_valid;

  logic [RNID_W-1: 0]         rd_old_rnid_tmp[msrh_conf_pkg::DISP_SIZE];
  logic [msrh_conf_pkg::DISP_SIZE-1: 0] rd_old_rnid_tmp_valid;

  always_comb begin

    /* initial index of loop */
    if (iq_disp.inst[0].rd_valid &&
        iq_disp.inst[0].rd_type   == iq_disp.inst[d_idx].rs1_type &&
        iq_disp.inst[0].rd_regidx == iq_disp.inst[d_idx].rs1_regidx) begin
      rs1_rnid_tmp_valid[0] = 1'b1;
      rs1_rnid_tmp      [0] = w_rd_rnid[0];
    end else begin
      rs1_rnid_tmp_valid[0] = 1'b0;
      rs1_rnid_tmp      [0] = w_rnid[d_idx * 2 + 0];
    end

    if (iq_disp.inst[0].rd_valid &&
        iq_disp.inst[0].rd_type   == iq_disp.inst[d_idx].rs2_type &&
        iq_disp.inst[0].rd_regidx == iq_disp.inst[d_idx].rs2_regidx) begin
      rs2_rnid_tmp_valid[0] = 1'b1;
      rs2_rnid_tmp      [0] = w_rd_rnid[0];
    end else begin
      rs2_rnid_tmp_valid[0] = 1'b0;
      rs2_rnid_tmp      [0] = w_rnid[d_idx * 2 + 1];
    end // else: !if(iq_disp.inst[p_idx].rd_valid &&...

    if (iq_disp.inst[0].rd_valid &&
        iq_disp.inst[0].rd_type   == iq_disp.inst[d_idx].rd_type &&
        iq_disp.inst[0].rd_regidx == iq_disp.inst[d_idx].rd_regidx) begin
      rd_old_rnid_tmp_valid[0] = 1'b1;
      rd_old_rnid_tmp      [0] = w_rd_rnid[0];
    end else begin
      rd_old_rnid_tmp_valid[0] = 1'b0;
      rd_old_rnid_tmp      [0] = w_rd_old_rnid[d_idx];
    end // else: !if(iq_disp.inst[p_idx].rd_valid &&...

    /* verilator lint_off UNSIGNED */
    for (int p_idx = 1; p_idx < d_idx; p_idx++) begin: prev_rd_loop
      if (iq_disp.inst[p_idx].rd_valid &&
          iq_disp.inst[p_idx].rd_type   == iq_disp.inst[d_idx].rs1_type &&
          iq_disp.inst[p_idx].rd_regidx == iq_disp.inst[d_idx].rs1_regidx) begin
        rs1_rnid_tmp_valid[p_idx] = 1'b1;
        rs1_rnid_tmp      [p_idx] = w_rd_rnid[p_idx];
      end else begin
        rs1_rnid_tmp_valid[p_idx] = rs1_rnid_tmp_valid[p_idx-1];
        rs1_rnid_tmp      [p_idx] = rs1_rnid_tmp      [p_idx-1];
      end // else: !if(iq_disp.inst[p_idx].rd_valid &&...

      if (iq_disp.inst[p_idx].rd_valid &&
          iq_disp.inst[p_idx].rd_type   == iq_disp.inst[d_idx].rs2_type &&
          iq_disp.inst[p_idx].rd_regidx == iq_disp.inst[d_idx].rs2_regidx) begin
        rs2_rnid_tmp_valid[p_idx] = 1'b1;
        rs2_rnid_tmp      [p_idx] = w_rd_rnid[p_idx];
      end else begin
        rs2_rnid_tmp_valid[p_idx] = rs2_rnid_tmp_valid[p_idx-1];
        rs2_rnid_tmp      [p_idx] = rs2_rnid_tmp      [p_idx-1];
      end // else: !if(iq_disp.inst[p_idx].rd_valid &&...

      if (iq_disp.inst[p_idx].rd_valid &&
          iq_disp.inst[p_idx].rd_type   == iq_disp.inst[d_idx].rd_type &&
          iq_disp.inst[p_idx].rd_regidx == iq_disp.inst[d_idx].rd_regidx) begin
        rd_old_rnid_tmp_valid[p_idx] = 1'b1;
        rd_old_rnid_tmp      [p_idx] = w_rd_rnid[p_idx];
      end else begin
        rd_old_rnid_tmp_valid[p_idx] = rd_old_rnid_tmp_valid[p_idx-1];
        rd_old_rnid_tmp      [p_idx] = rd_old_rnid_tmp      [p_idx-1];
      end // else: !if(iq_disp.inst[p_idx].rd_valid &&...
    end // block: prev_rd_loop

  end // always_comb

  /* verilator lint_off SELRANGE */
  assign rs1_rnid_fwd[d_idx] = (d_idx == 0) ? w_rnid[0] : rs1_rnid_tmp[d_idx-1];
  assign rs2_rnid_fwd[d_idx] = (d_idx == 0) ? w_rnid[1] : rs2_rnid_tmp[d_idx-1];

  assign rd_old_rnid_fwd[d_idx] = (d_idx == 0) ? w_rd_old_rnid[0] : rd_old_rnid_tmp[d_idx-1];

  assign w_disp_inst[d_idx] = assign_disp_rename (iq_disp.inst[d_idx],
                                                            w_rd_rnid[d_idx],
                                                            rd_old_rnid_fwd[d_idx],
                                                            w_active [d_idx*2+0],
                                                            rs1_rnid_fwd[d_idx],
                                                            w_active [d_idx*2+1],
                                                            rs2_rnid_fwd[d_idx]);

end // block: src_rn_loop
endgenerate


logic [RNID_W-1: 0] w_rs1_rs2_rnid[msrh_conf_pkg::DISP_SIZE*2];
generate for (genvar d_idx = 0; d_idx < msrh_conf_pkg::DISP_SIZE; d_idx++) begin : op_loop
  assign w_rs1_rs2_rnid[d_idx*2+0] = rs1_rnid_fwd[d_idx];
  assign w_rs1_rs2_rnid[d_idx*2+1] = rs2_rnid_fwd[d_idx];
end
endgenerate

msrh_inflight_list u_inflight_map
  (
   .i_clk     (i_clk),
   .i_reset_n (i_reset_n),

   .i_rnid   (w_rs1_rs2_rnid),
   .o_valids (w_active),

   .i_update_fetch_valid (w_rd_valids),
   .i_update_fetch_rnid  (w_rd_rnid  ),
   .i_update_fetch_data  (w_rd_data  ),

   .i_phy_wr (i_phy_wr)
);

// Map List Queue
msrh_rn_map_queue
  u_rn_map_queue
    (
     .i_clk (i_clk),
     .i_reset_n(i_reset_n),

     .i_load (w_iq_fire & iq_disp.is_br_included),
     .i_rn_list (w_rn_list),

     .i_restore (w_commit_rnid_restore_valid),
     .o_rn_list (w_restore_queue_list),

     .o_full (/*xxx*/)
     );


// Commit Map
msrh_commit_map
u_commit_map
  (
   .i_clk (i_clk),
   .i_reset_n(i_reset_n),

   .i_commit_rnid_update(i_commit_rnid_update),
   .o_rnid_map (w_restore_commit_map_list)
   );


// -----------------------------
// Credits / Return Interface
// -----------------------------
// generate for (genvar d_idx = 0; d_idx < msrh_conf_pkg::DISP_SIZE; d_idx++) begin : disp_loop
//   assign w_inst_is_arith[d_idx] = iq_disp.inst[d_idx].valid & (iq_disp.inst[d_idx].cat == decoder_inst_cat_pkg::INST_CAT_ARITH);
//   assign w_inst_is_ld   [d_idx] = iq_disp.inst[d_idx].valid & (iq_disp.inst[d_idx].cat == decoder_inst_cat_pkg::INST_CAT_LD  );
//   assign w_inst_is_st   [d_idx] = iq_disp.inst[d_idx].valid & (iq_disp.inst[d_idx].cat == decoder_inst_cat_pkg::INST_CAT_ST  );
//   assign w_inst_is_br   [d_idx] = iq_disp.inst[d_idx].valid & (iq_disp.inst[d_idx].cat == decoder_inst_cat_pkg::INST_CAT_BR  );
//   assign w_inst_is_csu  [d_idx] = iq_disp.inst[d_idx].valid & (iq_disp.inst[d_idx].cat == decoder_inst_cat_pkg::INST_CAT_CSU );
// end
// endgenerate
//
// bit_cnt #(.WIDTH(msrh_conf_pkg::DISP_SIZE)) u_arith_cnt (.in(w_inst_is_arith), .out(w_inst_cnt_arith));
// bit_cnt #(.WIDTH(msrh_conf_pkg::DISP_SIZE)) u_ld_cnt    (.in(w_inst_is_ld   ), .out(w_inst_cnt_ld   ));
// bit_cnt #(.WIDTH(msrh_conf_pkg::DISP_SIZE)) u_st_cnt    (.in(w_inst_is_st   ), .out(w_inst_cnt_st   ));
// bit_cnt #(.WIDTH(msrh_conf_pkg::DISP_SIZE)) u_bru_cnt   (.in(w_inst_is_br   ), .out(w_inst_cnt_br   ));
// bit_cnt #(.WIDTH(msrh_conf_pkg::DISP_SIZE)) u_csu_cnt   (.in(w_inst_is_csu  ), .out(w_inst_cnt_csu  ));

assign w_flush_valid = i_commit.commit & i_commit.flush_valid & !i_commit.all_dead;


msrh_credit_return_master
  #(.MAX_CREDITS(msrh_conf_pkg::CMT_ENTRY_SIZE))
u_rob_credit_return
(
 .i_clk(i_clk),
 .i_reset_n(i_reset_n),

 .i_get_credit(~w_flush_valid & w_iq_fire),
 .i_credit_val('h1),

 .o_credits(),
 .o_no_credits(w_rob_no_credits_remained),

 .cre_ret_if (rob_cre_ret_if)
);


generate for (genvar a_idx = 0; a_idx < msrh_conf_pkg::ALU_INST_NUM; a_idx++) begin : alu_cre_ret_loop
  logic w_inst_arith_valid;
  assign w_inst_arith_valid = iq_disp.valid & |iq_disp.resource_cnt.alu_inst_cnt[a_idx];
  logic [$clog2(msrh_conf_pkg::RV_ALU_ENTRY_SIZE):0] w_alu_inst_cnt;
  /* verilator lint_off WIDTH */
  assign w_alu_inst_cnt = iq_disp.resource_cnt.alu_inst_cnt[a_idx];

  msrh_credit_return_master
    #(.MAX_CREDITS(msrh_conf_pkg::RV_ALU_ENTRY_SIZE))
  u_alu_credit_return
  (
   .i_clk(i_clk),
   .i_reset_n(i_reset_n),

   .i_get_credit(~w_flush_valid & w_inst_arith_valid & iq_disp.ready),
   .i_credit_val(w_alu_inst_cnt),

   .o_credits(),
   .o_no_credits(w_alu_no_credits_remained[a_idx]),

   .cre_ret_if (alu_cre_ret_if[a_idx])
   );
end // block: alu_cre_ret_loop
endgenerate

generate for (genvar l_idx = 0; l_idx < msrh_conf_pkg::LSU_INST_NUM; l_idx++) begin : lsu_cre_ret_loop
//   logic w_inst_lsu_valid;
//   assign w_inst_lsu_valid = iq_disp.valid & |iq_disp.resource_cnt.lsu_inst_cnt[l_idx];
//   logic [$clog2(msrh_lsu_pkg::MEM_Q_SIZE):0] w_lsu_inst_cnt;
//   assign w_lsu_inst_cnt = iq_disp.resource_cnt.lsu_inst_cnt[l_idx];
//
//   msrh_credit_return_master
//     #(.MAX_CREDITS(msrh_lsu_pkg::MEM_Q_SIZE))
//   u_lsu_credit_return
//   (
//    .i_clk(i_clk),
//    .i_reset_n(i_reset_n),
//
//    .i_get_credit(~w_flush_valid & w_inst_lsu_valid & iq_disp.ready),
//    .i_credit_val(w_lsu_inst_cnt),
//
//    .o_credits(),
//    .o_no_credits(w_lsu_no_credits_remained[l_idx]),
//
//    .cre_ret_if (lsu_cre_ret_if[l_idx])
//    );
  assign w_lsu_no_credits_remained[l_idx] = 1'b0;
end
endgenerate


logic   w_inst_ld_valid;
assign w_inst_ld_valid = iq_disp.valid & |iq_disp.resource_cnt.ld_inst_cnt;
msrh_credit_return_master
  #(.MAX_CREDITS(msrh_conf_pkg::LDQ_SIZE))
u_ldq_credit_return
(
 .i_clk(i_clk),
 .i_reset_n(i_reset_n),

 .i_get_credit(~w_flush_valid & w_inst_ld_valid & iq_disp.ready),
 .i_credit_val(iq_disp.resource_cnt.ld_inst_cnt),

 .o_credits(),
 .o_no_credits(w_ldq_no_credits_remained),

 .cre_ret_if (ldq_cre_ret_if)
);


logic   w_inst_st_valid;
assign w_inst_st_valid = iq_disp.valid & |iq_disp.resource_cnt.st_inst_cnt;
msrh_credit_return_master
  #(.MAX_CREDITS(msrh_conf_pkg::STQ_SIZE))
u_stq_credit_return
(
 .i_clk(i_clk),
 .i_reset_n(i_reset_n),

 .i_get_credit(~w_flush_valid & w_inst_st_valid & iq_disp.ready),
 .i_credit_val(iq_disp.resource_cnt.st_inst_cnt),

 .o_credits    (),
 .o_no_credits (w_stq_no_credits_remained),

 .cre_ret_if (stq_cre_ret_if)
);


logic   w_inst_csu_valid;
assign w_inst_csu_valid = iq_disp.valid & |iq_disp.resource_cnt.csu_inst_cnt;
logic [$clog2(msrh_conf_pkg::RV_CSU_ENTRY_SIZE):0] w_inst_csu_cnt;
assign w_inst_csu_cnt = iq_disp.resource_cnt.csu_inst_cnt;
msrh_credit_return_master
  #(.MAX_CREDITS(msrh_conf_pkg::RV_CSU_ENTRY_SIZE))
u_csu_credit_return
(
 .i_clk(i_clk),
 .i_reset_n(i_reset_n),

 .i_get_credit(~w_flush_valid & w_inst_csu_valid & iq_disp.ready),
 .i_credit_val(w_inst_csu_cnt),

 .o_credits(),
 .o_no_credits(w_csu_no_credits_remained),

 .cre_ret_if (csu_cre_ret_if)
);

logic   w_inst_bru_valid;
assign w_inst_bru_valid = iq_disp.valid & |iq_disp.resource_cnt.bru_inst_cnt;
logic [$clog2(msrh_conf_pkg::RV_BRU_ENTRY_SIZE):0] w_bru_inst_cnt;
assign w_bru_inst_cnt = iq_disp.resource_cnt.bru_inst_cnt;
msrh_credit_return_master
  #(.MAX_CREDITS(msrh_conf_pkg::RV_BRU_ENTRY_SIZE))
u_bru_credit_return
(
 .i_clk(i_clk),
 .i_reset_n(i_reset_n),

 .i_get_credit(~w_flush_valid & w_inst_bru_valid & iq_disp.ready),
 .i_credit_val(w_bru_inst_cnt),

 .o_credits(),
 .o_no_credits(w_bru_no_credits_remained),

 .cre_ret_if (bru_cre_ret_if)
);


`ifdef SIMULATION
function void dump_json(int fp);
  $fwrite(fp, "  \"msrh_rename\" : {\n");

  if (sc_disp.valid) begin
    $fwrite(fp, "    \"sc_disp\" : {\n");
    $fwrite(fp, "      valid  : \"%d\",\n", sc_disp.valid);
    $fwrite(fp, "      ready  : \"%d\",\n", sc_disp.ready);
    $fwrite(fp, "      cmt_id  : \"%d\",\n", sc_disp.cmt_id);
    $fwrite(fp, "      pc_addr : \"0x%08x\",\n", sc_disp.pc_addr);

    for (int d_idx = 0; d_idx < msrh_conf_pkg::DISP_SIZE; d_idx++) begin : disp_loop
      $fwrite(fp, "      \"inst[%d]\" : {", d_idx);
      $fwrite(fp, "        valid : \"%d\",",      sc_disp.inst[d_idx].valid);
      $fwrite(fp, "        inst  : \"%08x\",",     sc_disp.inst[d_idx].inst);
      $fwrite(fp, "        pc_addr : \"%0x\",",   sc_disp.inst[d_idx].pc_addr);

      $fwrite(fp, "        rd_valid   : \"%d\",", sc_disp.inst[d_idx].rd_valid);
      $fwrite(fp, "        rd_type    : \"%d\",", sc_disp.inst[d_idx].rd_type);
      $fwrite(fp, "        rd_regidx  : \"%d\",", sc_disp.inst[d_idx].rd_regidx);
      $fwrite(fp, "        rd_rnid    : \"%d\",", sc_disp.inst[d_idx].rd_rnid);

      $fwrite(fp, "        rs1_valid  : \"%d\",", sc_disp.inst[d_idx].rs1_valid);
      $fwrite(fp, "        rs1_type   : \"%d\",", sc_disp.inst[d_idx].rs1_type);
      $fwrite(fp, "        rs1_regidx : \"%d\",", sc_disp.inst[d_idx].rs1_regidx);
      $fwrite(fp, "        rs1_rnid   : \"%d\",", sc_disp.inst[d_idx].rs1_rnid);
      $fwrite(fp, "        rs1_ready  : \"%d\",", sc_disp.inst[d_idx].rs1_ready);

      $fwrite(fp, "        rs2_valid  : \"%d\",", sc_disp.inst[d_idx].rs2_valid);
      $fwrite(fp, "        rs2_type   : \"%d\",", sc_disp.inst[d_idx].rs2_type);
      $fwrite(fp, "        rs2_regidx : \"%d\",", sc_disp.inst[d_idx].rs2_regidx);
      $fwrite(fp, "        rs2_rnid   : \"%d\",", sc_disp.inst[d_idx].rs2_rnid);
      $fwrite(fp, "        rs2_ready  : \"%d\",", sc_disp.inst[d_idx].rs2_ready);

      $fwrite(fp, "        cat[d_idx] : \"%d\",", sc_disp.inst[d_idx].cat);
      $fwrite(fp, "      },\n");
    end

    // $fwrite(fp, "    \"freelist[]\": {", d_idx);
    // $fwrite(fp, "      \"head_ptr\": %d", free_loop[d_idx].u_freelist.r_head_ptr);
    // $fwrite(fp, "      \"tail_ptr\": %d", free_loop[d_idx].u_freelist.r_tail_ptr);
    // $fwrite(fp, "      \"freelist\": {", );
    // for (int f_idx = 0; f_idx < FLIST_SIZE; f_idx++) begin
    //   $fwrite(fp, "%d,", free_loop[d_idx].u_freelist.r_freelist[f_idx]);
    // end
    // $fwrite(fp, "      }\n", );
  end // if (sc_disp.valid & sc_disp.ready)
  $fwrite(fp, "  },\n");

endfunction // dump

logic [RNID_W-1: 0] w_rnid_list[RNID_SIZE];
generate for (genvar d_idx = 0; d_idx < msrh_conf_pkg::DISP_SIZE; d_idx++) begin : rn_loop
  for (genvar f_idx = 0; f_idx < msrh_pkg::FLIST_SIZE; f_idx++) begin : flist_loop
    assign w_rnid_list[d_idx * FLIST_SIZE + f_idx] = free_loop[d_idx].u_freelist.r_freelist[f_idx];
  end
end
endgenerate
generate for (genvar r_idx = 0; r_idx < 32; r_idx++) begin : rmap_loop
  assign w_rnid_list[msrh_conf_pkg::DISP_SIZE * FLIST_SIZE + r_idx] = u_msrh_rename_map.r_map[r_idx];
end
endgenerate

always_ff @ (negedge i_clk, negedge i_reset_n) begin
  if (i_reset_n) begin
    for (int f1_idx = 0; f1_idx < RNID_SIZE; f1_idx++) begin : list_check1_loop
      for (int f2_idx = 0; f2_idx < RNID_SIZE; f2_idx++) begin : list_check2_loop
        if (f1_idx != f2_idx) begin
          if (w_rnid_list[f1_idx] !='h0 && (w_rnid_list[f1_idx] == w_rnid_list[f2_idx])) begin
            $fatal(0, "Index %d(%2d, %2d) and %d(%2d, %2d) are same ID: %3d\n",
                   f1_idx[$clog2(RNID_SIZE)-1: 0], f1_idx[$clog2(RNID_SIZE)-1: 0] / msrh_pkg::FLIST_SIZE, f1_idx[$clog2(RNID_SIZE)-1: 0] % msrh_pkg::FLIST_SIZE,
                   f2_idx[$clog2(RNID_SIZE)-1: 0], f2_idx[$clog2(RNID_SIZE)-1: 0] / msrh_pkg::FLIST_SIZE, f2_idx[$clog2(RNID_SIZE)-1: 0] % msrh_pkg::FLIST_SIZE,
                   w_rnid_list[f1_idx]);
          end
        end
      end
    end
  end // if (i_reset_n)
end // always_ff @ (negedge i_clk, negedge i_reset_n)

`endif // SIMULATION

endmodule // msrh_rename
