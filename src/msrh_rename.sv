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
   cre_ret_if.slave  rob_cre_ret_if,
   cre_ret_if.master alu_cre_ret_if[msrh_conf_pkg::ALU_INST_NUM],
   cre_ret_if.master lsu_cre_ret_if[msrh_conf_pkg::LSU_INST_NUM],
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
logic [msrh_conf_pkg::DISP_SIZE-1: 0]     w_commit_rd_valid;
logic [ 4: 0]                             w_commit_rd_regidx[msrh_conf_pkg::DISP_SIZE];
logic [RNID_W-1: 0]                       w_commit_rd_rnid[msrh_conf_pkg::DISP_SIZE];

logic [msrh_conf_pkg::DISP_SIZE-1: 0]     w_rd_valids;
logic [ 4: 0]                             w_rd_regidx[msrh_conf_pkg::DISP_SIZE];
logic [msrh_conf_pkg::DISP_SIZE-1: 0]     w_rd_data;

// Current rename map information to stack
logic [RNID_W-1: 0]                       w_rn_list[32];
logic [RNID_W-1: 0]                       w_restore_rn_list[32];

logic                                     w_flush_valid;

// -----------------------------
// Credits / Return Interface
// -----------------------------
logic [msrh_conf_pkg::DISP_SIZE-1: 0] w_inst_is_arith;
logic [msrh_conf_pkg::DISP_SIZE-1: 0] w_inst_is_ld;
logic [msrh_conf_pkg::DISP_SIZE-1: 0] w_inst_is_st;
logic [msrh_conf_pkg::DISP_SIZE-1: 0] w_inst_is_br;
logic [msrh_conf_pkg::DISP_SIZE-1: 0] w_inst_is_csu;

logic [$clog2(msrh_conf_pkg::DISP_SIZE): 0] w_inst_cnt_arith;
logic [$clog2(msrh_conf_pkg::DISP_SIZE): 0] w_inst_cnt_ld;
logic [$clog2(msrh_conf_pkg::DISP_SIZE): 0] w_inst_cnt_st;
logic [$clog2(msrh_conf_pkg::DISP_SIZE): 0] w_inst_cnt_br;
logic [$clog2(msrh_conf_pkg::DISP_SIZE): 0] w_inst_cnt_csu;

logic [$clog2(msrh_conf_pkg::RV_ALU_ENTRY_SIZE): 0] w_alu_credits[msrh_conf_pkg::ALU_INST_NUM];
logic [$clog2(msrh_lsu_pkg::MEM_Q_SIZE): 0]         w_lsu_credits[msrh_conf_pkg::LSU_INST_NUM];
logic [$clog2(msrh_conf_pkg::RV_CSU_ENTRY_SIZE): 0] w_csu_credits;
logic [$clog2(msrh_conf_pkg::RV_BRU_ENTRY_SIZE): 0] w_br_credits;

logic                                               w_rob_no_credits_remained;
logic [msrh_conf_pkg::ALU_INST_NUM-1: 0]            w_alu_no_credits_remained;
logic [msrh_conf_pkg::LSU_INST_NUM-1: 0]            w_lsu_no_credits_remained;
logic                                               w_csu_no_credits_remained;
logic                                               w_bru_no_credits_remained;

assign iq_disp.ready = !(w_rob_no_credits_remained |
                         (|w_alu_no_credits_remained) |
                         (|w_lsu_no_credits_remained) |
                         w_csu_no_credits_remained |
                         w_bru_no_credits_remained);

generate for (genvar d_idx = 0; d_idx < msrh_conf_pkg::DISP_SIZE; d_idx++) begin : free_loop
  logic [RNID_W-1: 0] w_rd_rnid_tmp;
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

    .i_push(i_commit_rnid_update.commit &
            i_commit_rnid_update.rnid_valid[d_idx] &
            (i_commit_rnid_update.rd_regidx[d_idx] != 'h0)),
    .i_push_id(i_commit_rnid_update.commit & (i_commit_rnid_update.all_dead | i_commit_rnid_update.dead_id[d_idx]) ?
               i_commit_rnid_update.rd_rnid[d_idx] : i_commit_rnid_update.old_rnid[d_idx]),

    .i_pop(w_iq_fire &
           iq_disp.inst[d_idx].valid &
           iq_disp.inst[d_idx].rd_valid &
           (iq_disp.inst[d_idx].rd_regidx != 'h0)),
    .o_pop_id(w_rd_rnid_tmp)
  );
  assign w_rd_rnid[d_idx] = iq_disp.inst[d_idx].rd_regidx != 'h0 ? w_rd_rnid_tmp : 'h0;
end
endgenerate

// `ifdef SIMULATION
// generate for (genvar d_idx = 0; d_idx < msrh_conf_pkg::DISP_SIZE; d_idx++) begin
//
//   logic [RNID_W-1: 0] freelist_model[$];
//   logic [RNID_W-1: 0] pop_data;
//
//   initial begin
//     for (int i = 0; i < 32; i++) begin
//       /* verilator lint_off WIDTH */
//       freelist_model.push_back(32 + d_idx * FLIST_SIZE + i);
//     end
//   end
//
//   always_ff @ (negedge i_clk, negedge i_reset_n) begin
//     if (i_reset_n) begin
//       if (free_loop[d_idx].u_freelist.i_push) begin
//         freelist_model.push_back(free_loop[d_idx].u_freelist.i_push_id);
//       end
//       if (free_loop[d_idx].u_freelist.i_pop) begin
//         pop_data = freelist_model.pop_front();
//         if (free_loop[d_idx].u_freelist.o_pop_id != pop_data) begin
//           $fatal(0, "Pop back error. RTL=%d, MODEL=%d\n", free_loop[d_idx].u_freelist.o_pop_id, pop_data);
//         end
//       end
//     end
//
//     if (freelist_model.size > 32) begin
//       $fatal(0, "freelist_model shouldn't be over 32");
//     end
//   end
// end // for (int d_idx = 0; d_idx < msrh_conf_pkg::DISP_SIZE; d_idx++)
// endgenerate
//
// `endif // SIMULATION


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

assign w_commit_rd_valid = {msrh_conf_pkg::DISP_SIZE{w_commit_rnid_restore_valid & i_commit_rnid_update.upd_pc_valid}} &
                           i_commit_rnid_update.rnid_valid & ~i_commit_rnid_update.dead_id;

generate for (genvar d_idx = 0; d_idx < msrh_conf_pkg::DISP_SIZE; d_idx++) begin : cmt_rd_loop
  assign w_commit_rd_regidx[d_idx] = i_commit_rnid_update.rd_regidx[d_idx];
  assign w_commit_rd_rnid[d_idx]   = i_commit_rnid_update.rd_rnid[d_idx];
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

   .i_restore_from_queue (w_commit_rnid_restore_valid & i_commit_rnid_update.upd_pc_valid),
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
     .o_rn_list (w_restore_rn_list),

     .o_full (/*xxx*/)
     );


// -----------------------------
// Credits / Return Interface
// -----------------------------
generate for (genvar d_idx = 0; d_idx < msrh_conf_pkg::DISP_SIZE; d_idx++) begin : disp_loop
  assign w_inst_is_arith[d_idx] = iq_disp.inst[d_idx].valid & (iq_disp.inst[d_idx].cat == decoder_inst_cat_pkg::INST_CAT_ARITH);
  assign w_inst_is_ld   [d_idx] = iq_disp.inst[d_idx].valid & (iq_disp.inst[d_idx].cat == decoder_inst_cat_pkg::INST_CAT_LD  );
  assign w_inst_is_st   [d_idx] = iq_disp.inst[d_idx].valid & (iq_disp.inst[d_idx].cat == decoder_inst_cat_pkg::INST_CAT_ST  );
  assign w_inst_is_br   [d_idx] = iq_disp.inst[d_idx].valid & (iq_disp.inst[d_idx].cat == decoder_inst_cat_pkg::INST_CAT_BR  );
  assign w_inst_is_csu  [d_idx] = iq_disp.inst[d_idx].valid & (iq_disp.inst[d_idx].cat == decoder_inst_cat_pkg::INST_CAT_CSU );
end
endgenerate

bit_cnt #(.WIDTH(msrh_conf_pkg::DISP_SIZE)) u_arith_cnt (.in(w_inst_is_arith), .out(w_inst_cnt_arith));
bit_cnt #(.WIDTH(msrh_conf_pkg::DISP_SIZE)) u_ld_cnt    (.in(w_inst_is_ld   ), .out(w_inst_cnt_ld   ));
bit_cnt #(.WIDTH(msrh_conf_pkg::DISP_SIZE)) u_st_cnt    (.in(w_inst_is_st   ), .out(w_inst_cnt_st   ));
bit_cnt #(.WIDTH(msrh_conf_pkg::DISP_SIZE)) u_bru_cnt   (.in(w_inst_is_br   ), .out(w_inst_cnt_br   ));
bit_cnt #(.WIDTH(msrh_conf_pkg::DISP_SIZE)) u_csu_cnt   (.in(w_inst_is_csu  ), .out(w_inst_cnt_csu  ));

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
  msrh_credit_return_master
    #(.MAX_CREDITS(msrh_conf_pkg::RV_ALU_ENTRY_SIZE))
  u_alu_credit_return
  (
   .i_clk(i_clk),
   .i_reset_n(i_reset_n),

   .i_get_credit(~w_flush_valid & (|w_inst_cnt_arith) & iq_disp.ready),
   /* verilator lint_off WIDTH */
   .i_credit_val(w_inst_cnt_arith),

   .o_credits(w_alu_credits[a_idx]),
   .o_no_credits(w_alu_no_credits_remained[a_idx]),

   .cre_ret_if (alu_cre_ret_if[a_idx])
   );
end // block: alu_cre_ret_loop
endgenerate

generate for (genvar l_idx = 0; l_idx < msrh_conf_pkg::LSU_INST_NUM; l_idx++) begin : lsu_cre_ret_loop
  msrh_credit_return_master
    #(.MAX_CREDITS(msrh_lsu_pkg::MEM_Q_SIZE))
  u_lsu_credit_return
  (
   .i_clk(i_clk),
   .i_reset_n(i_reset_n),

   .i_get_credit(~w_flush_valid & ((|w_inst_cnt_ld) | (|w_inst_cnt_st)) & iq_disp.ready),
   .i_credit_val(w_inst_cnt_ld + w_inst_cnt_st),   /* verilator lint_off WIDTH */

   .o_credits(w_lsu_credits[l_idx]),
   .o_no_credits(w_lsu_no_credits_remained[l_idx]),

   .cre_ret_if (lsu_cre_ret_if[l_idx])
   );

end
endgenerate

msrh_credit_return_master
  #(.MAX_CREDITS(msrh_conf_pkg::RV_CSU_ENTRY_SIZE))
u_csu_credit_return
(
 .i_clk(i_clk),
 .i_reset_n(i_reset_n),

 .i_get_credit(~w_flush_valid & (|w_inst_cnt_csu) & iq_disp.ready),
 .i_credit_val(w_inst_cnt_csu),   /* verilator lint_off WIDTH */

 .o_credits(w_csu_credits),
 .o_no_credits(w_csu_no_credits_remained),

 .cre_ret_if (csu_cre_ret_if)
);

msrh_credit_return_master
  #(.MAX_CREDITS(msrh_conf_pkg::RV_BRU_ENTRY_SIZE))
u_bru_credit_return
(
 .i_clk(i_clk),
 .i_reset_n(i_reset_n),

 .i_get_credit(~w_flush_valid & (|w_inst_cnt_br) & iq_disp.ready),
 .i_credit_val(w_inst_cnt_br),   /* verilator lint_off WIDTH */

 .o_credits(w_br_credits),
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
`endif // SIMULATION

endmodule // msrh_rename
