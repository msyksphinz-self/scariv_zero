module msrh_rename
  import msrh_pkg::*;
  #(parameter REG_TYPE = GPR)
(
   input logic i_clk,
   input logic i_reset_n,

   disp_if.slave iq_disp,
   input logic [msrh_pkg::CMT_ID_W-1:0] i_sc_new_cmt_id,

   input msrh_pkg::phy_wr_t i_phy_wr[msrh_pkg::TGT_BUS_SIZE],
   disp_if.master           sc_disp,

   // from Resource Allocator
   input logic [$clog2(msrh_conf_pkg::RV_BRU_ENTRY_SIZE)-1:0] i_brtag  [msrh_conf_pkg::DISP_SIZE],
   input logic [msrh_conf_pkg::RV_BRU_ENTRY_SIZE-1:0]         i_brmask [msrh_conf_pkg::DISP_SIZE],
   input logic                                                i_resource_ok,

   // Branch Tag Update Signal
   br_upd_if.slave                                            br_upd_if,

   input logic [$clog2(msrh_conf_pkg::RAS_ENTRY_SIZE)-1: 0] i_sc_ras_index,
   input logic [riscv_pkg::VADDR_W-1: 0]                    i_sc_ras_vaddr,

   // Committer Rename ID update
   input msrh_pkg::commit_blk_t   i_commit,
   input msrh_pkg::cmt_rnid_upd_t i_commit_rnid_update
   );

logic    w_iq_fire;

logic [RNID_W-1: 0]        w_rd_rnid[msrh_conf_pkg::DISP_SIZE];
logic [RNID_W-1: 0]        w_rd_old_rnid[msrh_conf_pkg::DISP_SIZE];

logic [msrh_conf_pkg::DISP_SIZE * 2-1: 0] w_archreg_valid;
logic [ 4: 0]                             w_archreg[msrh_conf_pkg::DISP_SIZE * 2];
logic [RNID_W-1: 0]                       w_rnid[msrh_conf_pkg::DISP_SIZE * 2];

logic [ 4: 0]                             w_update_arch_id [msrh_conf_pkg::DISP_SIZE];
logic [RNID_W-1: 0]                       w_update_rnid    [msrh_conf_pkg::DISP_SIZE];

disp_t [msrh_conf_pkg::DISP_SIZE-1:0]     w_disp_inst;
disp_t [msrh_conf_pkg::DISP_SIZE-1:0]     r_disp_inst;

logic [RNID_W-1: 0]                       rs1_rnid_fwd[msrh_conf_pkg::DISP_SIZE];
logic [RNID_W-1: 0]                       rs2_rnid_fwd[msrh_conf_pkg::DISP_SIZE];
logic [RNID_W-1: 0]                       rd_old_rnid_fwd[msrh_conf_pkg::DISP_SIZE];

logic [msrh_conf_pkg::DISP_SIZE * 2-1: 0] w_active;

logic                                     w_brupd_rnid_restore_valid;
logic                                     w_commit_flush_rnid_restore_valid;
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

logic                                     w_commit_flush;
logic                                     w_br_flush;
logic                                     w_flush_valid;

assign iq_disp.ready = !(i_commit_rnid_update.commit & (|i_commit.except_valid)) & i_resource_ok;

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
  assign w_push_freelist = r_commit_rnid_update_dly.commit &
                           r_commit_rnid_update_dly.rnid_valid[d_idx] &
                           (r_commit_rnid_update_dly.rd_typ[d_idx] == REG_TYPE) &
                           (REG_TYPE == GPR) & (r_commit_rnid_update_dly.rd_regidx[d_idx] != 'h0);

  // Pushed ID, normal commit inst                    => old ID
  //            dead instruction                      => new ID
  //            normal exception                      => new ID
  //            silent flush (actually normally exit) => old ID
  assign except_flush_valid = r_commit_rnid_update_dly.commit &
                              r_commit_rnid_update_dly.except_valid[d_idx] &
                              (r_commit_rnid_update_dly.except_type != msrh_pkg::SILENT_FLUSH) &
                              (r_commit_rnid_update_dly.except_type != msrh_pkg::ANOTHER_FLUSH);

  always_comb begin
    if (r_commit_rnid_update_dly.commit &
        !(r_commit_rnid_update_dly.dead_id[d_idx] | except_flush_valid)) begin
      // old ID push
      w_push_freelist_id = r_commit_rnid_update_dly.old_rnid[d_idx];
    end else begin
      w_push_freelist_id = r_commit_rnid_update_dly.rd_rnid[d_idx];
    end
  end

  logic w_freelist_pop;
  assign w_freelist_pop = iq_disp.inst[d_idx].valid &
                          iq_disp.inst[d_idx].wr_reg.valid &
                          (iq_disp.inst[d_idx].wr_reg.typ == REG_TYPE) &
                          ((REG_TYPE == GPR) ? (iq_disp.inst[d_idx].wr_reg.regidx != 'h0) : 1'b1);

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

    .i_pop(w_iq_fire & w_freelist_pop),
    .o_pop_id(w_rd_rnid_tmp)
  );
  assign w_rd_rnid[d_idx] = (REG_TYPE == GPR) & (iq_disp.inst[d_idx].wr_reg.regidx == 'h0) ? 'h0 : w_rd_rnid_tmp;
end
endgenerate


generate for (genvar d_idx = 0; d_idx < msrh_conf_pkg::DISP_SIZE; d_idx++) begin : src_rd_loop
  assign w_archreg_valid [d_idx*2 + 0] = iq_disp.inst[d_idx].rd_regs[0].valid & (iq_disp.inst[d_idx].rd_regs[0].typ == REG_TYPE);
  assign w_archreg_valid [d_idx*2 + 1] = iq_disp.inst[d_idx].rd_regs[1].valid & (iq_disp.inst[d_idx].rd_regs[0].typ == REG_TYPE);

  assign w_archreg [d_idx*2 + 0] = iq_disp.inst[d_idx].rd_regs[0].regidx;
  assign w_archreg [d_idx*2 + 1] = iq_disp.inst[d_idx].rd_regs[1].regidx;

  assign w_update_arch_id[d_idx] = w_rd_regidx[d_idx];
  assign w_update_rnid   [d_idx] = w_rd_rnid[d_idx];

end
endgenerate

assign w_brupd_rnid_restore_valid = br_upd_if.update & ~br_upd_if.dead & br_upd_if.mispredict;
msrh_pkg::commit_blk_t r_commit_dly;
logic                  r_commit_except_valid_dly;
msrh_pkg::cmt_rnid_upd_t r_commit_rnid_update_dly;

always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_commit_dly <= 'h0;
    r_commit_except_valid_dly <= 1'b0;
    r_commit_rnid_update_dly <= 'h0;
  end else begin
    r_commit_dly <= i_commit;
    r_commit_except_valid_dly <= w_commit_except_valid;
    r_commit_rnid_update_dly <= i_commit_rnid_update;
  end
end

assign w_commit_except_valid = msrh_pkg::is_flushed_commit(i_commit);

assign w_restore_valid = (|r_commit_except_valid_dly)  |                        // Exception : Restore from CommitMap
                         w_brupd_rnid_restore_valid; // Speculation Miss : Restore from Br Queue
assign w_restore_rn_list = (|r_commit_except_valid_dly) ? w_restore_commit_map_list :
                           w_restore_queue_list;

generate for (genvar d_idx = 0; d_idx < msrh_conf_pkg::DISP_SIZE; d_idx++) begin : cmt_rd_loop
  assign w_commit_rd_regidx[d_idx] = i_commit_rnid_update.rd_regidx[d_idx];
  assign w_commit_rd_rnid[d_idx]   = i_commit_rnid_update.rd_rnid[d_idx];

  assign w_commit_except_rd_valid[d_idx] = w_commit_except_valid & i_commit.grp_id[d_idx] & !i_commit.dead_id[d_idx];
end
endgenerate

msrh_rename_map
  #(.REG_TYPE(REG_TYPE))
u_msrh_rename_map
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

   .i_commit_rd_valid ({msrh_conf_pkg::DISP_SIZE{1'b0}}),
   .i_commit_rd_regidx(w_commit_rd_regidx),
   .i_commit_rd_rnid  (w_commit_rd_rnid),

   .o_rn_list (w_rn_list)
   );


generate for (genvar d_idx = 0; d_idx < msrh_conf_pkg::DISP_SIZE; d_idx++) begin : rd_loop
  assign w_rd_valids[d_idx] =  w_iq_fire & iq_disp.inst[d_idx].wr_reg.valid &
                               (iq_disp.inst[d_idx].wr_reg.typ == REG_TYPE);
  assign w_rd_regidx[d_idx] =  iq_disp.inst[d_idx].wr_reg.regidx;
  assign w_rd_data  [d_idx] = !iq_disp.inst[d_idx].wr_reg.valid;
end
endgenerate

assign w_iq_fire = ~w_flush_valid & iq_disp.valid & iq_disp.ready;

always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    sc_disp.valid <= 'h0;
    sc_disp.pc_addr <= 'h0;
    sc_disp.is_br_included <= 1'b0;

    // sc_disp.inst <= 'h0;
    r_disp_inst <= 'h0;
  end else begin
    sc_disp.valid            <= w_iq_fire;
    sc_disp.pc_addr          <= iq_disp.pc_addr;
    sc_disp.is_br_included   <= iq_disp.is_br_included;
    // sc_disp.inst             <= w_disp_inst;
    sc_disp.tlb_except_valid <= iq_disp.tlb_except_valid;
    sc_disp.tlb_except_cause <= iq_disp.tlb_except_cause;
    sc_disp.tlb_except_tval  <= iq_disp.tlb_except_tval;
    sc_disp.resource_cnt     <= iq_disp.resource_cnt;

    r_disp_inst <= w_disp_inst;
  end // else: !if(!i_reset_n)
end // always_ff @ (posedge i_clk, negedge i_reset_n)

assign sc_disp.cmt_id = i_sc_new_cmt_id;
always_comb begin
  sc_disp.inst = r_disp_inst;
  for (int d_idx = 0; d_idx < msrh_conf_pkg::DISP_SIZE; d_idx++) begin : ras_idx_loop
    sc_disp.inst[d_idx].ras_index      = i_sc_ras_index;
    if (sc_disp.inst[d_idx].is_call) begin
      sc_disp.inst[d_idx].ras_prev_vaddr = i_sc_ras_vaddr;  // When CALL, stack previous RAS address
    end
    // if (sc_disp.inst[d_idx].is_ret) begin
    //   sc_disp.inst[d_idx].pred_target_vaddr = i_sc_ras_vaddr;  // When RET, use pred adddres
    // end
  end
end

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
    if (iq_disp.inst[0].wr_reg.valid &&
        iq_disp.inst[0].wr_reg.typ   == iq_disp.inst[d_idx].rd_regs[0].typ &&
        iq_disp.inst[0].wr_reg.regidx == iq_disp.inst[d_idx].rd_regs[0].regidx) begin
      rs1_rnid_tmp_valid[0] = 1'b1;
      rs1_rnid_tmp      [0] = w_rd_rnid[0];
    end else begin
      rs1_rnid_tmp_valid[0] = 1'b0;
      rs1_rnid_tmp      [0] = w_rnid[d_idx * 2 + 0];
    end

    if (iq_disp.inst[0].wr_reg.valid &&
        iq_disp.inst[0].wr_reg.typ   == iq_disp.inst[d_idx].rd_regs[1].typ &&
        iq_disp.inst[0].wr_reg.regidx == iq_disp.inst[d_idx].rd_regs[1].regidx) begin
      rs2_rnid_tmp_valid[0] = 1'b1;
      rs2_rnid_tmp      [0] = w_rd_rnid[0];
    end else begin
      rs2_rnid_tmp_valid[0] = 1'b0;
      rs2_rnid_tmp      [0] = w_rnid[d_idx * 2 + 1];
    end // else: !if(iq_disp.inst[p_idx].wr_reg.valid &&...

    if (iq_disp.inst[0].wr_reg.valid &&
        iq_disp.inst[0].wr_reg.typ   == iq_disp.inst[d_idx].wr_reg.typ &&
        iq_disp.inst[0].wr_reg.regidx == iq_disp.inst[d_idx].wr_reg.regidx) begin
      rd_old_rnid_tmp_valid[0] = 1'b1;
      rd_old_rnid_tmp      [0] = w_rd_rnid[0];
    end else begin
      rd_old_rnid_tmp_valid[0] = 1'b0;
      rd_old_rnid_tmp      [0] = w_rd_old_rnid[d_idx];
    end // else: !if(iq_disp.inst[p_idx].wr_reg.valid &&...

    /* verilator lint_off UNSIGNED */
    for (int p_idx = 1; p_idx < d_idx; p_idx++) begin: prev_rd_loop
      if (iq_disp.inst[p_idx].wr_reg.valid &&
          iq_disp.inst[p_idx].wr_reg.typ   == iq_disp.inst[d_idx].rd_regs[0].typ &&
          iq_disp.inst[p_idx].wr_reg.regidx == iq_disp.inst[d_idx].rd_regs[0].regidx) begin
        rs1_rnid_tmp_valid[p_idx] = 1'b1;
        rs1_rnid_tmp      [p_idx] = w_rd_rnid[p_idx];
      end else begin
        rs1_rnid_tmp_valid[p_idx] = rs1_rnid_tmp_valid[p_idx-1];
        rs1_rnid_tmp      [p_idx] = rs1_rnid_tmp      [p_idx-1];
      end // else: !if(iq_disp.inst[p_idx].wr_reg.valid &&...

      if (iq_disp.inst[p_idx].wr_reg.valid &&
          iq_disp.inst[p_idx].wr_reg.typ   == iq_disp.inst[d_idx].rd_regs[1].typ &&
          iq_disp.inst[p_idx].wr_reg.regidx == iq_disp.inst[d_idx].rd_regs[1].regidx) begin
        rs2_rnid_tmp_valid[p_idx] = 1'b1;
        rs2_rnid_tmp      [p_idx] = w_rd_rnid[p_idx];
      end else begin
        rs2_rnid_tmp_valid[p_idx] = rs2_rnid_tmp_valid[p_idx-1];
        rs2_rnid_tmp      [p_idx] = rs2_rnid_tmp      [p_idx-1];
      end // else: !if(iq_disp.inst[p_idx].wr_reg.valid &&...

      if (iq_disp.inst[p_idx].wr_reg.valid &&
          iq_disp.inst[p_idx].wr_reg.typ   == iq_disp.inst[d_idx].wr_reg.typ &&
          iq_disp.inst[p_idx].wr_reg.regidx == iq_disp.inst[d_idx].wr_reg.regidx) begin
        rd_old_rnid_tmp_valid[p_idx] = 1'b1;
        rd_old_rnid_tmp      [p_idx] = w_rd_rnid[p_idx];
      end else begin
        rd_old_rnid_tmp_valid[p_idx] = rd_old_rnid_tmp_valid[p_idx-1];
        rd_old_rnid_tmp      [p_idx] = rd_old_rnid_tmp      [p_idx-1];
      end // else: !if(iq_disp.inst[p_idx].wr_reg.valid &&...
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
                                                  rs2_rnid_fwd[d_idx],
                                                  i_brtag[d_idx],
                                                  i_brmask[d_idx]);

end // block: src_rn_loop
endgenerate


logic [RNID_W-1: 0] w_rs1_rs2_rnid[msrh_conf_pkg::DISP_SIZE*2];
generate for (genvar d_idx = 0; d_idx < msrh_conf_pkg::DISP_SIZE; d_idx++) begin : op_loop
  assign w_rs1_rs2_rnid[d_idx*2+0] = rs1_rnid_fwd[d_idx];
  assign w_rs1_rs2_rnid[d_idx*2+1] = rs2_rnid_fwd[d_idx];
end
endgenerate

msrh_inflight_list
  #(.REG_TYPE(REG_TYPE))
u_inflight_map
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
logic [msrh_conf_pkg::DISP_SIZE-1: 0] w_is_br_inst;
generate for (genvar d_idx = 0; d_idx < msrh_conf_pkg::DISP_SIZE; d_idx++) begin : br_loop
  assign w_is_br_inst[d_idx] = w_iq_fire &
                               iq_disp.inst[d_idx].valid &
                               (iq_disp.inst[d_idx].cat == decoder_inst_cat_pkg::INST_CAT_BR);
end
endgenerate


msrh_bru_rn_snapshots
u_msrh_bru_rn_snapshots
  (
   .i_clk (i_clk),
   .i_reset_n(i_reset_n),

   .i_rn_list (w_rn_list),

   .i_load ({msrh_conf_pkg::DISP_SIZE{w_iq_fire}} & w_is_br_inst),

   .i_rd_valid   (w_rd_valids),
   .i_rd_archreg (w_update_arch_id),
   .i_rd_rnid    (w_rd_rnid),
   .i_brtag      (i_brtag  ),

   .br_upd_if (br_upd_if),
   .o_rn_list (w_restore_queue_list)
   );


// Commit Map
msrh_commit_map
  #(.REG_TYPE(REG_TYPE))
u_commit_map
  (
   .i_clk (i_clk),
   .i_reset_n(i_reset_n),

   .i_commit_rnid_update(i_commit_rnid_update),
   .o_rnid_map (w_restore_commit_map_list)
   );

assign w_commit_flush = msrh_pkg::is_flushed_commit(i_commit);
assign w_br_flush     = br_upd_if.update & ~br_upd_if.dead & br_upd_if.mispredict;
assign w_flush_valid  = w_commit_flush | w_br_flush;

`ifdef SIMULATION
function void dump_json(string name, int fp);
  $fwrite(fp, "  \"msrh_%s_rename\" : {\n", name);

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

      $fwrite(fp, "        rd_valid   : \"%d\",", sc_disp.inst[d_idx].wr_reg.valid);
      $fwrite(fp, "        rd_type    : \"%d\",", sc_disp.inst[d_idx].wr_reg.typ);
      $fwrite(fp, "        rd_regidx  : \"%d\",", sc_disp.inst[d_idx].wr_reg.regidx);
      $fwrite(fp, "        rd_rnid    : \"%d\",", sc_disp.inst[d_idx].wr_reg.rnid);

      $fwrite(fp, "        rs1_valid  : \"%d\",", sc_disp.inst[d_idx].rd_regs[0].valid);
      $fwrite(fp, "        rs1_type   : \"%d\",", sc_disp.inst[d_idx].rd_regs[0].typ);
      $fwrite(fp, "        rs1_regidx : \"%d\",", sc_disp.inst[d_idx].rd_regs[0].regidx);
      $fwrite(fp, "        rs1_rnid   : \"%d\",", sc_disp.inst[d_idx].rd_regs[0].rnid);
      $fwrite(fp, "        rs1_ready  : \"%d\",", sc_disp.inst[d_idx].rd_regs[0].ready);

      $fwrite(fp, "        rs2_valid  : \"%d\",", sc_disp.inst[d_idx].rd_regs[1].valid);
      $fwrite(fp, "        rs2_type   : \"%d\",", sc_disp.inst[d_idx].rd_regs[1].typ);
      $fwrite(fp, "        rs2_regidx : \"%d\",", sc_disp.inst[d_idx].rd_regs[1].regidx);
      $fwrite(fp, "        rs2_rnid   : \"%d\",", sc_disp.inst[d_idx].rd_regs[1].rnid);
      $fwrite(fp, "        rs2_ready  : \"%d\",", sc_disp.inst[d_idx].rd_regs[1].ready);

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
