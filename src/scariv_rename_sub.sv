// ------------------------------------------------------------------------
// NAME : Submodule of Rename Unit
// TYPE : module
// ------------------------------------------------------------------------
// Rename Unit for each register types, INT, FP
// ------------------------------------------------------------------------
// ------------------------------------------------------------------------

module scariv_rename_sub
  import scariv_pkg::*;
  #(parameter REG_TYPE = GPR)
(
 input logic i_clk,
 input logic i_reset_n,

 output logic                    o_freelist_ready,

 input logic                     i_ibuf_front_fire,
 input scariv_front_pkg::front_t i_ibuf_front_payload,

 input scariv_pkg::phy_wr_t i_phy_wr[scariv_pkg::TGT_BUS_SIZE],

 // from Resource Allocator
 input brtag_t i_brtag  [scariv_conf_pkg::DISP_SIZE],

 // Branch Tag Update Signal
 br_upd_if.slave        br_upd_if,

 output disp_t [scariv_conf_pkg::DISP_SIZE-1:0] o_disp_inst,

 // Committer Rename ID update
 input scariv_pkg::commit_blk_t   i_commit,
 input scariv_pkg::cmt_rnid_upd_t i_commit_rnid_update
 );

localparam NUM_OPERANDS = REG_TYPE == FPR ? 3 :
                          2;   // REG_TYPE == INT

logic [scariv_conf_pkg::DISP_SIZE-1: 0] w_freelist_empty;
logic                                   w_all_freelist_ready;

rnid_t        w_rd_rnid[scariv_conf_pkg::DISP_SIZE];
rnid_t        w_rd_old_rnid[scariv_conf_pkg::DISP_SIZE];

logic [scariv_conf_pkg::DISP_SIZE * NUM_OPERANDS-1: 0] w_archreg_valid;
logic [ 4: 0]                             w_archreg[scariv_conf_pkg::DISP_SIZE * NUM_OPERANDS];
rnid_t                       w_rnid[scariv_conf_pkg::DISP_SIZE * NUM_OPERANDS];

logic [ 4: 0]                             w_update_arch_id [scariv_conf_pkg::DISP_SIZE];
rnid_t                       w_update_rnid    [scariv_conf_pkg::DISP_SIZE];

rnid_t                       rs1_rnid_fwd[scariv_conf_pkg::DISP_SIZE];
rnid_t                       rs2_rnid_fwd[scariv_conf_pkg::DISP_SIZE];
rnid_t                       rs3_rnid_fwd[scariv_conf_pkg::DISP_SIZE];
rnid_t                       rd_old_rnid_fwd[scariv_conf_pkg::DISP_SIZE];

logic [scariv_conf_pkg::DISP_SIZE * NUM_OPERANDS-1: 0] w_active;

logic                                     w_brupd_rnid_restore_valid;
logic                                     w_commit_flush_rnid_restore_valid;
logic                                     w_commit_except_valid;
grp_id_t     w_commit_except_rd_valid;
logic [ 4: 0]                             w_commit_rd_regidx[scariv_conf_pkg::DISP_SIZE];
rnid_t                       w_commit_rd_rnid[scariv_conf_pkg::DISP_SIZE];

grp_id_t     w_rd_valids;
logic [ 4: 0]                             w_rd_regidx[scariv_conf_pkg::DISP_SIZE];
grp_id_t     w_rd_data;

// Current rename map information to stack
logic                                     w_restore_valid;
rnid_t                       w_rn_list[32];
rnid_t                       w_restore_rn_list[32];
rnid_t                       w_restore_queue_list[32];
rnid_t                       w_restore_commit_map_list[32];

assign w_all_freelist_ready = ~(|w_freelist_empty);
assign o_freelist_ready = w_all_freelist_ready;

//                                          Freelist      RenameMap
// normal commit inst                    => old ID push / no update
// dead instruction                      => new ID push / no update
// normal exception                      => new ID push / restore
// silent flush (actually normally exit) => old ID push / no update

generate for (genvar d_idx = 0; d_idx < scariv_conf_pkg::DISP_SIZE; d_idx++) begin : free_loop
  rnid_t w_rd_rnid_tmp;

  logic                 w_push_freelist;
  logic                 except_flush_valid;
  logic                 is_active_flush;
  rnid_t   w_push_freelist_id;

  // When instruction commit normally, return old RNID
  // even thouhg instruction is dead, newly allocated RNID should be return
  assign w_push_freelist = r_commit_rnid_update_dly.commit &
                           r_commit_rnid_update_dly.rnid_valid[d_idx] &
                           (r_commit_rnid_update_dly.rd_typ[d_idx] == REG_TYPE) &
                           ((REG_TYPE == GPR) ? (r_commit_rnid_update_dly.rd_regidx[d_idx] != 'h0) : 1'b1);

  // Pushed ID, normal commit inst                    => old ID
  //            dead instruction                      => new ID
  //            normal exception                      => new ID
  //            silent flush (actually normally exit) => old ID
  assign except_flush_valid = r_commit_rnid_update_dly.commit &
                              r_commit_rnid_update_dly.except_valid[d_idx] &
                              (r_commit_rnid_update_dly.except_type != scariv_pkg::SILENT_FLUSH);
  // Another Flush generate flush even though it is (actually) dead.
  // Another Flush is not marked as dead, but it is actually dead.
  // Freelist must be receive new ID
  assign is_active_flush = r_commit_rnid_update_dly.except_valid[d_idx] &
                           (r_commit_rnid_update_dly.except_type == scariv_pkg::ANOTHER_FLUSH);

  always_comb begin
    if (r_commit_rnid_update_dly.commit &
        (r_commit_rnid_update_dly.dead_id[d_idx] | except_flush_valid | is_active_flush)) begin
      // Must be roll back
      w_push_freelist_id = r_commit_rnid_update_dly.rd_rnid[d_idx];
    end else begin
      // old ID push
      w_push_freelist_id = r_commit_rnid_update_dly.old_rnid[d_idx];
    end
  end

  logic w_freelist_pop;
  assign w_freelist_pop = i_ibuf_front_payload.inst[d_idx].valid &
                          i_ibuf_front_payload.inst[d_idx].wr_reg.valid &
                          (i_ibuf_front_payload.inst[d_idx].wr_reg.typ == REG_TYPE) &
                          ((REG_TYPE == GPR) ? (i_ibuf_front_payload.inst[d_idx].wr_reg.regidx != 'h0) : 1'b1);

  scariv_freelist
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

    .i_pop(i_ibuf_front_fire & w_freelist_pop),
    .o_pop_id(w_rd_rnid_tmp),

     .o_is_empty (w_freelist_empty[d_idx])
  );
  assign w_rd_rnid[d_idx] = (REG_TYPE == GPR) & (i_ibuf_front_payload.inst[d_idx].wr_reg.regidx == 'h0) ? 'h0 : w_rd_rnid_tmp;
end
endgenerate


generate for (genvar d_idx = 0; d_idx < scariv_conf_pkg::DISP_SIZE; d_idx++) begin : src_rd_loop
  for (genvar rs_idx = 0; rs_idx < NUM_OPERANDS; rs_idx++) begin : rs_idx_loop
    assign w_archreg_valid [d_idx * NUM_OPERANDS + rs_idx] = i_ibuf_front_payload.inst[d_idx].rd_regs[rs_idx].valid & (i_ibuf_front_payload.inst[d_idx].rd_regs[rs_idx].typ == REG_TYPE);
    assign w_archreg       [d_idx * NUM_OPERANDS + rs_idx] = i_ibuf_front_payload.inst[d_idx].rd_regs[rs_idx].regidx;
  end

  assign w_update_arch_id[d_idx] = w_rd_regidx[d_idx];
  assign w_update_rnid   [d_idx] = w_rd_rnid[d_idx];

end
endgenerate

assign w_brupd_rnid_restore_valid = br_upd_if.update & ~br_upd_if.dead & br_upd_if.mispredict;
scariv_pkg::commit_blk_t r_commit_dly;
logic                  r_commit_except_valid_dly;
scariv_pkg::cmt_rnid_upd_t r_commit_rnid_update_dly;

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

assign w_commit_except_valid = scariv_pkg::is_flushed_commit(i_commit);

assign w_restore_valid = (|r_commit_except_valid_dly)  |                        // Exception : Restore from CommitMap
                         w_brupd_rnid_restore_valid; // Speculation Miss : Restore from Br Queue
assign w_restore_rn_list = (|r_commit_except_valid_dly) ? w_restore_commit_map_list :
                           w_restore_queue_list;

generate for (genvar d_idx = 0; d_idx < scariv_conf_pkg::DISP_SIZE; d_idx++) begin : cmt_rd_loop
  assign w_commit_rd_regidx[d_idx] = i_commit_rnid_update.rd_regidx[d_idx];
  assign w_commit_rd_rnid[d_idx]   = i_commit_rnid_update.rd_rnid[d_idx];

  assign w_commit_except_rd_valid[d_idx] = w_commit_except_valid & i_commit.grp_id[d_idx] & !i_commit.dead_id[d_idx];
end
endgenerate

scariv_rename_map
  #(.REG_TYPE(REG_TYPE))
u_scariv_rename_map
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

   .i_commit_rd_valid ({scariv_conf_pkg::DISP_SIZE{1'b0}}),
   .i_commit_rd_regidx(w_commit_rd_regidx),
   .i_commit_rd_rnid  (w_commit_rd_rnid),

   .o_rn_list (w_rn_list)
   );


generate for (genvar d_idx = 0; d_idx < scariv_conf_pkg::DISP_SIZE; d_idx++) begin : rd_loop
  assign w_rd_valids[d_idx] =  i_ibuf_front_fire & i_ibuf_front_payload.inst[d_idx].wr_reg.valid &
                               (i_ibuf_front_payload.inst[d_idx].wr_reg.typ == REG_TYPE);
  assign w_rd_regidx[d_idx] =  i_ibuf_front_payload.inst[d_idx].wr_reg.regidx;
  assign w_rd_data  [d_idx] = !i_ibuf_front_payload.inst[d_idx].wr_reg.valid;
end
endgenerate


generate for (genvar d_idx = 0; d_idx < scariv_conf_pkg::DISP_SIZE; d_idx++) begin : src_rn_loop
  /* verilator lint_off UNOPTFLAT */
  rnid_t   rs1_rnid_tmp[scariv_conf_pkg::DISP_SIZE];
  grp_id_t rs1_rnid_tmp_valid;

  rnid_t   rs2_rnid_tmp[scariv_conf_pkg::DISP_SIZE];
  grp_id_t rs2_rnid_tmp_valid;

  rnid_t   rs3_rnid_tmp[scariv_conf_pkg::DISP_SIZE];
  grp_id_t rs3_rnid_tmp_valid;

  rnid_t   rd_old_rnid_tmp[scariv_conf_pkg::DISP_SIZE];
  grp_id_t rd_old_rnid_tmp_valid;

  always_comb begin

    /* initial index of loop */
    if (i_ibuf_front_payload.inst[0].wr_reg.valid &&
        i_ibuf_front_payload.inst[0].wr_reg.typ    == i_ibuf_front_payload.inst[d_idx].rd_regs[0].typ &&
        i_ibuf_front_payload.inst[0].wr_reg.regidx == i_ibuf_front_payload.inst[d_idx].rd_regs[0].regidx) begin
      rs1_rnid_tmp_valid[0] = 1'b1;
      rs1_rnid_tmp      [0] = w_rd_rnid[0];
    end else begin
      rs1_rnid_tmp_valid[0] = 1'b0;
      rs1_rnid_tmp      [0] = w_rnid[d_idx * NUM_OPERANDS + 0];
    end

    if (i_ibuf_front_payload.inst[0].wr_reg.valid &&
        i_ibuf_front_payload.inst[0].wr_reg.typ    == i_ibuf_front_payload.inst[d_idx].rd_regs[1].typ &&
        i_ibuf_front_payload.inst[0].wr_reg.regidx == i_ibuf_front_payload.inst[d_idx].rd_regs[1].regidx) begin
      rs2_rnid_tmp_valid[0] = 1'b1;
      rs2_rnid_tmp      [0] = w_rd_rnid[0];
    end else begin
      rs2_rnid_tmp_valid[0] = 1'b0;
      rs2_rnid_tmp      [0] = w_rnid[d_idx * NUM_OPERANDS + 1];
    end // else: !if(i_ibuf_front_payload.inst[p_idx].wr_reg.valid &&...

    if (NUM_OPERANDS >= 3) begin
      if (i_ibuf_front_payload.inst[0].wr_reg.valid &&
          i_ibuf_front_payload.inst[0].wr_reg.typ    == i_ibuf_front_payload.inst[d_idx].rd_regs[2].typ &&
          i_ibuf_front_payload.inst[0].wr_reg.regidx == i_ibuf_front_payload.inst[d_idx].rd_regs[2].regidx) begin
        rs3_rnid_tmp_valid[0] = 1'b1;
        rs3_rnid_tmp      [0] = w_rd_rnid[0];
      end else begin
        rs3_rnid_tmp_valid[0] = 1'b0;
        rs3_rnid_tmp      [0] = w_rnid[d_idx * NUM_OPERANDS + 2];
      end // else: !if(i_ibuf_front_payload.inst[p_idx].wr_reg.valid &&...
    end // if (NUM_OPERANDS >= 3)

    if (i_ibuf_front_payload.inst[0].wr_reg.valid &&
        i_ibuf_front_payload.inst[0].wr_reg.typ    == i_ibuf_front_payload.inst[d_idx].wr_reg.typ &&
        i_ibuf_front_payload.inst[0].wr_reg.regidx == i_ibuf_front_payload.inst[d_idx].wr_reg.regidx) begin
      rd_old_rnid_tmp_valid[0] = 1'b1;
      rd_old_rnid_tmp      [0] = w_rd_rnid[0];
    end else begin
      rd_old_rnid_tmp_valid[0] = 1'b0;
      rd_old_rnid_tmp      [0] = w_rd_old_rnid[d_idx];
    end // else: !if(i_ibuf_front_payload.inst[p_idx].wr_reg.valid &&...

    /* verilator lint_off UNSIGNED */
    for (int p_idx = 1; p_idx < d_idx; p_idx++) begin: prev_rd_loop
      if (i_ibuf_front_payload.inst[p_idx].wr_reg.valid &&
          i_ibuf_front_payload.inst[p_idx].wr_reg.typ    == i_ibuf_front_payload.inst[d_idx].rd_regs[0].typ &&
          i_ibuf_front_payload.inst[p_idx].wr_reg.regidx == i_ibuf_front_payload.inst[d_idx].rd_regs[0].regidx) begin
        rs1_rnid_tmp_valid[p_idx] = 1'b1;
        rs1_rnid_tmp      [p_idx] = w_rd_rnid[p_idx];
      end else begin
        rs1_rnid_tmp_valid[p_idx] = rs1_rnid_tmp_valid[p_idx-1];
        rs1_rnid_tmp      [p_idx] = rs1_rnid_tmp      [p_idx-1];
      end // else: !if(i_ibuf_front_payload.inst[p_idx].wr_reg.valid &&...

      if (i_ibuf_front_payload.inst[p_idx].wr_reg.valid &&
          i_ibuf_front_payload.inst[p_idx].wr_reg.typ    == i_ibuf_front_payload.inst[d_idx].rd_regs[1].typ &&
          i_ibuf_front_payload.inst[p_idx].wr_reg.regidx == i_ibuf_front_payload.inst[d_idx].rd_regs[1].regidx) begin
        rs2_rnid_tmp_valid[p_idx] = 1'b1;
        rs2_rnid_tmp      [p_idx] = w_rd_rnid[p_idx];
      end else begin
        rs2_rnid_tmp_valid[p_idx] = rs2_rnid_tmp_valid[p_idx-1];
        rs2_rnid_tmp      [p_idx] = rs2_rnid_tmp      [p_idx-1];
      end // else: !if(i_ibuf_front_payload.inst[p_idx].wr_reg.valid &&...

      if (NUM_OPERANDS >= 3) begin
        if (i_ibuf_front_payload.inst[p_idx].wr_reg.valid &&
            i_ibuf_front_payload.inst[p_idx].wr_reg.typ    == i_ibuf_front_payload.inst[d_idx].rd_regs[2].typ &&
            i_ibuf_front_payload.inst[p_idx].wr_reg.regidx == i_ibuf_front_payload.inst[d_idx].rd_regs[2].regidx) begin
          rs3_rnid_tmp_valid[p_idx] = 1'b1;
          rs3_rnid_tmp      [p_idx] = w_rd_rnid[p_idx];
        end else begin
          rs3_rnid_tmp_valid[p_idx] = rs3_rnid_tmp_valid[p_idx-1];
          rs3_rnid_tmp      [p_idx] = rs3_rnid_tmp      [p_idx-1];
        end
      end // if (NUM_OPERANDS >= 3)

      if (i_ibuf_front_payload.inst[p_idx].wr_reg.valid &&
          i_ibuf_front_payload.inst[p_idx].wr_reg.typ    == i_ibuf_front_payload.inst[d_idx].wr_reg.typ &&
          i_ibuf_front_payload.inst[p_idx].wr_reg.regidx == i_ibuf_front_payload.inst[d_idx].wr_reg.regidx) begin
        rd_old_rnid_tmp_valid[p_idx] = 1'b1;
        rd_old_rnid_tmp      [p_idx] = w_rd_rnid[p_idx];
      end else begin
        rd_old_rnid_tmp_valid[p_idx] = rd_old_rnid_tmp_valid[p_idx-1];
        rd_old_rnid_tmp      [p_idx] = rd_old_rnid_tmp      [p_idx-1];
      end // else: !if(i_ibuf_front_payload.inst[p_idx].wr_reg.valid &&...
    end // block: prev_rd_loop

  end // always_comb

  /* verilator lint_off SELRANGE */
  assign rs1_rnid_fwd[d_idx] = (d_idx == 0) ? w_rnid[0] : rs1_rnid_tmp[d_idx-1];
  assign rs2_rnid_fwd[d_idx] = (d_idx == 0) ? w_rnid[1] : rs2_rnid_tmp[d_idx-1];
  if (NUM_OPERANDS >= 3) begin
    assign rs3_rnid_fwd[d_idx] = (d_idx == 0) ? w_rnid[2] : rs3_rnid_tmp[d_idx-1];
  end
  assign rd_old_rnid_fwd[d_idx] = (d_idx == 0) ? w_rd_old_rnid[0] : rd_old_rnid_tmp[d_idx-1];

  assign o_disp_inst[d_idx] = assign_disp_rename (i_ibuf_front_payload.inst[d_idx],
                                                  w_rd_rnid[d_idx],
                                                  rd_old_rnid_fwd[d_idx],
                                                  w_active [d_idx * NUM_OPERANDS + 0],
                                                  rs1_rnid_fwd[d_idx],
                                                  w_active [d_idx * NUM_OPERANDS + 1],
                                                  rs2_rnid_fwd[d_idx],
                                                  w_active [d_idx * NUM_OPERANDS + 2],
                                                  rs3_rnid_fwd[d_idx],
                                                  i_brtag[d_idx]);

end // block: src_rn_loop
endgenerate


rnid_t w_rs1_rs2_rnid[scariv_conf_pkg::DISP_SIZE * NUM_OPERANDS];
generate for (genvar d_idx = 0; d_idx < scariv_conf_pkg::DISP_SIZE; d_idx++) begin : op_loop
  assign w_rs1_rs2_rnid[d_idx * NUM_OPERANDS + 0] = rs1_rnid_fwd[d_idx];
  assign w_rs1_rs2_rnid[d_idx * NUM_OPERANDS + 1] = rs2_rnid_fwd[d_idx];
  if (NUM_OPERANDS >= 3) begin
    assign w_rs1_rs2_rnid[d_idx * NUM_OPERANDS + 2] = rs3_rnid_fwd[d_idx];
  end
end
endgenerate

scariv_inflight_list
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
grp_id_t w_is_br_inst;
generate for (genvar d_idx = 0; d_idx < scariv_conf_pkg::DISP_SIZE; d_idx++) begin : br_loop
  assign w_is_br_inst[d_idx] = i_ibuf_front_fire &
                               i_ibuf_front_payload.inst[d_idx].valid &
                               (i_ibuf_front_payload.inst[d_idx].cat == decoder_inst_cat_pkg::INST_CAT_BR);
end
endgenerate


scariv_bru_rn_snapshots
u_scariv_bru_rn_snapshots
  (
   .i_clk (i_clk),
   .i_reset_n(i_reset_n),

   .i_rn_list (w_rn_list),

   .i_load ({scariv_conf_pkg::DISP_SIZE{i_ibuf_front_fire}} & w_is_br_inst),

   .i_rd_valid   (w_rd_valids),
   .i_rd_archreg (w_update_arch_id),
   .i_rd_rnid    (w_rd_rnid),
   .i_brtag      (i_brtag  ),

   .br_upd_if (br_upd_if),
   .o_rn_list (w_restore_queue_list)
   );


// Commit Map
scariv_commit_map
  #(.REG_TYPE(REG_TYPE))
u_commit_map
  (
   .i_clk (i_clk),
   .i_reset_n(i_reset_n),

   .i_commit_rnid_update(i_commit_rnid_update),
   .o_rnid_map (w_restore_commit_map_list)
   );

`ifdef SIMULATION

rnid_t w_rnid_list[RNID_SIZE];
generate for (genvar d_idx = 0; d_idx < scariv_conf_pkg::DISP_SIZE; d_idx++) begin : rn_loop
  for (genvar f_idx = 0; f_idx < scariv_pkg::FLIST_SIZE; f_idx++) begin : flist_loop
    assign w_rnid_list[d_idx * FLIST_SIZE + f_idx] = free_loop[d_idx].u_freelist.r_freelist[f_idx];
  end
end
endgenerate
generate for (genvar r_idx = 0; r_idx < 32; r_idx++) begin : rmap_loop
  assign w_rnid_list[scariv_conf_pkg::DISP_SIZE * FLIST_SIZE + r_idx] = u_scariv_rename_map.r_map[r_idx];
end
endgenerate

always_ff @ (negedge i_clk, negedge i_reset_n) begin
  if (i_reset_n) begin
    for (int f1_idx = 0; f1_idx < RNID_SIZE; f1_idx++) begin : list_check1_loop
      for (int f2_idx = 0; f2_idx < RNID_SIZE; f2_idx++) begin : list_check2_loop
        if (f1_idx != f2_idx) begin
          if (w_rnid_list[f1_idx] !='h0 && (w_rnid_list[f1_idx] == w_rnid_list[f2_idx])) begin
            $fatal(0, "Index %d(%2d, %2d) and %d(%2d, %2d) are same ID: %3d\n",
                   f1_idx[$clog2(RNID_SIZE)-1: 0], f1_idx[$clog2(RNID_SIZE)-1: 0] / scariv_pkg::FLIST_SIZE, f1_idx[$clog2(RNID_SIZE)-1: 0] % scariv_pkg::FLIST_SIZE,
                   f2_idx[$clog2(RNID_SIZE)-1: 0], f2_idx[$clog2(RNID_SIZE)-1: 0] / scariv_pkg::FLIST_SIZE, f2_idx[$clog2(RNID_SIZE)-1: 0] % scariv_pkg::FLIST_SIZE,
                   w_rnid_list[f1_idx]);
          end
        end
      end
    end
  end // if (i_reset_n)
end // always_ff @ (negedge i_clk, negedge i_reset_n)

`endif //  `ifdef SIMULATION


endmodule // scariv_rename
