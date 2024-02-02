// ------------------------------------------------------------------------
// NAME : SCARIV Rename Unit
// TYPE : module
// ------------------------------------------------------------------------
// Rename Unit
// ------------------------------------------------------------------------
// SubUnit:
//  FreeList, contains free Physical ID
//  Rename Map, translate Logical Register Index -> Physical Register Index
//  Inflight List, checking Physical Index is flight or not
//  BR RN Snapshot, snapshot for Branch Instruction
//  Commit Map, snapshot for Exception
// ------------------------------------------------------------------------

module scariv_rename
  import scariv_pkg::*;
  #(parameter REG_TYPE = GPR)
(
   input logic i_clk,
   input logic i_reset_n,

   scariv_front_if.slave      ibuf_front_if,
   input scariv_pkg::cmt_id_t i_sc_new_cmt_id,

   input scariv_pkg::phy_wr_t i_phy_wr[scariv_pkg::TGT_BUS_SIZE],
   scariv_front_if.master     rn_front_if,

   phy_wr_if.slave phy_wr_if[scariv_pkg::TGT_BUS_SIZE],
   vec_phy_fwd_if.slave       vec_phy_fwd_if[3],
   scariv_front_if.master           rn_front_if,

   // from Resource Allocator
   input brtag_t i_brtag  [scariv_conf_pkg::DISP_SIZE],
   input logic            i_resource_ok,

   // Branch Tag Update Signal
   br_upd_if.slave        br_upd_if,

   vlmul_upd_if.slave         vlmul_upd_if,

   // Committer Rename ID update
   commit_if.monitor   commit_if,
   input scariv_pkg::cmt_rnid_upd_t commit_if_rnid_update
   );

logic [ 2: 0] w_freelist_ready;
logic         w_ibuf_front_fire;

logic         w_commit_flush;
logic         w_br_flush;
logic         w_flush_valid;

disp_t [scariv_conf_pkg::DISP_SIZE-1:0] w_ibuf_ipr_disp_inst;
disp_t [scariv_conf_pkg::DISP_SIZE-1:0] w_ibuf_fpr_disp_inst;
disp_t [scariv_conf_pkg::DISP_SIZE-1:0] w_ibuf_vpr_disp_inst;
disp_t [scariv_conf_pkg::DISP_SIZE-1:0] w_ibuf_merge_disp_inst;
disp_t [scariv_conf_pkg::DISP_SIZE-1:0] r_disp_inst;

vlmul_upd_if w_dummy_vlmul_upd_if;
assign w_dummy_vlmul_upd_if.valid = 1'b0;
assign ibuf_front_if.ready = !(commit_if_rnid_update.commit & (|commit_if.payload.except_valid)) &
                             i_resource_ok & &w_freelist_ready;

assign w_ibuf_front_fire = ~w_flush_valid & ibuf_front_if.valid & ibuf_front_if.ready;
assign w_commit_flush = commit_if.is_flushed_commit();
assign w_br_flush     = br_upd_if.update & ~br_upd_if.dead & br_upd_if.mispredict;
assign w_flush_valid  = w_commit_flush | w_br_flush;


rnid_update_t w_xpr_update_phy[scariv_pkg::TGT_BUS_SIZE];
for (genvar t_idx = 0; t_idx < scariv_pkg::TGT_BUS_SIZE; t_idx++) begin : target_loop
  assign w_xpr_update_phy[t_idx].valid = i_phy_wr[t_idx].valid & (i_phy_wr[t_idx].rd_type == scariv_pkg::GPR);
  assign w_xpr_update_phy[t_idx].rnid  = i_phy_wr[t_idx].rd_rnid;
end

scariv_rename_sub
  #(.REG_TYPE (GPR),
    .TARGET_SIZE (scariv_pkg::TGT_BUS_SIZE)
    )
u_ipr_rename
  (
   .i_clk     (i_clk    ),
   .i_reset_n (i_reset_n),

   // Change VLMUL size
   .vlmul_upd_if (w_dummy_vlmul_upd_if),

   .o_freelist_ready (w_freelist_ready[0]),

   .i_ibuf_front_fire    (w_ibuf_front_fire),
   .i_ibuf_front_payload (ibuf_front_if.payload),

   .phy_wr_if  (phy_wr_if),
   .i_brtag   (i_brtag),
   .br_upd_if (br_upd_if),

   .o_disp_inst (w_ibuf_ipr_disp_inst),

   .commit_if             (commit_if            ),
   .commit_if_rnid_update (commit_if_rnid_update)
   );

generate if (riscv_fpu_pkg::FLEN_W != 0) begin : fpr

  rnid_update_t w_fpr_update_phy[scariv_pkg::TGT_BUS_SIZE];
  for (genvar t_idx = 0; t_idx < scariv_pkg::TGT_BUS_SIZE; t_idx++) begin : target_loop
    assign w_fpr_update_phy[t_idx].valid = i_phy_wr[t_idx].valid & (i_phy_wr[t_idx].rd_type == scariv_pkg::FPR);
    assign w_fpr_update_phy[t_idx].rnid  = i_phy_wr[t_idx].rd_rnid;
  end

  scariv_rename_sub
    #(.REG_TYPE (scariv_pkg::FPR),
      .TARGET_SIZE (scariv_pkg::TGT_BUS_SIZE)
      )
  u_fpr_rename
    (
     .i_clk     (i_clk    ),
     .i_reset_n (i_reset_n),

     // Change VLMUL size
     .vlmul_upd_if (w_dummy_vlmul_upd_if),

     .o_freelist_ready (w_freelist_ready[1]),

     .i_ibuf_front_fire    (w_ibuf_front_fire),
     .i_ibuf_front_payload (ibuf_front_if.payload),

     .phy_wr_if  (phy_wr_if),
     .i_brtag   (i_brtag),
     .br_upd_if (br_upd_if),

     .o_disp_inst (w_ibuf_fpr_disp_inst),

     .commit_if             (commit_if            ),
     .commit_if_rnid_update (commit_if_rnid_update)
     );

end else begin // block: fpu
  assign w_freelist_ready[1] = 1'b1;
  for (genvar d_idx = 0; d_idx < scariv_conf_pkg::DISP_SIZE; d_idx++) begin : disp_loop
    assign w_ibuf_fpr_disp_inst[d_idx]  = 'h0;
  end
end endgenerate


generate if (scariv_vec_pkg::VLEN_W != 0) begin : vpr

  rnid_update_t w_vpr_update_phy[3];
  for (genvar t_idx = 0; t_idx < 3; t_idx++) begin : target_loop
    assign w_vpr_update_phy[t_idx].valid = vec_phy_fwd_if[t_idx].valid;
    assign w_vpr_update_phy[t_idx].rnid  = vec_phy_fwd_if[t_idx].rd_rnid;
  end

  scariv_rename_sub
    #(.REG_TYPE (scariv_pkg::VPR),
      .TARGET_SIZE (3))
  u_vpr_rename
    (
     .i_clk     (i_clk    ),
     .i_reset_n (i_reset_n),

     // Change VLMUL size
     .vlmul_upd_if (vlmul_upd_if),

     .o_freelist_ready (w_freelist_ready[2]),

     .i_ibuf_front_fire    (w_ibuf_front_fire),
     .i_ibuf_front_payload (ibuf_front_if.payload),

     .i_update_phy (w_vpr_update_phy),
     .i_brtag      (i_brtag),
     .br_upd_if    (br_upd_if),

     .o_disp_inst (w_ibuf_vpr_disp_inst),

     .commit_if             (commit_if            ),
     .commit_if_rnid_update (commit_if_rnid_update)
     );

end else begin // block: vpr
  assign w_freelist_ready[2] = 1'b1;
  for (genvar d_idx = 0; d_idx < scariv_conf_pkg::DISP_SIZE; d_idx++) begin : disp_loop
    assign w_ibuf_vpr_disp_inst[d_idx]  = 'h0;
  end
end endgenerate

// Merge dispatched instruction
generate for (genvar d_idx = 0; d_idx < scariv_conf_pkg::DISP_SIZE; d_idx++) begin : disp_loop
  assign w_ibuf_merge_disp_inst[d_idx]  = merge_scariv_front_if (w_ibuf_ipr_disp_inst[d_idx],
                                                                 w_ibuf_fpr_disp_inst[d_idx],
                                                                 w_ibuf_vpr_disp_inst[d_idx]);
end endgenerate

always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    rn_front_if.valid <= 'h0;
    rn_front_if.payload.pc_addr <= 'h0;
    rn_front_if.payload.is_br_included <= 1'b0;

    r_disp_inst <= 'h0;
  end else begin
    rn_front_if.valid                    <= w_ibuf_front_fire;
    rn_front_if.payload.pc_addr          <= ibuf_front_if.payload.pc_addr;
    rn_front_if.payload.is_br_included   <= ibuf_front_if.payload.is_br_included;
`ifdef SIMULATION
    rn_front_if.payload.pc_addr_debug    <= {ibuf_front_if.payload.pc_addr, 1'b0};
`endif // SIMULATION
    rn_front_if.payload.tlb_except_valid <= ibuf_front_if.payload.tlb_except_valid;
    rn_front_if.payload.tlb_except_cause <= ibuf_front_if.payload.tlb_except_cause;
    rn_front_if.payload.tlb_except_tval  <= ibuf_front_if.payload.tlb_except_tval;
    rn_front_if.payload.resource_cnt     <= ibuf_front_if.payload.resource_cnt;
    rn_front_if.payload.basicblk_pc_vaddr<= ibuf_front_if.payload.basicblk_pc_vaddr;

    rn_front_if.payload.int_inserted <= ibuf_front_if.payload.int_inserted;
    r_disp_inst <= w_ibuf_merge_disp_inst;
  end // else: !if(!i_reset_n)
end // always_ff @ (posedge i_clk, negedge i_reset_n)

assign rn_front_if.payload.cmt_id = i_sc_new_cmt_id;
always_comb begin
  rn_front_if.payload.inst = r_disp_inst;
end


`ifdef SIMULATION
function void dump_json(string name, int fp);
  $fwrite(fp, "  \"scariv_%s_rename\" : {\n", name);

  if (rn_front_if.valid) begin
    $fwrite(fp, "    \"rn_front_if\" : {\n");
    $fwrite(fp, "      valid  : \"%d\",\n", rn_front_if.valid);
    $fwrite(fp, "      ready  : \"%d\",\n", rn_front_if.ready);
    $fwrite(fp, "      cmt_id  : \"%d\",\n", rn_front_if.payload.cmt_id);
    $fwrite(fp, "      pc_addr : \"0x%08x\",\n", rn_front_if.payload.pc_addr);

    for (int d_idx = 0; d_idx < scariv_conf_pkg::DISP_SIZE; d_idx++) begin : disp_loop
      $fwrite(fp, "      \"inst[%d]\" : {", d_idx);
      $fwrite(fp, "        valid : \"%d\",",      rn_front_if.payload.inst[d_idx].valid);
      $fwrite(fp, "        inst  : \"%08x\",",     rn_front_if.payload.inst[d_idx].inst);
      $fwrite(fp, "        pc_addr : \"%0x\",",   rn_front_if.payload.inst[d_idx].pc_addr);

      $fwrite(fp, "        rd_valid   : \"%d\",", rn_front_if.payload.inst[d_idx].wr_reg.valid);
      $fwrite(fp, "        rd_type    : \"%d\",", rn_front_if.payload.inst[d_idx].wr_reg.typ);
      $fwrite(fp, "        rd_regidx  : \"%d\",", rn_front_if.payload.inst[d_idx].wr_reg.regidx);
      $fwrite(fp, "        rd_rnid    : \"%d\",", rn_front_if.payload.inst[d_idx].wr_reg.rnid);

      $fwrite(fp, "        rs1_valid  : \"%d\",", rn_front_if.payload.inst[d_idx].rd_regs[0].valid);
      $fwrite(fp, "        rs1_type   : \"%d\",", rn_front_if.payload.inst[d_idx].rd_regs[0].typ);
      $fwrite(fp, "        rs1_regidx : \"%d\",", rn_front_if.payload.inst[d_idx].rd_regs[0].regidx);
      $fwrite(fp, "        rs1_rnid   : \"%d\",", rn_front_if.payload.inst[d_idx].rd_regs[0].rnid);
      $fwrite(fp, "        rs1_ready  : \"%d\",", rn_front_if.payload.inst[d_idx].rd_regs[0].ready);

      $fwrite(fp, "        rs2_valid  : \"%d\",", rn_front_if.payload.inst[d_idx].rd_regs[1].valid);
      $fwrite(fp, "        rs2_type   : \"%d\",", rn_front_if.payload.inst[d_idx].rd_regs[1].typ);
      $fwrite(fp, "        rs2_regidx : \"%d\",", rn_front_if.payload.inst[d_idx].rd_regs[1].regidx);
      $fwrite(fp, "        rs2_rnid   : \"%d\",", rn_front_if.payload.inst[d_idx].rd_regs[1].rnid);
      $fwrite(fp, "        rs2_ready  : \"%d\",", rn_front_if.payload.inst[d_idx].rd_regs[1].ready);

      // if (NUM_OPERANDS >= 3) begin
      $fwrite(fp, "        rs3_valid  : \"%d\",", rn_front_if.payload.inst[d_idx].rd_regs[2].valid);
      $fwrite(fp, "        rs3_type   : \"%d\",", rn_front_if.payload.inst[d_idx].rd_regs[2].typ);
      $fwrite(fp, "        rs3_regidx : \"%d\",", rn_front_if.payload.inst[d_idx].rd_regs[2].regidx);
      $fwrite(fp, "        rs3_rnid   : \"%d\",", rn_front_if.payload.inst[d_idx].rd_regs[2].rnid);
      $fwrite(fp, "        rs3_ready  : \"%d\",", rn_front_if.payload.inst[d_idx].rd_regs[2].ready);
      // end

      $fwrite(fp, "        cat[d_idx] : \"%d\",", rn_front_if.payload.inst[d_idx].cat);
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
  end // if (rn_front_if.valid & rn_front_if.ready)
  $fwrite(fp, "  },\n");

endfunction // dump

// Kanata
import "DPI-C" function void log_stage
(
 input longint id,
 input string stage
);

always_ff @ (negedge i_clk, negedge i_reset_n) begin
  if (i_reset_n) begin
    if (rn_front_if.valid & rn_front_if.ready) begin
      for (int i = 0; i < scariv_conf_pkg::DISP_SIZE; i++) begin
        if (rn_front_if.payload.inst[i].valid) begin
          log_stage (rn_front_if.payload.inst[i].kanata_id, "Rn");
        end
      end
    end
  end
end


`endif // SIMULATION

endmodule // scariv_rename
