module msrh_rob_entry
  import msrh_pkg::*;
  (
   input logic                                i_clk,
   input logic                                i_reset_n,

   input logic [CMT_ENTRY_W-1:0]              i_cmt_id,

   input logic                                i_load_valid,
   input logic [riscv_pkg::VADDR_W-1: 1]      i_load_pc_addr,
   input disp_t[msrh_conf_pkg::DISP_SIZE-1:0] i_load_inst,
   input logic [msrh_conf_pkg::DISP_SIZE-1:0] i_load_grp_id,
   input logic                                i_load_br_included,
   input logic [msrh_conf_pkg::DISP_SIZE-1:0] i_load_tlb_except_valid,
   input msrh_pkg::except_t                   i_load_tlb_except_cause[msrh_conf_pkg::DISP_SIZE],

   input                                      done_rpt_t i_done_rpt [CMT_BUS_SIZE],

   output                                     rob_entry_t o_entry,
   output logic                               o_block_all_done,
   input logic                                i_commit_finish,

   input logic                                i_kill,

   br_upd_if.slave                            br_upd_if
   );

rob_entry_t             r_entry;
rob_entry_t             w_entry_next;

logic [msrh_conf_pkg::DISP_SIZE-1:0]   w_done_rpt_valid;
logic [msrh_conf_pkg::DISP_SIZE-1:0]   w_finished_grp_id;
logic [msrh_conf_pkg::DISP_SIZE-1:0]   w_done_rpt_except_valid;
except_t                               w_done_rpt_except_type[msrh_conf_pkg::DISP_SIZE];
logic [riscv_pkg::XLEN_W-1: 0]         w_done_rpt_except_tval[msrh_conf_pkg::DISP_SIZE];

generate for (genvar d_idx = 0; d_idx < msrh_conf_pkg::DISP_SIZE; d_idx++) begin : grp_id_loop
  logic [CMT_BUS_SIZE-1: 0] w_done_rpt_tmp_valid;
  done_rpt_t                w_done_rpt_selected;
  for (genvar c_idx = 0; c_idx < CMT_BUS_SIZE; c_idx++) begin : cmt_loop
    assign w_done_rpt_tmp_valid[c_idx] = i_done_rpt[c_idx].valid &
                                         i_done_rpt[c_idx].cmt_id[CMT_ENTRY_W-1:0] == i_cmt_id &&
                                         i_done_rpt[c_idx].grp_id == (1 << d_idx);
  end
  assign w_done_rpt_valid[d_idx] = |w_done_rpt_tmp_valid;
  bit_oh_or #(.T(done_rpt_t), .WORDS(CMT_BUS_SIZE))
  sel_done_rpt (.i_oh(w_done_rpt_tmp_valid),
                .i_data(i_done_rpt),
                .o_selected(w_done_rpt_selected));
  assign w_done_rpt_except_valid[d_idx] = w_done_rpt_selected.except_valid;
  assign w_done_rpt_except_type [d_idx] = w_done_rpt_selected.except_type;
  assign w_done_rpt_except_tval [d_idx] = w_done_rpt_selected.except_tval;
end
endgenerate

`ifdef SIMULATION
logic [riscv_pkg::XLEN_W-1:0]   r_mstatus[msrh_conf_pkg::DISP_SIZE];
`endif // SIMULATION


always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_entry <= 'h0;
  end else begin
    r_entry <= w_entry_next;

`ifdef SIMULATION
    for (int d_idx = 0; d_idx < msrh_conf_pkg::DISP_SIZE; d_idx++) begin
      if (w_entry_next.done_grp_id[d_idx] & ~r_entry.done_grp_id[d_idx]) begin
        r_mstatus[d_idx] <= u_msrh_tile_wrapper.u_msrh_tile.u_msrh_csu.u_msrh_csr.w_mstatus_next;
      end
    end
`endif // SIMULATION
  end
end

assign w_finished_grp_id = (r_entry.done_grp_id | r_entry.dead) & r_entry.grp_id;

always_comb begin
  w_entry_next = r_entry;

  if (i_load_valid) begin
    w_entry_next.valid = 1'b1;
    w_entry_next.dead  = {msrh_conf_pkg::DISP_SIZE{i_kill}};
    w_entry_next.grp_id = i_load_grp_id;
    w_entry_next.pc_addr = i_load_pc_addr;
    w_entry_next.inst    = i_load_inst;
    w_entry_next.br_upd_info = 'h0;


    w_entry_next.is_br_included = i_load_br_included;

    for (int d_idx = 0; d_idx < msrh_conf_pkg::DISP_SIZE; d_idx++) begin : disp_loop
      // If TLB Exception detected before execution, this instruction already done.
      w_entry_next.done_grp_id [d_idx] = (i_load_tlb_except_valid[d_idx] | i_load_inst[d_idx].illegal_valid) ? i_load_grp_id[d_idx] : 1'b0;
      w_entry_next.except_valid[d_idx] = (i_load_tlb_except_valid[d_idx] | i_load_inst[d_idx].illegal_valid);
      w_entry_next.except_type [d_idx] = i_load_tlb_except_valid[d_idx] ? i_load_tlb_except_cause[d_idx] : ILLEGAL_INST;
    end

    if (br_upd_if.update & ~br_upd_if.dead & br_upd_if.mispredict) begin
      for (int d_idx = 0; d_idx < msrh_conf_pkg::DISP_SIZE; d_idx++) begin : disp_loop
        if (is_br_flush_target (i_load_inst[d_idx].br_mask, br_upd_if.brtag)) begin
          w_entry_next.done_grp_id[d_idx] = 1'b1;
          w_entry_next.dead[d_idx] = 1'b1;
        end
      end
      if (br_upd_if.cmt_id[CMT_ENTRY_W-1:0] == i_cmt_id) begin
        w_entry_next.br_upd_info.upd_valid   [encoder_grp_id(br_upd_if.grp_id)] = 1'b1;
        w_entry_next.br_upd_info.upd_br_vaddr[encoder_grp_id(br_upd_if.grp_id)] = br_upd_if.vaddr;
      end
    end
  end // if (i_load_valid)

  if (r_entry.valid) begin
    // Condition :
    // all instruction done, or ROB entry dead,
    // So, during killing, allocated new instruction should be killed.
    if (i_commit_finish & o_block_all_done) begin
      w_entry_next.valid = 1'b0;
    end else begin
      w_entry_next.done_grp_id = r_entry.done_grp_id | w_done_rpt_valid;
      for(int d = 0; d < msrh_conf_pkg::DISP_SIZE; d++) begin
        w_entry_next.except_valid[d] = w_done_rpt_valid[d] ? w_done_rpt_except_valid[d] : r_entry.except_valid[d];
        w_entry_next.except_type [d] = w_done_rpt_valid[d] ? w_done_rpt_except_type [d] : r_entry.except_type [d];
        w_entry_next.except_tval [d] = w_done_rpt_valid[d] ? w_done_rpt_except_tval [d] : r_entry.except_tval [d];
      end
    end

    w_entry_next.dead = r_entry.dead | {msrh_conf_pkg::DISP_SIZE{i_kill}};

    // Branch condition update
    if (br_upd_if.update & ~br_upd_if.dead & br_upd_if.mispredict) begin
      for (int d_idx = 0; d_idx < msrh_conf_pkg::DISP_SIZE; d_idx++) begin : disp_loop
        if (r_entry.inst[d_idx].valid &
            is_br_flush_target (r_entry.inst[d_idx].br_mask, br_upd_if.brtag)) begin
          w_entry_next.done_grp_id[d_idx] = 1'b1;
          w_entry_next.dead[d_idx] = 1'b1;
        end
      end
      if (br_upd_if.cmt_id[CMT_ENTRY_W-1:0] == i_cmt_id) begin
        w_entry_next.br_upd_info.upd_valid   [encoder_grp_id(br_upd_if.grp_id)] = 1'b1;
        w_entry_next.br_upd_info.upd_br_vaddr[encoder_grp_id(br_upd_if.grp_id)] = br_upd_if.vaddr;
      end
    end
  end
end // always_comb


assign o_entry = r_entry;
assign o_block_all_done = r_entry.valid & (w_finished_grp_id == r_entry.grp_id);

endmodule // msrh_rob_entry
