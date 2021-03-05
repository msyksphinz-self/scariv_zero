module msrh_rob_entry
  (
   input logic                             i_clk,
   input logic                             i_reset_n,

   input logic [msrh_pkg::CMT_BLK_W-1:0]   i_cmt_id,

   input logic                             i_load_valid,
   input logic [riscv_pkg::VADDR_W-1: 1]   i_load_pc_addr,
   input                                   msrh_pkg::disp_t[msrh_pkg::DISP_SIZE-1:0] i_load_inst,
   input logic [msrh_pkg::DISP_SIZE-1:0]   i_load_grp_id,
   input logic [msrh_pkg::DISP_SIZE-1:0]   i_old_rd_valid,
   input logic [msrh_pkg::RNID_W-1:0]      i_old_rd_rnid[msrh_pkg::DISP_SIZE],

   input                                   msrh_pkg::done_rpt_t i_done_rpt [msrh_pkg::CMT_BUS_SIZE],

   output logic                            o_block_all_done,
   output logic [msrh_pkg::DISP_SIZE-1: 0] o_block_grp_id,
   input logic                             i_commit_finish
   );

logic                             r_valid;
msrh_pkg::rob_entry_t             r_entry;

logic [msrh_pkg::DISP_SIZE-1:0]   w_done_rpt_vld;

generate for (genvar d_idx = 0; d_idx < msrh_pkg::DISP_SIZE; d_idx++) begin : grp_id_loop
  logic [msrh_pkg::CMT_BUS_SIZE-1: 0] w_done_rpt_tmp_vld;
  for (genvar c_idx = 0; c_idx < msrh_pkg::CMT_BUS_SIZE; c_idx++) begin : cmt_loop
    assign w_done_rpt_tmp_vld[c_idx] = i_done_rpt[c_idx].valid &
                                       i_done_rpt[c_idx].cmt_id == i_cmt_id &&
                                       i_done_rpt[c_idx].grp_id == (1 << d_idx);
  end
  assign w_done_rpt_vld[d_idx] = |w_done_rpt_tmp_vld;
end
endgenerate



always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_valid <= 1'b0;
    r_entry <= 'h0;
  end else begin
    if (i_load_valid) begin
      r_valid <= 1'b1;
      r_entry.grp_id <= i_load_grp_id;
      r_entry.pc_addr <= i_load_pc_addr;
      r_entry.inst    <= i_load_inst;

      r_entry.done_grp_id <= {msrh_pkg::DISP_SIZE{1'b0}};
      for (int i = 0; i < msrh_pkg::DISP_SIZE; i++) begin
        r_entry.old_rd_valid[i] <= i_old_rd_valid[i];
        r_entry.old_rd_rnid [i] <= i_old_rd_rnid [i];
      end
    end else if (r_valid) begin
      if (o_block_all_done & i_commit_finish) begin
        r_valid <= 1'b0;
      end else begin
        r_entry.done_grp_id <= r_entry.done_grp_id | w_done_rpt_vld;
      end
    end
  end
end // always_ff @ (posedge i_clk, negedge i_reset_n)

assign o_block_all_done = r_valid & (r_entry.grp_id == r_entry.done_grp_id);
assign o_block_grp_id   = r_entry.grp_id;

endmodule // msrh_rob_entry
