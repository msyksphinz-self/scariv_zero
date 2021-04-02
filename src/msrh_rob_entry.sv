module msrh_rob_entry
  import msrh_pkg::*;
  (
   input logic                                i_clk,
   input logic                                i_reset_n,

   input logic [CMT_BLK_W-1:0]                i_cmt_id,

   input logic                                i_load_valid,
   input logic [riscv_pkg::VADDR_W-1: 1]      i_load_pc_addr,
   input                                      disp_t[msrh_conf_pkg::DISP_SIZE-1:0] i_load_inst,
   input logic [msrh_conf_pkg::DISP_SIZE-1:0] i_load_grp_id,
   input logic                                i_load_br_included,

   input                                      done_rpt_t i_done_rpt [CMT_BUS_SIZE],


   output                                     rob_entry_t o_entry,
   output logic                               o_block_all_done,
   input logic                                i_commit_finish,

                                              br_upd_if.slave br_upd_if
   );

rob_entry_t             r_entry;

logic [msrh_conf_pkg::DISP_SIZE-1:0]   w_done_rpt_valid;
logic [msrh_conf_pkg::DISP_SIZE-1:0]   w_done_rpt_except_valid;
except_t                                w_done_rpt_except_type[msrh_conf_pkg::DISP_SIZE];

generate for (genvar d_idx = 0; d_idx < msrh_conf_pkg::DISP_SIZE; d_idx++) begin : grp_id_loop
  logic [CMT_BUS_SIZE-1: 0] w_done_rpt_tmp_valid;
  done_rpt_t                w_done_rpt_selected;
  for (genvar c_idx = 0; c_idx < CMT_BUS_SIZE; c_idx++) begin : cmt_loop
    assign w_done_rpt_tmp_valid[c_idx] = i_done_rpt[c_idx].valid &
                                       i_done_rpt[c_idx].cmt_id == i_cmt_id &&
                                       i_done_rpt[c_idx].grp_id == (1 << d_idx);
  end
  assign w_done_rpt_valid[d_idx] = |w_done_rpt_tmp_valid;
  bit_oh_or #(.T(done_rpt_t), .WORDS(CMT_BUS_SIZE))
  sel_done_rpt (.i_oh(w_done_rpt_tmp_valid),
                .i_data(i_done_rpt),
                .o_selected(w_done_rpt_selected));
  assign w_done_rpt_except_valid[d_idx] = w_done_rpt_selected.exc_valid;
  assign w_done_rpt_except_type [d_idx] = w_done_rpt_selected.exc_type;
end
endgenerate



always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_entry <= 'h0;
  end else begin
    if (i_load_valid) begin
      r_entry.valid <= 1'b1;
      r_entry.grp_id <= i_load_grp_id;
      r_entry.pc_addr <= i_load_pc_addr;
      r_entry.inst    <= i_load_inst;

      r_entry.done_grp_id <= {msrh_conf_pkg::DISP_SIZE{1'b0}};

      r_entry.is_br_included <= i_load_br_included;
    end else if (r_entry.valid) begin
      if (o_block_all_done & i_commit_finish) begin
        r_entry.valid <= 1'b0;
      end else begin
        r_entry.done_grp_id <= r_entry.done_grp_id | w_done_rpt_valid;
        for(int d = 0; d < msrh_conf_pkg::DISP_SIZE; d++) begin
          r_entry.except_valid[d] <= w_done_rpt_valid[d] ? w_done_rpt_except_valid[d] : r_entry.except_valid[d];
          r_entry.except_type [d] <= w_done_rpt_valid[d] ? w_done_rpt_except_type [d] : r_entry.except_type [d];
        end
      end

      // Branch condition update
      if (br_upd_if.update & (br_upd_if.cmt_id == i_cmt_id)) begin
        r_entry.br_upd_info.upd_valid   [encoder_grp_id(br_upd_if.grp_id)] <= 1'b1;
        r_entry.br_upd_info.upd_br_vaddr[encoder_grp_id(br_upd_if.grp_id)] <= br_upd_if.vaddr;
      end
    end
  end
end // always_ff @ (posedge i_clk, negedge i_reset_n)

assign o_entry = r_entry;
assign o_block_all_done = r_entry.valid & (r_entry.grp_id == r_entry.done_grp_id);

endmodule // msrh_rob_entry
