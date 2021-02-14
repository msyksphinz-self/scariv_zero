module msrh_rob_entry
  (
   input logic                           i_clk,
   input logic                           i_reset_n,

   input logic [msrh_pkg::CMT_BLK_W-1:0] i_ctag,

   input logic                           i_load_valid,
   input logic [msrh_pkg::DISP_SIZE-1:0] i_load_ii,
   input logic [msrh_pkg::DISP_SIZE-1:0] i_old_rd_valid,
   input logic [msrh_pkg::RNID_W-1:0]    i_old_rd_rnid[msrh_pkg::DISP_SIZE],

   input msrh_pkg::done_rpt_t i_done_rpt [msrh_pkg::CMT_BUS_SIZE],

   output o_block_all_done
   );

logic                                    r_valid;
logic [msrh_pkg::DISP_SIZE-1:0]          r_ii;
logic [msrh_pkg::DISP_SIZE-1:0]          r_done_ii;
logic [msrh_pkg::DISP_SIZE-1:0]          r_old_rd_valid;
logic [msrh_pkg::RNID_W-1:0]             r_old_rd_rnid[msrh_pkg::DISP_SIZE];

logic [msrh_pkg::DISP_SIZE-1:0]          w_done_rpt_vld;

generate for (genvar d_idx = 0; d_idx < msrh_pkg::DISP_SIZE; d_idx++) begin : ii_loop
  logic [msrh_pkg::CMT_BUS_SIZE-1: 0] w_done_rpt_tmp_vld;
  for (genvar c_idx = 0; c_idx < msrh_pkg::CMT_BUS_SIZE; c_idx++) begin : cmt_loop
    assign w_done_rpt_tmp_vld[c_idx] = i_done_rpt[c_idx].valid &
                                       i_done_rpt[c_idx].ctag == i_ctag &&
                                       i_done_rpt[c_idx].ii == (1 << d_idx);
  end
  assign w_done_rpt_vld[d_idx] = |w_done_rpt_tmp_vld;
end
endgenerate



always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_valid <= 1'b0;
  end else begin
    if (i_load_valid) begin
      r_valid <= 1'b1;
      r_ii <= i_load_ii;
      r_done_ii <= {msrh_pkg::DISP_SIZE{1'b0}};
      for (int i = 0; i < msrh_pkg::DISP_SIZE; i++) begin
        r_old_rd_valid[i] <= i_old_rd_valid[i];
        r_old_rd_rnid [i] <= i_old_rd_rnid [i];
      end
    end else if (r_valid) begin
      if (o_block_all_done) begin
        r_valid <= 1'b0;
      end else begin
        r_done_ii <= r_done_ii | w_done_rpt_vld;
      end
    end
  end
end // always_ff @ (posedge i_clk, negedge i_reset_n)

assign o_block_all_done = r_valid & (r_ii == r_done_ii);

endmodule // msrh_rob_entry
