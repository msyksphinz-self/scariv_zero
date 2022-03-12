module msrh_commit_map
  import msrh_pkg::*;
  #(parameter REG_TYPE = GPR)
(
 input logic                    i_clk,
 input logic                    i_reset_n,

 // Commit notification
 input msrh_pkg::cmt_rnid_upd_t i_commit_rnid_update,

 output msrh_pkg::rnid_t o_rnid_map[32]
 );

msrh_pkg::rnid_t         r_commit_map[32];
msrh_pkg::rnid_t         w_commit_map_next[32];
grp_id_t w_dead_id_with_except;

always_comb begin
  for (int r_idx = 0; r_idx < 32; r_idx++) begin : r_loop
    w_commit_map_next[r_idx] = r_commit_map[r_idx];
  end

  w_dead_id_with_except = (|i_commit_rnid_update.except_valid) &
                          (i_commit_rnid_update.except_type != msrh_pkg::SILENT_FLUSH) &
                          (i_commit_rnid_update.except_type != msrh_pkg::ANOTHER_FLUSH) ?
                          {i_commit_rnid_update.dead_id | i_commit_rnid_update.except_valid} : // When except and NOT silent flush, instruction itself is not valid
                          i_commit_rnid_update.dead_id;

  if (i_commit_rnid_update.commit) begin
    for (int d_idx = 0; d_idx < msrh_conf_pkg::DISP_SIZE; d_idx++) begin : d_loop
      if (i_commit_rnid_update.rnid_valid[d_idx] &
          (i_commit_rnid_update.rd_typ[d_idx] == REG_TYPE) &
          !w_dead_id_with_except[d_idx]) begin
        w_commit_map_next[i_commit_rnid_update.rd_regidx[d_idx]] = i_commit_rnid_update.rd_rnid[d_idx];
      end
    end
  end
end

generate for (genvar d_idx = 0; d_idx < 32; d_idx++) begin : reg_loop
  if (d_idx == 0) begin
    assign r_commit_map[d_idx] = 'h0;
  end else begin
    always_ff @ (posedge i_clk, negedge i_reset_n) begin
      if (!i_reset_n) begin
        r_commit_map[d_idx] <= d_idx;
      end else begin
        r_commit_map[d_idx] <= w_commit_map_next[d_idx];
      end
    end
  end

  assign o_rnid_map[d_idx] = r_commit_map[d_idx];
end
endgenerate

endmodule // msrh_commit_map
