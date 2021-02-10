module mrh_alu_pipe
  (
   input logic                           i_clk,
   input logic                           i_reset_n,

   input mrh_pkg::issue_t rv0_issue,

   input mrh_pkg::target_t         target_in [mrh_pkg::TGT_BUS_SIZE],

   output mrh_pkg::release_t       ex1_release_out,
   output mrh_pkg::target_t        ex3_target_out
   );

typedef struct packed {
logic [2: 0]   op;
logic          imm;
logic          size;
logic          sign;
} pipe_ctrl_t;

mrh_pkg::issue_t    r_ex0_issue;
pipe_ctrl_t         w_ex0_pipe_ctrl;

pipe_ctrl_t         r_ex1_pipe_ctrl;
mrh_pkg::issue_t    r_ex1_issue;


always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_ex0_issue <= 'h0;
  end else begin
    r_ex0_issue <= rv0_issue;
  end
end

decoder_inst_ctrl u_pipe_ctrl
  (
   .inst (r_ex0_issue.inst),
   .op   (w_ex0_pipe_ctrl.op  ),
   .imm  (w_ex0_pipe_ctrl.imm ),
   .size (w_ex0_pipe_ctrl.size),
   .sign (w_ex0_pipe_ctrl.sign)
   );

always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_ex1_issue     <= 'h0;
    r_ex1_pipe_ctrl <= 'h0;
  end else begin
    r_ex1_issue     <= r_ex0_issue;
    r_ex1_pipe_ctrl <= w_ex0_pipe_ctrl;
  end
end


generate for (genvar rs_idx = 0; rs_idx < mrh_pkg::REL_BUS_SIZE; rs_idx++) begin : rs_rel_loop
  // assign w_rs1_rel_fwd_valid[i] = r_entry.rs1_valid & release_in[rs_idx].rd_valid &
  //                                 (r_entry.rs1_type == release_in[rs_idx].rd_type) &
  //                                 (r_entry.rs1_rnid == release_in[rs_idx].rd_rnid));
  //
  // assign w_rs2_rel_fwd_valid[i] = r_entry.rs2_valid & release_in[rs_idx].rd_valid &
  //                                 (r_entry.rs2_type == release_in[rs_idx].rd_type) &
  //                                 (r_entry.rs2_rnid == release_in[rs_idx].rd_rnid));
end
endgenerate


endmodule // mrh_alu_pipe
