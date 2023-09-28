// ------------------------------------------------------------------------
// NAME : scariv_alu_pipe
// TYPE : module
// ------------------------------------------------------------------------
// Arithmetic Unit
// ------------------------------------------------------------------------
// ex0: Decode instruction
// ex1: Send Early-release
// ex2: Get Forwarding data
// ex3: Write Data / Done Report
// ------------------------------------------------------------------------

module scariv_vec_alu_pipe
  import decoder_vec_ctrl_pkg::*;
#(
  parameter RV_ENTRY_SIZE = 32
  )
(
    input logic i_clk,
    input logic i_reset_n,

    // Commit notification
    input scariv_pkg::commit_blk_t i_commit,
    br_upd_if.slave              br_upd_if,

    input scariv_pkg::issue_t  i_ex0_issue,
    input scariv_pkg::phy_wr_t ex1_i_phy_wr[scariv_pkg::TGT_BUS_SIZE],

    regread_if.master ex0_regread_rs1,

    vec_regwrite_if.master vec_phy_wr_if,

    output scariv_pkg::done_rpt_t o_done_report
);

typedef struct packed {
  op_t  op;
} pipe_ctrl_t;

pipe_ctrl_t    w_ex0_pipe_ctrl;
logic          w_ex0_commit_flush;
logic          w_ex0_br_flush;
logic          w_ex0_flush;

pipe_ctrl_t         r_ex1_pipe_ctrl;
scariv_pkg::issue_t r_ex1_issue;
scariv_pkg::issue_t w_ex1_issue_next;
logic               w_ex1_commit_flush;
logic               w_ex1_br_flush;
logic               w_ex1_flush;
riscv_pkg::xlen_t r_ex1_rs1_data;

riscv_pkg::xlen_t w_ex1_rs1_selected_data;

pipe_ctrl_t         r_ex2_pipe_ctrl;
scariv_pkg::issue_t r_ex2_issue;
scariv_pkg::issue_t w_ex2_issue_next;
logic               r_ex2_wr_valid;

assign w_ex0_commit_flush = scariv_pkg::is_commit_flush_target(i_ex0_issue.cmt_id, i_ex0_issue.grp_id, i_commit);
assign w_ex0_br_flush     = scariv_pkg::is_br_flush_target(i_ex0_issue.cmt_id, i_ex0_issue.grp_id, br_upd_if.cmt_id, br_upd_if.grp_id,
                                                          br_upd_if.dead, br_upd_if.mispredict) & br_upd_if.update;
assign w_ex0_flush = w_ex0_commit_flush | w_ex0_br_flush;

// ---------------------
// EX0
// ---------------------

decoder_vec_ctrl u_pipe_ctrl (
    .inst(i_ex0_issue.inst),
    .op  (w_ex0_pipe_ctrl.op)
);

assign ex0_regread_rs1.valid = i_ex0_issue.valid & i_ex0_issue.rd_regs[0].valid;
assign ex0_regread_rs1.rnid  = i_ex0_issue.rd_regs[0].rnid;

assign w_ex0_commit_flush = scariv_pkg::is_commit_flush_target(i_ex0_issue.cmt_id, i_ex0_issue.grp_id, i_commit);
assign w_ex0_br_flush     = scariv_pkg::is_br_flush_target(i_ex0_issue.cmt_id, i_ex0_issue.grp_id, br_upd_if.cmt_id, br_upd_if.grp_id,
                                                           br_upd_if.dead, br_upd_if.mispredict) & br_upd_if.update;
assign w_ex0_flush = w_ex0_commit_flush | w_ex0_br_flush;

// ---------------------
// EX1
// ---------------------

always_comb begin
  w_ex1_issue_next = i_ex0_issue;
  w_ex1_issue_next.valid = i_ex0_issue.valid & !w_ex0_flush;
end

always_ff @(posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_ex1_issue.valid <= 1'b0;
  end else begin
    r_ex1_issue <= w_ex1_issue_next;
    r_ex1_pipe_ctrl <= w_ex0_pipe_ctrl;

    r_ex1_rs1_data <= ex0_regread_rs1.data;
  end
end


// -----------------------------
// EX2 Stage
// -----------------------------

assign w_ex1_rs1_selected_data = r_ex1_rs1_data;

logic                                      w_ex2_commit_flush;
logic                                      w_ex2_br_flush;
logic                                      w_ex2_flush;
assign w_ex2_commit_flush = scariv_pkg::is_commit_flush_target(r_ex2_issue.cmt_id, r_ex2_issue.grp_id, i_commit);
assign w_ex2_br_flush     = scariv_pkg::is_br_flush_target(r_ex2_issue.cmt_id, r_ex2_issue.grp_id, br_upd_if.cmt_id, br_upd_if.grp_id,
                                                           br_upd_if.dead, br_upd_if.mispredict) & br_upd_if.update;
assign w_ex2_flush = w_ex2_commit_flush | w_ex2_br_flush;

always_comb begin
  w_ex2_issue_next = r_ex1_issue;
  w_ex2_issue_next.valid = r_ex1_issue.valid & !w_ex1_flush;
end

always_ff @(posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_ex2_issue <= 'h0;
    r_ex2_wr_valid <= 1'b0;
  end else begin
    r_ex2_issue <= w_ex2_issue_next;
    r_ex2_wr_valid <= r_ex1_issue.wr_reg.valid;
  end // else: !if(!i_reset_n)
end // always_ff @ (posedge i_clk, negedge i_reset_n)

always_comb begin
  vec_phy_wr_if.valid   = r_ex2_wr_valid;
  vec_phy_wr_if.rd_rnid = r_ex2_issue.wr_reg.rnid;
  vec_phy_wr_if.rd_data = 'h0;

  o_done_report.valid  = r_ex2_issue.valid;
  o_done_report.cmt_id = r_ex2_issue.cmt_id;
  o_done_report.grp_id = r_ex2_issue.grp_id;
  o_done_report.fflags_update_valid = 1'b0;
  o_done_report.fflags = 'h0;
end // always_comb


`ifdef SIMULATION
// Kanata
import "DPI-C" function void log_stage
(
 input longint id,
 input string stage
);

always_ff @ (negedge i_clk, negedge i_reset_n) begin
  if (i_reset_n) begin
    if (i_ex0_issue.valid) begin
      log_stage (i_ex0_issue.kanata_id, "EX0");
    end
    if (r_ex1_issue.valid) begin
      log_stage (r_ex1_issue.kanata_id, "EX1");
    end
    if (r_ex2_issue.valid) begin
      log_stage (r_ex2_issue.kanata_id, "EX2");
    end
  end
end

`endif // SIMULATION

endmodule // scariv_vec_alu_pipe
