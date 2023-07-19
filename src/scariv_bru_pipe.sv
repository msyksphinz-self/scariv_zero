// ------------------------------------------------------------------------
// NAME : scariv_bootrom
// TYPE : module
// ------------------------------------------------------------------------
// Branch Unit Pipeline
// ------------------------------------------------------------------------
// ex0: Decode instruction
// ex1: Send Early-release
// ex2: Get Forwarding data
// ex3: Send Branch Result
// ------------------------------------------------------------------------

module scariv_bru_pipe
  import decoder_bru_ctrl_pkg::*;
#(
  parameter RV_ENTRY_SIZE = 32
  )
(
  input logic                       i_clk,
  input logic                       i_reset_n,

  input                             scariv_pkg::issue_t rv0_issue,
  input logic [RV_ENTRY_SIZE-1:0]   rv0_index,
  input                             scariv_pkg::phy_wr_t ex1_i_phy_wr[scariv_pkg::TGT_BUS_SIZE],

  // Commit notification
  input scariv_pkg::commit_blk_t      i_commit,

  input scariv_pkg::mispred_t         i_mispred_lsu[scariv_conf_pkg::LSU_INST_NUM],

 regread_if.master ex1_regread_rs1,
 regread_if.master ex1_regread_rs2,

  output                            scariv_pkg::early_wr_t o_ex1_early_wr,
  output                            scariv_pkg::phy_wr_t o_ex3_phy_wr,

  output scariv_pkg::done_rpt_t     o_done_report,
  br_upd_if.master                  ex3_br_upd_if
);

typedef struct packed {
  op_t  op;
  logic is_cond;
  imm_t imm;
  logic wr_rd;
} pipe_ctrl_t;

logic   w_commit_flushed;

scariv_pkg::issue_t                        r_ex0_issue;
logic [RV_ENTRY_SIZE-1: 0] w_ex0_index;
pipe_ctrl_t                              w_ex0_pipe_ctrl;
logic                      w_ex0_br_flush;

pipe_ctrl_t                              r_ex1_pipe_ctrl;
scariv_pkg::issue_t                        r_ex1_issue;
scariv_pkg::issue_t                        w_ex1_issue_next;
logic [RV_ENTRY_SIZE-1: 0] r_ex1_index;
logic                      w_ex1_br_flush;
logic                      r_ex1_dead;

logic [scariv_pkg::TGT_BUS_SIZE-1:0] w_ex1_rs_fwd_valid[2];
riscv_pkg::xlen_t                    w_ex1_rs_fwd_data [2];

logic [scariv_pkg::TGT_BUS_SIZE-1:0] w_ex2_rs1_fwd_valid;
logic [scariv_pkg::TGT_BUS_SIZE-1:0] w_ex2_rs2_fwd_valid;
riscv_pkg::xlen_t w_ex2_tgt_data          [scariv_pkg::TGT_BUS_SIZE];
riscv_pkg::xlen_t w_ex2_rs1_fwd_data;
riscv_pkg::xlen_t w_ex2_rs2_fwd_data;

riscv_pkg::xlen_t w_ex2_rs1_selected_data;
riscv_pkg::xlen_t w_ex2_rs2_selected_data;

logic                                    w_ex2_rs1_pred_hit;
logic                                    w_ex2_rs2_pred_hit;

logic                                    w_ex1_rs1_lsu_mispred;
logic                                    w_ex1_rs2_lsu_mispred;
logic                                    w_ex1_rs1_mispred;
logic                                    w_ex1_rs2_mispred;

pipe_ctrl_t                              r_ex2_pipe_ctrl;
scariv_pkg::issue_t                        r_ex2_issue;
scariv_pkg::issue_t                        w_ex2_issue_next;
logic [RV_ENTRY_SIZE-1: 0]               r_ex2_index;
riscv_pkg::xlen_t            r_ex2_rs1_data;
riscv_pkg::xlen_t            r_ex2_rs2_data;
scariv_pkg::vaddr_t          w_ex2_br_vaddr;
logic                                    r_ex2_wr_valid;
logic                                    w_ex2_br_flush;
logic                                    r_ex2_dead;

scariv_pkg::issue_t                        r_ex3_issue;
scariv_pkg::issue_t                        w_ex3_issue_next;
pipe_ctrl_t                              r_ex3_pipe_ctrl;
logic                                    r_ex3_result;
logic [RV_ENTRY_SIZE-1: 0]               r_ex3_index;
scariv_pkg::vaddr_t          r_ex3_br_vaddr;
logic                                    r_ex3_rs1_pred_hit;
logic                                    r_ex3_rs2_pred_hit;
logic                                    r_ex3_dead;

always_comb begin
  r_ex0_issue = rv0_issue;
  w_ex0_index = rv0_index;
end

decoder_bru_ctrl u_pipe_ctrl (
  .inst    (r_ex0_issue.inst       ),
  .op      (w_ex0_pipe_ctrl.op     ),
  .is_cond (w_ex0_pipe_ctrl.is_cond),
  .imm     (w_ex0_pipe_ctrl.imm    ),
  .wr_rd   (w_ex0_pipe_ctrl.wr_rd  )
);

assign ex1_regread_rs1.valid = r_ex1_issue.valid & r_ex1_issue.rd_regs[0].valid;
assign ex1_regread_rs1.rnid  = r_ex1_issue.rd_regs[0].rnid;

assign ex1_regread_rs2.valid = r_ex1_issue.valid & r_ex1_issue.rd_regs[1].valid;
assign ex1_regread_rs2.rnid  = r_ex1_issue.rd_regs[1].rnid;

generate for (genvar rs_idx = 0; rs_idx < 2; rs_idx++) begin : ex1_rs_loop
  riscv_pkg::xlen_t w_ex1_tgt_data [scariv_pkg::TGT_BUS_SIZE];
  for (genvar tgt_idx = 0; tgt_idx < scariv_pkg::TGT_BUS_SIZE; tgt_idx++) begin : rs_tgt_loop
    assign w_ex1_rs_fwd_valid[rs_idx][tgt_idx] = r_ex1_issue.rd_regs[rs_idx].valid & ex1_i_phy_wr[tgt_idx].valid &
                                                (r_ex1_issue.rd_regs[rs_idx].typ  == ex1_i_phy_wr[tgt_idx].rd_type) &
                                                (r_ex1_issue.rd_regs[rs_idx].rnid == ex1_i_phy_wr[tgt_idx].rd_rnid) &
                                                (r_ex1_issue.rd_regs[rs_idx].rnid != 'h0);   // GPR[x0] always zero
    assign w_ex1_tgt_data[tgt_idx] = ex1_i_phy_wr[tgt_idx].rd_data;
  end
    bit_oh_or #(
      .T(riscv_pkg::xlen_t),
      .WORDS(scariv_pkg::TGT_BUS_SIZE)
  ) u_rs_data_select (
      .i_oh      (w_ex1_rs_fwd_valid[rs_idx]),
      .i_data    (w_ex1_tgt_data            ),
      .o_selected(w_ex1_rs_fwd_data [rs_idx])
  );
end endgenerate



// EX0 brtag flush check
assign w_ex0_br_flush  = scariv_pkg::is_br_flush_target(r_ex0_issue.cmt_id, ex3_br_upd_if.grp_id, ex3_br_upd_if.cmt_id, ex3_br_upd_if.grp_id,
                                                        ex3_br_upd_if.dead, ex3_br_upd_if.mispredict) & ex3_br_upd_if.update & r_ex0_issue.valid;

always_comb begin
  w_ex1_issue_next = r_ex0_issue;
end

always_ff @(posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_ex1_issue <= 'h0;
    r_ex1_index <= 'h0;
    r_ex1_pipe_ctrl <= 'h0;
    r_ex1_dead <= 1'b0;
  end else begin
    r_ex1_issue <= r_ex0_issue;
    r_ex1_index <= w_ex0_index;
    r_ex1_pipe_ctrl <= w_ex0_pipe_ctrl;
    r_ex1_dead <= r_ex0_issue.valid & (w_ex0_br_flush | w_commit_flushed);
  end
end

select_mispred_bus rs1_mispred_select
(
 .i_entry_rnid (r_ex1_issue.rd_regs[0].rnid),
 .i_entry_type (r_ex1_issue.rd_regs[0].typ),
 .i_mispred    (i_mispred_lsu),

 .o_mispred    (w_ex1_rs1_lsu_mispred)
 );


select_mispred_bus rs2_mispred_select
(
 .i_entry_rnid (r_ex1_issue.rd_regs[1].rnid),
 .i_entry_type (r_ex1_issue.rd_regs[1].typ),
 .i_mispred    (i_mispred_lsu),

 .o_mispred    (w_ex1_rs2_lsu_mispred)
 );

assign w_commit_flushed = scariv_pkg::is_flushed_commit(i_commit);


assign w_ex1_rs1_mispred = r_ex1_issue.rd_regs[0].valid & r_ex1_issue.rd_regs[0].predict_ready ? w_ex1_rs1_lsu_mispred : 1'b0;
assign w_ex1_rs2_mispred = r_ex1_issue.rd_regs[1].valid & r_ex1_issue.rd_regs[1].predict_ready ? w_ex1_rs2_lsu_mispred : 1'b0;

assign o_ex1_early_wr.valid = r_ex1_issue.valid & r_ex1_issue.wr_reg.valid &
                              ~w_ex1_rs1_mispred & ~w_ex1_rs2_mispred;
assign o_ex1_early_wr.rd_rnid = r_ex1_issue.wr_reg.rnid;
assign o_ex1_early_wr.rd_type = r_ex1_issue.wr_reg.typ;
assign o_ex1_early_wr.may_mispred = 1'b0;

generate
  for (genvar tgt_idx = 0; tgt_idx < scariv_pkg::TGT_BUS_SIZE; tgt_idx++) begin : rs_tgt_loop
    assign w_ex2_rs1_fwd_valid[tgt_idx] = r_ex2_issue.rd_regs[0].valid & ex1_i_phy_wr[tgt_idx].valid &
                                          (r_ex2_issue.rd_regs[0].typ  == ex1_i_phy_wr[tgt_idx].rd_type) &
                                          (r_ex2_issue.rd_regs[0].rnid == ex1_i_phy_wr[tgt_idx].rd_rnid) &
                                          (r_ex2_issue.rd_regs[0].rnid != 'h0);   // GPR[x0] always zero

    assign w_ex2_rs2_fwd_valid[tgt_idx] = r_ex2_issue.rd_regs[1].valid & ex1_i_phy_wr[tgt_idx].valid &
                                          (r_ex2_issue.rd_regs[1].typ  == ex1_i_phy_wr[tgt_idx].rd_type) &
                                          (r_ex2_issue.rd_regs[1].rnid == ex1_i_phy_wr[tgt_idx].rd_rnid) &
                                          (r_ex2_issue.rd_regs[1].rnid != 'h0);   // GPR[x0] always zero
    assign w_ex2_tgt_data[tgt_idx] = ex1_i_phy_wr[tgt_idx].rd_data;
  end
endgenerate

bit_oh_or #(
    .T(riscv_pkg::xlen_t),
    .WORDS(scariv_pkg::TGT_BUS_SIZE)
) u_rs1_data_select (
    .i_oh(w_ex2_rs1_fwd_valid),
    .i_data(w_ex2_tgt_data),
    .o_selected(w_ex2_rs1_fwd_data)
);

bit_oh_or #(
    .T(riscv_pkg::xlen_t),
    .WORDS(scariv_pkg::TGT_BUS_SIZE)
) u_rs2_data_select (
    .i_oh(w_ex2_rs2_fwd_valid),
    .i_data(w_ex2_tgt_data),
    .o_selected(w_ex2_rs2_fwd_data)
);

// EX1 brtag flush check
assign w_ex1_br_flush  = scariv_pkg::is_br_flush_target(r_ex1_issue.cmt_id, r_ex1_issue.grp_id, ex3_br_upd_if.cmt_id, ex3_br_upd_if.grp_id,
                                                      ex3_br_upd_if.dead, ex3_br_upd_if.mispredict) & ex3_br_upd_if.update & r_ex1_issue.valid;

always_comb begin
  w_ex2_issue_next = r_ex1_issue;
end

always_ff @(posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_ex2_rs1_data <= 'h0;
    r_ex2_rs2_data <= 'h0;

    r_ex2_issue <= 'h0;
    r_ex2_index <= 'h0;
    r_ex2_pipe_ctrl <= 'h0;
    r_ex2_dead <= 1'b0;

    r_ex2_wr_valid <= 1'b0;
  end else begin
    r_ex2_rs1_data <= |w_ex1_rs_fwd_valid[0] ? w_ex1_rs_fwd_data[0] : ex1_regread_rs1.data;
    r_ex2_rs2_data <= |w_ex1_rs_fwd_valid[1] ? w_ex1_rs_fwd_data[1] : ex1_regread_rs2.data;

    r_ex2_issue <= w_ex2_issue_next;
    r_ex2_index <= r_ex1_index;
    r_ex2_pipe_ctrl <= r_ex1_pipe_ctrl;
    r_ex2_dead <= r_ex1_dead | r_ex1_issue.valid & (w_ex1_br_flush | w_commit_flushed);

    r_ex2_wr_valid <= o_ex1_early_wr.valid;
  end
end

assign w_ex2_rs1_selected_data = |w_ex2_rs1_fwd_valid ? w_ex2_rs1_fwd_data : r_ex2_rs1_data;
assign w_ex2_rs2_selected_data = |w_ex2_rs2_fwd_valid ? w_ex2_rs2_fwd_data : r_ex2_rs2_data;

assign w_ex2_rs1_pred_hit = r_ex2_issue.rd_regs[0].valid & r_ex2_issue.rd_regs[0].predict_ready ? |w_ex2_rs1_fwd_valid : 1'b1;
assign w_ex2_rs2_pred_hit = r_ex2_issue.rd_regs[1].valid & r_ex2_issue.rd_regs[1].predict_ready ? |w_ex2_rs2_fwd_valid : 1'b1;

// EX2 brtag flush check
assign w_ex2_br_flush  = scariv_pkg::is_br_flush_target(r_ex2_issue.cmt_id, r_ex2_issue.grp_id, ex3_br_upd_if.cmt_id, ex3_br_upd_if.grp_id,
                                                      ex3_br_upd_if.dead, ex3_br_upd_if.mispredict) & ex3_br_upd_if.update & r_ex3_issue.valid;

always_comb begin
  w_ex3_issue_next = r_ex2_issue;
end

always_ff @(posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_ex3_result   <= 'h0;
    r_ex3_index    <= 'h0;
    r_ex3_issue    <= 'h0;
    r_ex3_br_vaddr <= 'h0;
    r_ex3_pipe_ctrl <= 'h0;
    r_ex3_dead <= 1'b0;

    r_ex3_rs1_pred_hit <= 1'b0;
    r_ex3_rs2_pred_hit <= 1'b0;
  end else begin
    r_ex3_issue    <= w_ex3_issue_next;
    r_ex3_index    <= r_ex2_index;
    r_ex3_br_vaddr <= w_ex2_br_vaddr;
    r_ex3_pipe_ctrl <= r_ex2_pipe_ctrl;
    r_ex3_dead <= r_ex2_dead | r_ex2_issue.valid & (w_ex2_br_flush | w_commit_flushed);

    r_ex3_rs1_pred_hit <= w_ex2_rs1_pred_hit;
    r_ex3_rs2_pred_hit <= w_ex2_rs2_pred_hit;

    case (r_ex2_pipe_ctrl.op)
      OP_EQ : r_ex3_result <= w_ex2_rs1_selected_data == w_ex2_rs2_selected_data;
      OP_NE : r_ex3_result <= w_ex2_rs1_selected_data != w_ex2_rs2_selected_data;
      OP_LT : r_ex3_result <= $signed(w_ex2_rs1_selected_data) <  $signed(w_ex2_rs2_selected_data);
      OP_GE : r_ex3_result <= $signed(w_ex2_rs1_selected_data) >= $signed(w_ex2_rs2_selected_data);
      OP_LTU: r_ex3_result <= w_ex2_rs1_selected_data <  w_ex2_rs2_selected_data;
      OP_GEU: r_ex3_result <= w_ex2_rs1_selected_data >= w_ex2_rs2_selected_data;
      OP__  : r_ex3_result <= 1'b1;   // Unconditional Jump
      default : r_ex3_result <= 1'bx;
    endcase
  end
end

assign o_ex3_phy_wr.valid   = r_ex3_issue.valid &
                              r_ex3_pipe_ctrl.wr_rd & (r_ex3_issue.wr_reg.regidx != 'h0) &
                              r_ex3_rs1_pred_hit & r_ex3_rs2_pred_hit;
assign o_ex3_phy_wr.rd_rnid = r_ex3_issue.wr_reg.rnid;
assign o_ex3_phy_wr.rd_type = r_ex3_issue.wr_reg.typ;
assign o_ex3_phy_wr.rd_data = {{(riscv_pkg::XLEN_W-riscv_pkg::VADDR_W){r_ex3_issue.pc_addr[riscv_pkg::VADDR_W-1]}},
                               r_ex3_issue.pc_addr} + (r_ex3_issue.is_rvc ? 'h2 : 'h4);

assign o_done_report.valid    = r_ex3_issue.valid & r_ex3_rs1_pred_hit & r_ex3_rs2_pred_hit;
assign o_done_report.cmt_id   = r_ex3_issue.cmt_id;
assign o_done_report.grp_id   = r_ex3_issue.grp_id;
assign o_done_report.except_valid  = 1'b0;
assign o_done_report.except_type = scariv_pkg::except_t'('h0);

scariv_pkg::vaddr_t w_ex2_offset_uj;
scariv_pkg::vaddr_t w_ex2_offset_sb;

assign w_ex2_offset_uj = {{(riscv_pkg::VADDR_W-21){r_ex2_issue.inst[31]}},
                          r_ex2_issue.inst[31],
                          r_ex2_issue.inst[19:12],
                          r_ex2_issue.inst[20],
                          r_ex2_issue.inst[30:21],
                          1'b0};
assign w_ex2_offset_sb = {{(riscv_pkg::VADDR_W-13){r_ex2_issue.inst[31]}},
                          r_ex2_issue.inst[31],
                          r_ex2_issue.inst[ 7],
                          r_ex2_issue.inst[30:25],
                          r_ex2_issue.inst[11: 8],
                          1'b0};

always_comb begin
  case (r_ex2_pipe_ctrl.imm)
    IMM_SB : w_ex2_br_vaddr = r_ex2_issue.pc_addr + w_ex2_offset_sb;
    IMM_UJ : w_ex2_br_vaddr = r_ex2_issue.pc_addr + w_ex2_offset_uj;
    IMM_I  : begin
      scariv_pkg::vaddr_t          w_ex2_br_vaddr_tmp;
      w_ex2_br_vaddr_tmp = w_ex2_rs1_selected_data[riscv_pkg::VADDR_W-1: 0] +
                           {{(riscv_pkg::VADDR_W-12){r_ex2_issue.inst[31]}},
                            r_ex2_issue.inst[31:20]};
      // When JALR, clearing lowest bit
      w_ex2_br_vaddr = {w_ex2_br_vaddr_tmp[riscv_pkg::VADDR_W-1: 1], 1'b0};
    end
    default : w_ex2_br_vaddr = {riscv_pkg::VADDR_W{1'bx}};
  endcase // case (w_ex2_pipe_ctrl.imm)
end // always_comb

// logic w_ex3_not_predict_taken;
logic w_ex3_ras_hit;
logic w_ex3_call_hit;
logic w_ex3_bim_hit;

assign w_ex3_call_hit = r_ex3_issue.is_call & r_ex3_issue.pred_taken & (r_ex3_br_vaddr == r_ex3_issue.pred_target_vaddr);
assign w_ex3_ras_hit = r_ex3_issue.is_ret & r_ex3_issue.pred_taken & (r_ex3_br_vaddr == r_ex3_issue.pred_target_vaddr);
assign w_ex3_bim_hit = r_ex3_issue.btb_valid &
                       ((~r_ex3_result & ~r_ex3_issue.pred_taken) |
                        (r_ex3_result & r_ex3_issue.pred_taken &
                         (r_ex3_br_vaddr == r_ex3_issue.pred_target_vaddr)));

assign ex3_br_upd_if.update        = r_ex3_issue.valid & r_ex3_rs1_pred_hit & r_ex3_rs2_pred_hit;
assign ex3_br_upd_if.is_cond       = r_ex3_pipe_ctrl.is_cond;
assign ex3_br_upd_if.is_call       = r_ex3_issue.is_call;
assign ex3_br_upd_if.is_ret        = r_ex3_issue.is_ret;
assign ex3_br_upd_if.is_rvc        = r_ex3_issue.is_rvc;
assign ex3_br_upd_if.ras_index     = r_ex3_issue.ras_index;
assign ex3_br_upd_if.taken         = r_ex3_result;
assign ex3_br_upd_if.dead          = r_ex3_dead;
assign ex3_br_upd_if.mispredict    = r_ex3_issue.is_call   ? ~w_ex3_call_hit :
                                     r_ex3_issue.is_ret    ? ~w_ex3_ras_hit  :
                                     r_ex3_issue.btb_valid ? ~w_ex3_bim_hit  :
                                     r_ex3_result;

assign ex3_br_upd_if.bim_value     = r_ex3_issue.bim_value;
assign ex3_br_upd_if.pc_vaddr      = /* r_ex3_issue.is_rvc ? */ r_ex3_issue.pc_addr /* : r_ex3_issue.pc_addr + 'h2 */;
assign ex3_br_upd_if.target_vaddr  = r_ex3_result ? r_ex3_br_vaddr :
                                     r_ex3_issue.is_rvc ? r_ex3_issue.pc_addr + 'h2 : r_ex3_issue.pc_addr + 'h4;
`ifdef SIMULATION
assign ex3_br_upd_if.pred_vaddr    = r_ex3_issue.pred_target_vaddr;
`endif // SIMULATION

assign ex3_br_upd_if.cmt_id        = r_ex3_issue.cmt_id;
assign ex3_br_upd_if.grp_id        = r_ex3_issue.grp_id;
assign ex3_br_upd_if.brtag         = r_ex3_issue.brtag;
assign ex3_br_upd_if.br_mask       = r_ex3_issue.br_mask;

`ifdef SIMULATION
`ifdef MONITOR

// Kanata
import "DPI-C" function void log_stage
(
 input longint id,
 input string stage
);

always_ff @ (negedge i_clk, negedge i_reset_n) begin
  if (i_reset_n) begin
    if (r_ex0_issue.valid) begin
      log_stage (r_ex0_issue.kanata_id, "EX0");
    end
    if (r_ex1_issue.valid) begin
      log_stage (r_ex1_issue.kanata_id, "EX1");
    end
    if (r_ex2_issue.valid) begin
      log_stage (r_ex2_issue.kanata_id, "EX2");
    end
    if (r_ex3_issue.valid) begin
      log_stage (r_ex3_issue.kanata_id, "EX3");
    end
  end
end

`endif // MONITOR
`endif // SIMULATION

endmodule // scariv_bru_pipe
