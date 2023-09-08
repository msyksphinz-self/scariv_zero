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

  input scariv_bru_pkg::issue_entry_t rv0_issue,
  input logic [RV_ENTRY_SIZE-1:0]     rv0_index,
  phy_wr_if.slave          ex1_phy_wr_if[scariv_pkg::TGT_BUS_SIZE],

  // Commit notification
  commit_if.monitor      commit_if,

  lsu_mispred_if.slave         mispred_if[scariv_conf_pkg::LSU_INST_NUM],

  regread_if.master                   ex0_regread_rs1,
  regread_if.master                   ex0_regread_rs2,

  early_wr_if.master ex1_early_wr_if,
  phy_wr_if.master   ex3_phy_wr_if,

  done_report_if.master             done_report_if,
  br_upd_if.master                  ex3_br_upd_if
);

typedef struct packed {
  op_t  op;
  logic is_cond;
  imm_t imm;
  logic wr_rd;
} pipe_ctrl_t;

logic   w_commit_flushed;

scariv_bru_pkg::issue_entry_t            w_ex0_issue;
logic [RV_ENTRY_SIZE-1: 0]               w_ex0_index;
pipe_ctrl_t                              w_ex0_pipe_ctrl;
logic                                    w_ex0_br_flush;
riscv_pkg::xlen_t                        w_ex0_rs_fwd_data [2];

pipe_ctrl_t                              r_ex1_pipe_ctrl;
scariv_bru_pkg::issue_entry_t            r_ex1_issue;
scariv_bru_pkg::issue_entry_t            w_ex1_issue_next;
logic [RV_ENTRY_SIZE-1: 0]               r_ex1_index;
logic                                    w_ex1_br_flush;
logic                                    r_ex1_dead;
riscv_pkg::xlen_t                        r_ex1_rs1_data;
riscv_pkg::xlen_t                        r_ex1_rs2_data;

riscv_pkg::xlen_t                        w_ex1_rs_fwd_data [2];

riscv_pkg::xlen_t                        w_ex1_rs1_selected_data;
riscv_pkg::xlen_t                        w_ex1_rs2_selected_data;

riscv_pkg::xlen_t w_ex1_tgt_data          [scariv_pkg::TGT_BUS_SIZE];
riscv_pkg::xlen_t w_ex1_rs1_fwd_data;
riscv_pkg::xlen_t w_ex1_rs2_fwd_data;

scariv_pkg::vaddr_t                      w_ex1_br_vaddr;

logic                                    w_ex0_rs1_lsu_mispred;
logic                                    w_ex0_rs2_lsu_mispred;
logic                                    w_ex0_rs1_mispred;
logic                                    w_ex0_rs2_mispred;

pipe_ctrl_t                              r_ex2_pipe_ctrl;
scariv_bru_pkg::issue_entry_t            r_ex2_issue;
scariv_bru_pkg::issue_entry_t            w_ex2_issue_next;
logic [RV_ENTRY_SIZE-1: 0]               r_ex2_index;
riscv_pkg::xlen_t                        r_ex2_wr_data;
riscv_pkg::xlen_t                        w_ex2_wr_data;
scariv_pkg::vaddr_t                      r_ex2_br_vaddr;
logic                                    r_ex2_wr_valid;
logic                                    w_ex2_br_flush;
logic                                    r_ex2_dead;
logic                                    r_ex2_result;


always_comb begin
  w_ex0_issue = rv0_issue;
  w_ex0_index = rv0_index;
end

decoder_bru_ctrl u_pipe_ctrl (
  .inst    (w_ex0_issue.inst       ),
  .op      (w_ex0_pipe_ctrl.op     ),
  .is_cond (w_ex0_pipe_ctrl.is_cond),
  .imm     (w_ex0_pipe_ctrl.imm    ),
  .wr_rd   (w_ex0_pipe_ctrl.wr_rd  )
);

assign ex0_regread_rs1.valid = w_ex0_issue.valid & w_ex0_issue.rd_regs[0].valid;
assign ex0_regread_rs1.rnid  = w_ex0_issue.rd_regs[0].rnid;

assign ex0_regread_rs2.valid = w_ex0_issue.valid & w_ex0_issue.rd_regs[1].valid;
assign ex0_regread_rs2.rnid  = w_ex0_issue.rd_regs[1].rnid;

generate for (genvar rs_idx = 0; rs_idx < 2; rs_idx++) begin : ex0_rs_loop
  riscv_pkg::xlen_t w_ex0_tgt_data [scariv_pkg::TGT_BUS_SIZE];
  for (genvar tgt_idx = 0; tgt_idx < scariv_pkg::TGT_BUS_SIZE; tgt_idx++) begin : rs_tgt_loop
    assign w_ex0_tgt_data[tgt_idx] = ex1_phy_wr_if[tgt_idx].rd_data;
  end
  assign w_ex0_rs_fwd_data [rs_idx] = w_ex0_tgt_data[w_ex0_issue.rd_regs[rs_idx].early_index];
end endgenerate



// EX0 brtag flush check
assign w_ex0_br_flush  = scariv_pkg::is_br_flush_target(w_ex0_issue.cmt_id, w_ex0_issue.grp_id, ex3_br_upd_if.cmt_id, ex3_br_upd_if.grp_id,
                                                        ex3_br_upd_if.dead, ex3_br_upd_if.mispredict) & ex3_br_upd_if.update & w_ex0_issue.valid;

assign w_ex0_rs1_mispred = w_ex0_issue.rd_regs[0].valid & w_ex0_issue.rd_regs[0].predict_ready ? w_ex0_rs1_lsu_mispred : 1'b0;
assign w_ex0_rs2_mispred = w_ex0_issue.rd_regs[1].valid & w_ex0_issue.rd_regs[1].predict_ready ? w_ex0_rs2_lsu_mispred : 1'b0;

always_comb begin
  w_ex1_issue_next = w_ex0_issue;
  w_ex1_issue_next.valid = w_ex0_issue.valid & !w_ex0_br_flush & (~w_ex0_rs1_mispred & ~w_ex0_rs2_mispred);
end

always_ff @(posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_ex1_issue <= 'h0;
    r_ex1_index <= 'h0;
    r_ex1_pipe_ctrl <= 'h0;
    r_ex1_dead <= 1'b0;

    r_ex1_rs1_data <= 'h0;
    r_ex1_rs2_data <= 'h0;
  end else begin
    r_ex1_issue <= w_ex1_issue_next;
    r_ex1_index <= w_ex0_index;
    r_ex1_pipe_ctrl <= w_ex0_pipe_ctrl;
    r_ex1_dead <= w_ex0_issue.valid & (w_ex0_br_flush | w_commit_flushed);

    // r_ex1_rs1_data <= w_ex0_issue.rd_regs[0].predict_ready[1] ? w_ex0_rs_fwd_data[0] : ex0_regread_rs1.data;
    // r_ex1_rs2_data <= w_ex0_issue.rd_regs[1].predict_ready[1] ? w_ex0_rs_fwd_data[1] : ex0_regread_rs2.data;
    r_ex1_rs1_data <= w_ex0_rs_fwd_data[0];
    r_ex1_rs2_data <= w_ex0_rs_fwd_data[1];
  end // else: !if(!i_reset_n)
end // always_ff @ (posedge i_clk, negedge i_reset_n)

select_mispred_bus rs1_mispred_select
(
 .i_entry_rnid (w_ex0_issue.rd_regs[0].rnid),
 .i_entry_type (w_ex0_issue.rd_regs[0].typ),
 .i_mispred    (mispred_if),

 .o_mispred    (w_ex0_rs1_lsu_mispred)
 );


select_mispred_bus rs2_mispred_select
(
 .i_entry_rnid (w_ex0_issue.rd_regs[1].rnid),
 .i_entry_type (w_ex0_issue.rd_regs[1].typ),
 .i_mispred    (mispred_if),

 .o_mispred    (w_ex0_rs2_lsu_mispred)
 );

assign w_commit_flushed = commit_if.is_flushed_commit();


assign ex1_early_wr_if.valid   = w_ex0_issue.valid & w_ex0_issue.wr_reg.valid;
assign ex1_early_wr_if.rd_rnid = w_ex0_issue.wr_reg.rnid;
assign ex1_early_wr_if.rd_type = w_ex0_issue.wr_reg.typ;
assign ex1_early_wr_if.may_mispred = 1'b0;

generate for (genvar rs_idx = 0; rs_idx < 2; rs_idx++) begin : ex1_rs_loop
  riscv_pkg::xlen_t w_ex1_tgt_data [scariv_pkg::TGT_BUS_SIZE];
  for (genvar tgt_idx = 0; tgt_idx < scariv_pkg::TGT_BUS_SIZE; tgt_idx++) begin : rs_tgt_loop
    assign w_ex1_tgt_data[tgt_idx] = ex1_phy_wr_if[tgt_idx].rd_data;
  end
  assign w_ex1_rs_fwd_data [rs_idx] = w_ex1_tgt_data[r_ex1_issue.rd_regs[rs_idx].early_index];
end endgenerate // block: ex1_rs_loop

// EX1 brtag flush check
assign w_ex1_br_flush  = scariv_pkg::is_br_flush_target(r_ex1_issue.cmt_id, r_ex1_issue.grp_id, ex3_br_upd_if.cmt_id, ex3_br_upd_if.grp_id,
                                                      ex3_br_upd_if.dead, ex3_br_upd_if.mispredict) & ex3_br_upd_if.update & r_ex1_issue.valid;

always_comb begin
  w_ex2_issue_next = r_ex1_issue;
  w_ex2_issue_next.valid = r_ex1_issue.valid & !w_ex1_br_flush;
end

assign w_ex1_rs1_selected_data = r_ex1_issue.rd_regs[0].predict_ready[0] ? w_ex1_rs_fwd_data[0] :
                                 r_ex1_issue.rd_regs[0].predict_ready[1] ? r_ex1_rs1_data :
                                 ex0_regread_rs1.data;
assign w_ex1_rs2_selected_data = r_ex1_issue.rd_regs[1].predict_ready[0] ? w_ex1_rs_fwd_data[1] :
                                 r_ex1_issue.rd_regs[1].predict_ready[1] ? r_ex1_rs2_data :
                                 ex0_regread_rs2.data;

always_ff @(posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_ex2_result   <= 'h0;
    r_ex2_index    <= 'h0;
    r_ex2_issue    <= 'h0;
    r_ex2_br_vaddr <= 'h0;
    r_ex2_pipe_ctrl <= 'h0;
    r_ex2_dead <= 1'b0;
  end else begin
    r_ex2_issue     <= w_ex2_issue_next;
    r_ex2_index     <= r_ex1_index;
    r_ex2_br_vaddr  <= w_ex1_br_vaddr;
    r_ex2_pipe_ctrl <= r_ex1_pipe_ctrl;
    r_ex2_dead      <= r_ex1_dead | r_ex1_issue.valid & (w_ex1_br_flush | w_commit_flushed);

    case (r_ex1_pipe_ctrl.op)
      OP_EQ   : r_ex2_result <=         w_ex1_rs1_selected_data ==          w_ex1_rs2_selected_data;
      OP_NE   : r_ex2_result <=         w_ex1_rs1_selected_data !=          w_ex1_rs2_selected_data;
      OP_LT   : r_ex2_result <= $signed(w_ex1_rs1_selected_data) <  $signed(w_ex1_rs2_selected_data);
      OP_GE   : r_ex2_result <= $signed(w_ex1_rs1_selected_data) >= $signed(w_ex1_rs2_selected_data);
      OP_LTU  : r_ex2_result <=         w_ex1_rs1_selected_data <           w_ex1_rs2_selected_data;
      OP_GEU  : r_ex2_result <=         w_ex1_rs1_selected_data >=          w_ex1_rs2_selected_data;
      OP_SIGN_AUIPC : r_ex2_result <= 1'b0;
      OP__    : r_ex2_result <= 1'b1;   // Unconditional Jump
      default : r_ex2_result <= 1'bx;
    endcase

    if (r_ex1_pipe_ctrl.op == OP_SIGN_AUIPC) begin
      r_ex2_wr_data <= {{(riscv_pkg::XLEN_W-riscv_pkg::VADDR_W){r_ex1_issue.pc_addr[riscv_pkg::VADDR_W-1]}},
                        r_ex1_issue.pc_addr} +
                       {{(riscv_pkg::XLEN_W-32){r_ex1_issue.inst[31]}}, r_ex1_issue.inst[31:12], 12'h000};
    end
  end
end

assign w_ex2_wr_data = r_ex2_pipe_ctrl.op == OP_SIGN_AUIPC ? r_ex2_wr_data :
                       {{(riscv_pkg::XLEN_W-riscv_pkg::VADDR_W){r_ex2_issue.pc_addr[riscv_pkg::VADDR_W-1]}},
                        r_ex2_issue.pc_addr} + (r_ex2_issue.is_rvc ? 'h2 : 'h4);

assign ex3_phy_wr_if.valid   = r_ex2_issue.valid &
                               r_ex2_pipe_ctrl.wr_rd & (r_ex2_issue.wr_reg.regidx != 'h0);
assign ex3_phy_wr_if.rd_rnid = r_ex2_issue.wr_reg.rnid;
assign ex3_phy_wr_if.rd_type = r_ex2_issue.wr_reg.typ;
assign ex3_phy_wr_if.rd_data = w_ex2_wr_data;

assign done_report_if.valid    = r_ex2_issue.valid;
assign done_report_if.cmt_id   = r_ex2_issue.cmt_id;
assign done_report_if.grp_id   = r_ex2_issue.grp_id;
assign done_report_if.except_valid  = 1'b0;
assign done_report_if.except_type = scariv_pkg::except_t'('h0);

scariv_pkg::vaddr_t w_ex1_offset_uj;
scariv_pkg::vaddr_t w_ex1_offset_sb;

assign w_ex1_offset_uj = {{(riscv_pkg::VADDR_W-21){r_ex1_issue.inst[31]}},
                          r_ex1_issue.inst[31],
                          r_ex1_issue.inst[19:12],
                          r_ex1_issue.inst[20],
                          r_ex1_issue.inst[30:21],
                          1'b0};
assign w_ex1_offset_sb = {{(riscv_pkg::VADDR_W-13){r_ex1_issue.inst[31]}},
                          r_ex1_issue.inst[31],
                          r_ex1_issue.inst[ 7],
                          r_ex1_issue.inst[30:25],
                          r_ex1_issue.inst[11: 8],
                          1'b0};

always_comb begin
  case (r_ex1_pipe_ctrl.imm)
    IMM_SB : w_ex1_br_vaddr = r_ex1_issue.pc_addr + w_ex1_offset_sb;
    IMM_UJ : w_ex1_br_vaddr = r_ex1_issue.pc_addr + w_ex1_offset_uj;
    IMM_I  : begin
      scariv_pkg::vaddr_t          w_ex1_br_vaddr_tmp;
      w_ex1_br_vaddr_tmp = w_ex1_rs1_selected_data[riscv_pkg::VADDR_W-1: 0] +
                           {{(riscv_pkg::VADDR_W-12){r_ex1_issue.inst[31]}},
                            r_ex1_issue.inst[31:20]};
      // When JALR, clearing lowest bit
      w_ex1_br_vaddr = {w_ex1_br_vaddr_tmp[riscv_pkg::VADDR_W-1: 1], 1'b0};
    end
    default : w_ex1_br_vaddr = {riscv_pkg::VADDR_W{1'bx}};
  endcase // case (w_ex1_pipe_ctrl.imm)
end // always_comb

// logic w_ex3_not_predict_taken;
logic w_ex2_ras_hit;
logic w_ex2_call_hit;
logic w_ex2_bim_hit;

assign w_ex2_call_hit = r_ex2_issue.is_call & r_ex2_issue.pred_taken & (r_ex2_br_vaddr == r_ex2_issue.pred_target_vaddr);
assign w_ex2_ras_hit  = r_ex2_issue.is_ret  & r_ex2_issue.pred_taken & (r_ex2_br_vaddr == r_ex2_issue.pred_target_vaddr);
assign w_ex2_bim_hit  = r_ex2_issue.btb_valid &
                        ((~r_ex2_result & ~r_ex2_issue.pred_taken) |
                         (r_ex2_result & r_ex2_issue.pred_taken &
                          (r_ex2_br_vaddr == r_ex2_issue.pred_target_vaddr)));

assign ex3_br_upd_if.update        = r_ex2_issue.valid & (r_ex2_pipe_ctrl.op != OP_SIGN_AUIPC);
assign ex3_br_upd_if.is_cond       = r_ex2_pipe_ctrl.is_cond;
assign ex3_br_upd_if.is_call       = r_ex2_issue.is_call;
assign ex3_br_upd_if.is_ret        = r_ex2_issue.is_ret;
assign ex3_br_upd_if.is_rvc        = r_ex2_issue.is_rvc;
assign ex3_br_upd_if.ras_index     = r_ex2_issue.ras_index;
assign ex3_br_upd_if.taken         = r_ex2_result;
assign ex3_br_upd_if.dead          = r_ex2_dead;
assign ex3_br_upd_if.mispredict    = r_ex2_issue.is_call   ? ~w_ex2_call_hit :
                                     r_ex2_issue.is_ret    ? ~w_ex2_ras_hit  :
                                     r_ex2_issue.btb_valid ? ~w_ex2_bim_hit  :
                                     r_ex2_result;

assign ex3_br_upd_if.bim_value     = r_ex2_issue.bim_value;
assign ex3_br_upd_if.pc_vaddr      = /* r_ex2_issue.is_rvc ? */ r_ex2_issue.pc_addr /* : r_ex2_issue.pc_addr + 'h2 */;
assign ex3_br_upd_if.basicblk_pc_vaddr  = r_ex2_issue.basicblk_pc_vaddr;
assign ex3_br_upd_if.target_vaddr  = r_ex2_result ? r_ex2_br_vaddr :
                                     r_ex2_issue.is_rvc ? r_ex2_issue.pc_addr + 'h2 : r_ex2_issue.pc_addr + 'h4;
`ifdef SIMULATION
assign ex3_br_upd_if.pred_vaddr    = r_ex2_issue.pred_target_vaddr;


always_ff @ (negedge i_clk, negedge i_reset_n) begin
  if (i_reset_n) begin
    if (ex3_br_upd_if.update & ex3_br_upd_if.mispredict & r_ex2_pipe_ctrl.op == OP_SIGN_AUIPC) begin
      $fatal(0, "In branch, ex3_br_upd_if.update and ex3_br_upd_if.mispredict must not be asserted in same time.\n");
    end
  end
end

`endif // SIMULATION

assign ex3_br_upd_if.cmt_id        = r_ex2_issue.cmt_id;
assign ex3_br_upd_if.grp_id        = r_ex2_issue.grp_id;
assign ex3_br_upd_if.brtag         = r_ex2_issue.brtag;
assign ex3_br_upd_if.gshare_bhr    = r_ex2_issue.gshare_bhr;
assign ex3_br_upd_if.gshare_index  = r_ex2_issue.gshare_index;
assign ex3_br_upd_if.btb_not_hit   = ~r_ex2_issue.btb_valid;

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
    if (w_ex0_issue.valid) begin
      log_stage (w_ex0_issue.kanata_id, "EX0");
    end
    if (r_ex1_issue.valid) begin
      log_stage (r_ex1_issue.kanata_id, "EX1");
    end
    if (r_ex2_issue.valid) begin
      log_stage (r_ex2_issue.kanata_id, "EX2");
    end
  end
end

`endif // MONITOR
`endif // SIMULATION

endmodule // scariv_bru_pipe
