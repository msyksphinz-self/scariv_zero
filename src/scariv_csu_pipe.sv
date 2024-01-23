// ------------------------------------------------------------------------
// NAME : scariv_csu_pipe
// TYPE : module
// ------------------------------------------------------------------------
// Access CSR
// ------------------------------------------------------------------------
// ex0: Decode instruction
// ex1: Send Early-release
// ex2: Nothing
// ex3: Back to response
// ------------------------------------------------------------------------

module scariv_csu_pipe
  import decoder_csu_ctrl_pkg::*;
#(
  parameter RV_ENTRY_SIZE = 32
  )
(
  input logic                       i_clk,
  input logic                       i_reset_n,

  commit_if.monitor      commit_if,

  input scariv_pkg::issue_t           rv0_issue,

  regread_if.master                 ex1_regread_rs1,

  early_wr_if.master       ex1_early_wr_if,
  phy_wr_if.master         ex3_phy_wr_if,

  /* CSR information */
  input riscv_common_pkg::priv_t               i_status_priv,
  input riscv_pkg::xlen_t i_mstatus,

  csr_rd_if.master                  read_if,
  csr_wr_if.master                  write_if,

  done_report_if.master     done_report_if
);

`include "scariv_csr_def.svh"

typedef struct packed {
  op_t  op;
  logic is_mret;
  logic is_sret;
  logic is_uret;
  logic is_ecall;
  logic is_ebreak;
  logic csr_update;
} pipe_ctrl_t;

scariv_pkg::issue_t    r_ex0_issue;
pipe_ctrl_t            w_ex0_pipe_ctrl;
csr_update_t           w_ex0_csr_update;

pipe_ctrl_t            r_ex1_pipe_ctrl;
scariv_pkg::issue_t    r_ex1_issue;

riscv_pkg::xlen_t      w_ex2_rs1_selected_data;

pipe_ctrl_t            r_ex2_pipe_ctrl;
scariv_pkg::issue_t    r_ex2_issue;
// riscv_pkg::xlen_t      r_ex2_rs1_data;
logic                  w_ex2_is_fs_illegal;

pipe_ctrl_t            r_ex3_pipe_ctrl;
scariv_pkg::issue_t    r_ex3_issue;
riscv_pkg::xlen_t      r_ex3_result;
riscv_pkg::xlen_t      r_ex3_csr_rd_data;
logic                  r_ex3_csr_illegal;

always_comb begin
  r_ex0_issue = rv0_issue;
end

decoder_csu_ctrl u_pipe_ctrl (
  .inst(r_ex0_issue.inst),
  .op            (w_ex0_pipe_ctrl.op           ),
  .is_mret       (w_ex0_pipe_ctrl.is_mret      ),
  .is_sret       (w_ex0_pipe_ctrl.is_sret      ),
  .is_uret       (w_ex0_pipe_ctrl.is_uret      ),
  .is_ecall      (w_ex0_pipe_ctrl.is_ecall     ),
  .is_ebreak     (w_ex0_pipe_ctrl.is_ebreak    ),
  .is_wfi        (),
  .csr_update    (w_ex0_csr_update             )
);
assign w_ex0_pipe_ctrl.csr_update = w_ex0_csr_update == decoder_csu_ctrl_pkg::CSR_UPDATE_1 ? 1'b1 : 1'b0;

assign ex1_regread_rs1.valid = r_ex1_issue.valid & r_ex1_issue.rd_regs[0].valid;
assign ex1_regread_rs1.rnid  = r_ex1_issue.rd_regs[0].rnid;

always_ff @(posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_ex1_issue <= 'h0;
    r_ex1_pipe_ctrl <= 'h0;
  end else begin
    r_ex1_issue <= r_ex0_issue;
    r_ex1_pipe_ctrl <= w_ex0_pipe_ctrl;
  end
end

// assign o_ex1_early_wr.valid       = r_ex1_issue.valid & r_ex1_issue.wr_reg.valid;
// assign o_ex1_early_wr.rd_rnid     = r_ex1_issue.wr_reg.rnid;
// assign o_ex1_early_wr.rd_type     = r_ex1_issue.wr_reg.typ;
// assign o_ex1_early_wr.may_mispred = 1'b0;

always_ff @(posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    // r_ex2_rs1_data <= 'h0;

    r_ex2_issue <= 'h0;
    r_ex2_pipe_ctrl <= 'h0;
  end else begin
    // r_ex2_rs1_data <= ex1_regread_rs1.data;

    r_ex2_issue <= r_ex1_issue;
    r_ex2_pipe_ctrl <= r_ex1_pipe_ctrl;
  end
end

assign w_ex2_rs1_selected_data = !r_ex2_issue.rd_regs[0].valid ? {{(riscv_pkg::XLEN_W-5){/* r_ex2_issue.inst[19] */1'b0}}, r_ex2_issue.inst[19:15]} :
                                 ex1_regread_rs1.data;

// ------------
// CSR Read
// ------------
assign read_if.valid = r_ex2_issue.valid & r_ex2_pipe_ctrl.csr_update;
assign read_if.addr  = r_ex2_issue.inst[31:20];

assign w_ex2_is_fs_illegal = r_ex2_pipe_ctrl.csr_update &
                             ((r_ex2_issue.inst[31:20] == `SYSREG_ADDR_FFLAGS) |
                              (r_ex2_issue.inst[31:20] == `SYSREG_ADDR_FRM   ) |
                              (r_ex2_issue.inst[31:20] == `SYSREG_ADDR_FCSR  )) & i_mstatus[`MSTATUS_FS] == 'h0;

always_ff @(posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_ex3_result    <= 'h0;
    r_ex3_issue     <= 'h0;
    r_ex3_pipe_ctrl <= 'h0;
    r_ex3_csr_illegal <= 1'b0;
  end else begin
    r_ex3_issue     <= r_ex2_issue;
    r_ex3_pipe_ctrl <= r_ex2_pipe_ctrl;

    r_ex3_csr_illegal <= read_if.resp_error | w_ex2_is_fs_illegal;

    case (r_ex2_pipe_ctrl.op)
      OP_RW: r_ex3_result <= w_ex2_rs1_selected_data;
      OP_RS: r_ex3_result <= read_if.data | w_ex2_rs1_selected_data;
      OP_RC: r_ex3_result <= read_if.data & ~w_ex2_rs1_selected_data;
      OP__ : r_ex3_result <= 'h0;
      default : r_ex3_result <= w_ex2_rs1_selected_data;
    endcase // case (r_ex2_pipe_ctrl.op)

    /* verilator lint_off WIDTH */
    r_ex3_csr_rd_data <= (read_if.addr == `SYSREG_ADDR_MINSTRET) ? read_if.data + scariv_pkg::encoder_grp_id({1'b0, r_ex2_issue.grp_id[scariv_conf_pkg::DISP_SIZE-1:1]}) :
                         read_if.data;
  end
end

assign ex3_phy_wr_if.valid   = r_ex3_issue.valid & r_ex3_issue.wr_reg.valid;
assign ex3_phy_wr_if.rd_rnid = r_ex3_issue.wr_reg.rnid;
assign ex3_phy_wr_if.rd_type = r_ex3_issue.wr_reg.typ;
assign ex3_phy_wr_if.rd_data = r_ex3_csr_rd_data;

logic w_ex3_sret_tsr_illegal;

assign w_ex3_sret_tsr_illegal   = r_ex3_pipe_ctrl.is_sret       & i_mstatus[`MSTATUS_TSR];

assign done_report_if.valid    = r_ex3_issue.valid;
assign done_report_if.cmt_id   = r_ex3_issue.cmt_id;
assign done_report_if.grp_id   = r_ex3_issue.grp_id;
assign done_report_if.except_valid  = r_ex3_pipe_ctrl.csr_update |
                                     r_ex3_pipe_ctrl.is_mret |
                                     r_ex3_pipe_ctrl.is_sret |
                                     r_ex3_pipe_ctrl.is_uret |
                                     r_ex3_pipe_ctrl.is_ecall |
                                     r_ex3_pipe_ctrl.is_ebreak |
                                     r_ex3_csr_illegal |
                                     (write_if.valid & write_if.resp_error);

assign done_report_if.except_type = (r_ex3_csr_illegal | w_ex3_sret_tsr_illegal | write_if.valid & write_if.resp_error) ? scariv_pkg::ILLEGAL_INST :
                                   r_ex3_pipe_ctrl.is_mret ? scariv_pkg::MRET :
                                   r_ex3_pipe_ctrl.is_sret ? scariv_pkg::SRET :
                                   r_ex3_pipe_ctrl.is_uret ? scariv_pkg::URET :
                                   r_ex3_pipe_ctrl.is_ecall & (i_status_priv == riscv_common_pkg::PRIV_U) ? scariv_pkg::ECALL_U :
                                   r_ex3_pipe_ctrl.is_ecall & (i_status_priv == riscv_common_pkg::PRIV_S) ? scariv_pkg::ECALL_S :
                                   r_ex3_pipe_ctrl.is_ecall & (i_status_priv == riscv_common_pkg::PRIV_M) ? scariv_pkg::ECALL_M :
                                   r_ex3_pipe_ctrl.is_ebreak ? scariv_pkg::BREAKPOINT :
                                   scariv_pkg::SILENT_FLUSH;

assign done_report_if.except_tval = (r_ex3_csr_illegal | w_ex3_sret_tsr_illegal) ? r_ex3_issue.inst :
                                   'h0;

// ------------
// CSR Update
// ------------
assign write_if.valid = r_ex3_issue.valid &
                        !r_ex3_csr_illegal &
                        r_ex3_pipe_ctrl.csr_update &
                        !((write_if.addr == `SYSREG_ADDR_MISA) & r_ex3_issue.pc_addr[1]) & // Suppress write MISA when next fetch become misalign
                        !((r_ex3_pipe_ctrl.op == OP_RS || r_ex3_pipe_ctrl.op == OP_RC) &
                          r_ex3_issue.rd_regs[0].valid & (r_ex3_issue.rd_regs[0].regidx == 5'h0));
assign write_if.addr  = r_ex3_issue.inst[31:20];
assign write_if.data  = r_ex3_result;

`ifdef SIMULATION

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

`endif // SIMULATION

endmodule // scariv_csu_pipe
