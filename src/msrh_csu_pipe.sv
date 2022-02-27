module msrh_csu_pipe
  import decoder_csu_ctrl_pkg::*;
#(
  parameter RV_ENTRY_SIZE = 32
  )
(
  input logic                       i_clk,
  input logic                       i_reset_n,

  input msrh_pkg::commit_blk_t      i_commit,

  input                             msrh_pkg::issue_t rv0_issue,
  input logic [RV_ENTRY_SIZE-1:0]   rv0_index,
  input                             msrh_pkg::phy_wr_t ex1_i_phy_wr[msrh_pkg::TGT_BUS_SIZE],

  regread_if.master                 ex1_regread_rs1,

  output                            msrh_pkg::early_wr_t o_ex1_early_wr,
  output                            msrh_pkg::phy_wr_t o_ex3_phy_wr,

  /* CSR information */
  input riscv_common_pkg::priv_t               i_status_priv,
  input logic [riscv_pkg::XLEN_W-1: 0] i_mstatus,

  csr_rd_if.master                  read_if,
  csr_wr_if.master                  write_if,

  /* SFENCE update information */
  sfence_if.master                  sfence_if,
  /* FENCE.I update */
  output logic                      o_fence_i,

  done_if.master   ex3_done_if
);

`include "msrh_csr_def.svh"

typedef struct packed {
  op_t  op;
  logic is_mret;
  logic is_sret;
  logic is_uret;
  logic is_ecall;
  logic is_ebreak;
  logic is_fence;
  logic is_fence_i;
  logic is_sfence_vma;
  logic csr_update;
} pipe_ctrl_t;

msrh_pkg::issue_t                        r_ex0_issue;
logic [RV_ENTRY_SIZE-1: 0] w_ex0_index;
pipe_ctrl_t                              w_ex0_pipe_ctrl;
csr_update_t                             w_ex0_csr_update;

pipe_ctrl_t                              r_ex1_pipe_ctrl;
msrh_pkg::issue_t                        r_ex1_issue;
logic [RV_ENTRY_SIZE-1: 0] r_ex1_index;

logic [msrh_pkg::TGT_BUS_SIZE-1:0] w_ex2_rs1_fwd_valid;
logic [riscv_pkg::XLEN_W-1:0]      w_ex2_tgt_data          [msrh_pkg::TGT_BUS_SIZE];
logic [riscv_pkg::XLEN_W-1:0]      w_ex2_rs1_fwd_data;
logic [riscv_pkg::XLEN_W-1:0]      w_ex2_csr_rd_data;
logic [riscv_pkg::XLEN_W-1:0]      w_ex2_rs1_selected_data;

pipe_ctrl_t                              r_ex2_pipe_ctrl;
msrh_pkg::issue_t                        r_ex2_issue;
logic [RV_ENTRY_SIZE-1: 0]               r_ex2_index;
logic [riscv_pkg::XLEN_W-1:0]            r_ex2_rs1_data;

pipe_ctrl_t                              r_ex3_pipe_ctrl;
msrh_pkg::issue_t                        r_ex3_issue;
logic [riscv_pkg::XLEN_W-1: 0]           r_ex3_result;
logic [RV_ENTRY_SIZE-1: 0]               r_ex3_index;
logic [riscv_pkg::XLEN_W-1: 0]           r_ex3_csr_rd_data;
logic                                    r_ex3_csr_illegal;

always_comb begin
  r_ex0_issue = rv0_issue;
  w_ex0_index = rv0_index;
end

decoder_csu_ctrl u_pipe_ctrl (
  .inst(r_ex0_issue.inst),
  .op            (w_ex0_pipe_ctrl.op           ),
  .is_mret       (w_ex0_pipe_ctrl.is_mret      ),
  .is_sret       (w_ex0_pipe_ctrl.is_sret      ),
  .is_uret       (w_ex0_pipe_ctrl.is_uret      ),
  .is_ecall      (w_ex0_pipe_ctrl.is_ecall     ),
  .is_ebreak     (w_ex0_pipe_ctrl.is_ebreak    ),
  .is_fence      (w_ex0_pipe_ctrl.is_fence     ),
  .is_fence_i    (w_ex0_pipe_ctrl.is_fence_i   ),
  .is_sfence_vma (w_ex0_pipe_ctrl.is_sfence_vma),
  .is_wfi        (),
  .csr_update    (w_ex0_csr_update             )
);
assign w_ex0_pipe_ctrl.csr_update = w_ex0_csr_update == decoder_csu_ctrl_pkg::CSR_UPDATE_1 ? 1'b1 : 1'b0;

assign ex1_regread_rs1.valid = r_ex1_issue.valid & r_ex1_issue.rd_regs[0].valid;
assign ex1_regread_rs1.rnid  = r_ex1_issue.rd_regs[0].rnid;

always_ff @(posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_ex1_issue <= 'h0;
    r_ex1_index <= 'h0;
    r_ex1_pipe_ctrl <= 'h0;
  end else begin
    r_ex1_issue <= r_ex0_issue;
    r_ex1_index <= w_ex0_index;
    r_ex1_pipe_ctrl <= w_ex0_pipe_ctrl;
  end
end

assign o_ex1_early_wr.valid       = r_ex1_issue.valid & r_ex1_issue.wr_reg.valid;
assign o_ex1_early_wr.rd_rnid     = r_ex1_issue.wr_reg.rnid;
assign o_ex1_early_wr.rd_type     = msrh_pkg::GPR;
assign o_ex1_early_wr.may_mispred = 1'b0;

generate
  for (genvar tgt_idx = 0; tgt_idx < msrh_pkg::REL_BUS_SIZE; tgt_idx++) begin : rs_tgt_loop
    assign w_ex2_rs1_fwd_valid[tgt_idx] = r_ex2_issue.rd_regs[0].valid & ex1_i_phy_wr[tgt_idx].valid &
                                          (r_ex2_issue.rd_regs[0].typ  == ex1_i_phy_wr[tgt_idx].rd_type) &
                                          (r_ex2_issue.rd_regs[0].rnid == ex1_i_phy_wr[tgt_idx].rd_rnid) &
                                          (r_ex2_issue.rd_regs[0].rnid != 'h0);   // GPR[x0] always zero

    assign w_ex2_tgt_data[tgt_idx] = ex1_i_phy_wr[tgt_idx].rd_data;
  end
endgenerate

bit_oh_or #(
    .T(logic[riscv_pkg::XLEN_W-1:0]),
    .WORDS(msrh_pkg::TGT_BUS_SIZE)
) u_rs1_data_select (
    .i_oh(w_ex2_rs1_fwd_valid),
    .i_data(w_ex2_tgt_data),
    .o_selected(w_ex2_rs1_fwd_data)
);

always_ff @(posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_ex2_rs1_data <= 'h0;

    r_ex2_issue <= 'h0;
    r_ex2_index <= 'h0;
    r_ex2_pipe_ctrl <= 'h0;
  end else begin
    r_ex2_rs1_data <= ex1_regread_rs1.data;

    r_ex2_issue <= r_ex1_issue;
    r_ex2_index <= r_ex1_index;
    r_ex2_pipe_ctrl <= r_ex1_pipe_ctrl;
  end
end

assign w_ex2_rs1_selected_data = !r_ex2_issue.rd_regs[0].valid ? {{(riscv_pkg::XLEN_W-5){/* r_ex2_issue.inst[19] */1'b0}}, r_ex2_issue.inst[19:15]} :
                                 |w_ex2_rs1_fwd_valid ? w_ex2_rs1_fwd_data : r_ex2_rs1_data;

// ------------
// CSR Read
// ------------
assign read_if.valid = r_ex2_issue.valid;
assign read_if.addr  = r_ex2_issue.inst[31:20];

always_ff @(posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_ex3_result    <= 'h0;
    r_ex3_index     <= 'h0;
    r_ex3_issue     <= 'h0;
    r_ex3_pipe_ctrl <= 'h0;
    r_ex3_csr_illegal <= 1'b0;
  end else begin
    r_ex3_issue     <= r_ex2_issue;
    r_ex3_index     <= r_ex2_index;
    r_ex3_pipe_ctrl <= r_ex2_pipe_ctrl;

    r_ex3_csr_illegal <= read_if.resp_error;

    case (r_ex2_pipe_ctrl.op)
      OP_RW: r_ex3_result <= w_ex2_rs1_selected_data;
      OP_RS: r_ex3_result <= read_if.data | w_ex2_rs1_selected_data;
      OP_RC: r_ex3_result <= read_if.data & ~w_ex2_rs1_selected_data;
      OP__ : r_ex3_result <= 'h0;
      default : r_ex3_result <= w_ex2_rs1_selected_data;
    endcase // case (r_ex2_pipe_ctrl.op)

    /* verilator lint_off WIDTH */
    r_ex3_csr_rd_data <= (read_if.addr == `SYSREG_ADDR_MINSTRET) ? read_if.data + msrh_pkg::encoder_grp_id({1'b0, r_ex2_issue.grp_id[msrh_conf_pkg::DISP_SIZE-1:1]}) :
                         read_if.data;
  end
end

assign o_ex3_phy_wr.valid   = r_ex3_issue.valid;
assign o_ex3_phy_wr.rd_rnid = r_ex3_issue.wr_reg.rnid;
assign o_ex3_phy_wr.rd_type = r_ex3_issue.wr_reg.typ;
assign o_ex3_phy_wr.rd_data = r_ex3_csr_rd_data;

logic w_ex3_sfence_vma_illegal;
logic w_ex3_sret_tsr_illegal;

assign w_ex3_sfence_vma_illegal = r_ex3_pipe_ctrl.is_sfence_vma & i_mstatus[`MSTATUS_TVM];
assign w_ex3_sret_tsr_illegal   = r_ex3_pipe_ctrl.is_sret       & i_mstatus[`MSTATUS_TSR];

assign ex3_done_if.done       = r_ex3_issue.valid;
assign ex3_done_if.index_oh   = r_ex3_index;
assign ex3_done_if.except_valid  = r_ex3_pipe_ctrl.csr_update |
                                   r_ex3_pipe_ctrl.is_mret |
                                   r_ex3_pipe_ctrl.is_sret |
                                   r_ex3_pipe_ctrl.is_uret |
                                   r_ex3_pipe_ctrl.is_ecall |
                                   r_ex3_pipe_ctrl.is_fence_i |
                                   r_ex3_pipe_ctrl.is_sfence_vma |
                                   r_ex3_csr_illegal | w_ex3_sfence_vma_illegal | /* w_ex3_sret_tsr_illegal (cover by pipe.is_sret)*/
                                   (write_if.valid & write_if.resp_error);

assign ex3_done_if.except_type = (r_ex3_csr_illegal | w_ex3_sfence_vma_illegal | w_ex3_sret_tsr_illegal) ? msrh_pkg::ILLEGAL_INST :
                                 r_ex3_pipe_ctrl.is_mret ? msrh_pkg::MRET :
                                 r_ex3_pipe_ctrl.is_sret ? msrh_pkg::SRET :
                                 r_ex3_pipe_ctrl.is_uret ? msrh_pkg::URET :
                                 r_ex3_pipe_ctrl.is_ecall & (i_status_priv == riscv_common_pkg::PRIV_U) ? msrh_pkg::ECALL_U :
                                 r_ex3_pipe_ctrl.is_ecall & (i_status_priv == riscv_common_pkg::PRIV_S) ? msrh_pkg::ECALL_S :
                                 r_ex3_pipe_ctrl.is_ecall & (i_status_priv == riscv_common_pkg::PRIV_M) ? msrh_pkg::ECALL_M :
                                 msrh_pkg::SILENT_FLUSH;

assign ex3_done_if.except_tval = (r_ex3_csr_illegal | w_ex3_sfence_vma_illegal | w_ex3_sret_tsr_illegal) ? r_ex3_issue.inst :
                                 'h0;

// ------------
// CSR Update
// ------------
assign write_if.valid = r_ex3_issue.valid &
                        r_ex3_pipe_ctrl.csr_update &
                        !((write_if.addr == `SYSREG_ADDR_MISA) & r_ex3_issue.pc_addr[1]) & // Suppress write MISA when next fetch become misalign
                        !((r_ex3_pipe_ctrl.op == OP_RS || r_ex3_pipe_ctrl.op == OP_RC) & r_ex3_issue.rd_regs[0].regidx == 5'h0);
assign write_if.addr  = r_ex3_issue.inst[31:20];
assign write_if.data  = r_ex3_result;

// ------------
// SFENCE Update
// ------------
logic r_sfence_vma_commit_wait;
logic [msrh_pkg::CMT_ID_W-1:0] r_sfence_vma_cmt_id;
logic [msrh_conf_pkg::DISP_SIZE-1:0] r_sfence_vma_grp_id;
logic                                r_sfence_vma_is_rs1_x0;
logic                                r_sfence_vma_is_rs2_x0;
logic [riscv_pkg::VADDR_W-1: 0]      r_sfence_vma_vaddr;

logic                                w_sfence_vma_sfence_commit_match;
assign w_sfence_vma_sfence_commit_match = r_sfence_vma_commit_wait & i_commit.commit &
                                          (i_commit.cmt_id == r_sfence_vma_cmt_id) &
                                          |(i_commit.grp_id & r_sfence_vma_grp_id);

always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_sfence_vma_commit_wait <= 'h0;
  end else begin
    if (w_sfence_vma_sfence_commit_match) begin
      r_sfence_vma_commit_wait <= 1'b0;
    end else if (r_ex3_issue.valid & r_ex3_pipe_ctrl.is_sfence_vma & ~w_ex3_sfence_vma_illegal) begin
      r_sfence_vma_commit_wait <= 1'b1;
      r_sfence_vma_cmt_id <= r_ex3_issue.cmt_id;
      r_sfence_vma_grp_id <= r_ex3_issue.grp_id;
      r_sfence_vma_is_rs1_x0 <= r_ex3_issue.rd_regs[0].regidx == 'h0;
      r_sfence_vma_is_rs2_x0 <= r_ex3_issue.rd_regs[1].regidx == 'h0;
      r_sfence_vma_vaddr     <= r_ex3_result[riscv_pkg::VADDR_W-1:0];
    end
  end // else: !if(i_reset_n)
end // always_ff @ (posedge i_clk, negedge i_reset_n)

assign sfence_if.valid     = r_sfence_vma_commit_wait & w_sfence_vma_sfence_commit_match;
assign sfence_if.is_rs1_x0 = r_ex3_issue.rd_regs[0].regidx == 'h0;
assign sfence_if.is_rs2_x0 = r_ex3_issue.rd_regs[1].regidx == 'h0;
assign sfence_if.vaddr     = r_ex3_result[riscv_pkg::VADDR_W-1:0];

// ---------------
// FENCE_I update
// ---------------
assign o_fence_i = r_ex3_issue.valid & r_ex3_pipe_ctrl.is_fence_i;

endmodule // msrh_csu_pipe
