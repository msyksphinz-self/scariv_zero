module msrh_csu_pipe
  import decoder_csu_ctrl_pkg::*;
#(
  parameter RV_ENTRY_SIZE = 32
  )
(
  input logic                       i_clk,
  input logic                       i_reset_n,

  input                             msrh_pkg::issue_t rv0_issue,
  input logic [RV_ENTRY_SIZE-1:0]   rv0_index,
  input                             msrh_pkg::phy_wr_t ex1_i_phy_wr[msrh_pkg::TGT_BUS_SIZE],

  regread_if.master                 ex1_regread_rs1,

  output                            msrh_pkg::early_wr_t o_ex1_early_wr,
  output                            msrh_pkg::phy_wr_t o_ex3_phy_wr,

  csr_rd_if.master                  read_if,
  csr_wr_if.master                  write_if,

  done_if.master   ex3_done_if
);

typedef struct packed {
  op_t  op;
  logic is_ret;
  logic is_ecall;
  logic is_ebreak;
  logic is_fence;
  logic is_fence_i;
} pipe_ctrl_t;

msrh_pkg::issue_t                        r_ex0_issue;
logic [RV_ENTRY_SIZE-1: 0] w_ex0_index;
pipe_ctrl_t                              w_ex0_pipe_ctrl;

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

always_comb begin
  r_ex0_issue = rv0_issue;
  w_ex0_index = rv0_index;
end

decoder_csu_ctrl u_pipe_ctrl (
  .inst(r_ex0_issue.inst),
  .op         (w_ex0_pipe_ctrl.op        ),
  .is_ret     (w_ex0_pipe_ctrl.is_ret    ),
  .is_ecall   (w_ex0_pipe_ctrl.is_ecall  ),
  .is_ebreak  (w_ex0_pipe_ctrl.is_ebreak ),
  .is_fence   (w_ex0_pipe_ctrl.is_fence  ),
  .is_fence_i (w_ex0_pipe_ctrl.is_fence_i)
);

assign ex1_regread_rs1.valid = r_ex1_issue.valid & r_ex1_issue.rs1_valid;
assign ex1_regread_rs1.rnid  = r_ex1_issue.rs1_rnid;

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

assign o_ex1_early_wr.valid = r_ex1_issue.valid & r_ex1_issue.rd_valid;
assign o_ex1_early_wr.rd_rnid = r_ex1_issue.rd_rnid;
assign o_ex1_early_wr.rd_type = msrh_pkg::GPR;
assign o_ex1_early_wr.may_mispred = 1'b0;

generate
  for (genvar tgt_idx = 0; tgt_idx < msrh_pkg::REL_BUS_SIZE; tgt_idx++) begin : rs_tgt_loop
    assign w_ex2_rs1_fwd_valid[tgt_idx] = r_ex2_issue.rs1_valid & ex1_i_phy_wr[tgt_idx].valid &
                                          (r_ex2_issue.rs1_type == ex1_i_phy_wr[tgt_idx].rd_type) &
                                          (r_ex2_issue.rs1_rnid == ex1_i_phy_wr[tgt_idx].rd_rnid) &
                                          (r_ex2_issue.rs1_rnid != 'h0);   // GPR[x0] always zero

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

assign w_ex2_rs1_selected_data = |w_ex2_rs1_fwd_valid ? w_ex2_rs1_fwd_data : r_ex2_rs1_data;

assign read_if.valid = r_ex2_issue.valid;
assign read_if.addr  = r_ex2_issue.inst[31:20];

always_ff @(posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_ex3_result    <= 'h0;
    r_ex3_index     <= 'h0;
    r_ex3_issue     <= 'h0;
    r_ex3_pipe_ctrl <= 'h0;
  end else begin
    r_ex3_issue     <= r_ex2_issue;
    r_ex3_index     <= r_ex2_index;
    r_ex3_pipe_ctrl <= r_ex2_pipe_ctrl;

    case (r_ex2_pipe_ctrl.op)
      OP_RW: r_ex3_result <= w_ex2_rs1_selected_data;
      OP_RS: r_ex3_result <= read_if.data | w_ex2_rs1_selected_data;
      OP_RC: r_ex3_result <= read_if.data & ~w_ex2_rs1_selected_data;
      OP__ : r_ex3_result <= 'h0;
      default : r_ex3_result <= 'h0;
    endcase // case (r_ex2_pipe_ctrl.op)

    r_ex3_csr_rd_data <= read_if.data;
  end
end

assign o_ex3_phy_wr.valid   = r_ex3_issue.valid;
assign o_ex3_phy_wr.rd_rnid = r_ex3_issue.rd_rnid;
assign o_ex3_phy_wr.rd_type = r_ex3_issue.rd_type;
assign o_ex3_phy_wr.rd_data = r_ex3_csr_rd_data;

assign ex3_done_if.done       = r_ex3_issue.valid;
assign ex3_done_if.index_oh   = r_ex3_index;
assign ex3_done_if.except_valid  = r_ex3_pipe_ctrl.is_ret | r_ex3_pipe_ctrl.is_ecall;
assign ex3_done_if.except_type = r_ex3_pipe_ctrl.is_ret ? msrh_pkg::MRET :  // r_ex3_pipe_ctrl.is_ret
                                msrh_pkg::ECALL_M;                         // r_ex3_pipe_ctrl.is_ecall

assign write_if.valid = r_ex3_issue.valid;
assign write_if.addr  = r_ex3_issue.inst[31:20];
assign write_if.data  = r_ex3_result;

endmodule // msrh_csu_pipe
