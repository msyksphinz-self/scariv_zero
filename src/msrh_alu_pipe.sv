module msrh_alu_pipe
  import decoder_alu_ctrl_pkg::*;
#(
  parameter RV_ENTRY_SIZE = 32
  )
(
    input logic i_clk,
    input logic i_reset_n,

    input msrh_pkg::issue_t rv0_issue,
    input logic [RV_ENTRY_SIZE-1:0] rv0_index,
    input msrh_pkg::phy_wr_t ex1_i_phy_wr[msrh_pkg::TGT_BUS_SIZE],

    regread_if.master ex1_regread_rs1,
    regread_if.master ex1_regread_rs2,

    output msrh_pkg::early_wr_t o_ex1_early_wr,
    output msrh_pkg::phy_wr_t   o_ex3_phy_wr,

  done_if.master ex3_done_if
);

  typedef struct packed {
    op_t  op;
    imm_t imm;
  } pipe_ctrl_t;

  msrh_pkg::issue_t                         r_ex0_issue;
  logic [RV_ENTRY_SIZE-1: 0] w_ex0_index;
  pipe_ctrl_t                              w_ex0_pipe_ctrl;

  pipe_ctrl_t                              r_ex1_pipe_ctrl;
  msrh_pkg::issue_t                         r_ex1_issue;
  logic [RV_ENTRY_SIZE-1: 0] r_ex1_index;

  logic [msrh_pkg::TGT_BUS_SIZE-1:0] w_ex2_rs1_fwd_valid;
  logic [msrh_pkg::TGT_BUS_SIZE-1:0] w_ex2_rs2_fwd_valid;
  logic            [riscv_pkg::XLEN_W-1:0] w_ex2_tgt_data          [msrh_pkg::TGT_BUS_SIZE];
  logic            [riscv_pkg::XLEN_W-1:0] w_ex2_rs1_fwd_data;
  logic            [riscv_pkg::XLEN_W-1:0] w_ex2_rs2_fwd_data;

  logic            [riscv_pkg::XLEN_W-1:0] w_ex2_rs1_selected_data;
  logic            [riscv_pkg::XLEN_W-1:0] w_ex2_rs2_selected_data;

  pipe_ctrl_t                              r_ex2_pipe_ctrl;
  msrh_pkg::issue_t                         r_ex2_issue;
  logic [RV_ENTRY_SIZE-1: 0] r_ex2_index;
  logic            [riscv_pkg::XLEN_W-1:0] r_ex2_rs1_data;
  logic            [riscv_pkg::XLEN_W-1:0] r_ex2_rs2_data;

  msrh_pkg::issue_t                         r_ex3_issue;
  logic            [riscv_pkg::XLEN_W-1:0] r_ex3_result;
  logic [RV_ENTRY_SIZE-1: 0] r_ex3_index;

always_comb begin
  r_ex0_issue = rv0_issue;
  w_ex0_index = rv0_index;
end

  decoder_alu_ctrl u_pipe_ctrl (
      .inst(r_ex0_issue.inst),
      .op  (w_ex0_pipe_ctrl.op),
      .imm (w_ex0_pipe_ctrl.imm)
  );

  assign ex1_regread_rs1.valid = r_ex1_issue.valid & r_ex1_issue.rs1_valid;
  assign ex1_regread_rs1.rnid  = r_ex1_issue.rs1_rnid;

  assign ex1_regread_rs2.valid = r_ex1_issue.valid & r_ex1_issue.rs2_valid;
  assign ex1_regread_rs2.rnid  = r_ex1_issue.rs2_rnid;

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

  generate
    for (genvar tgt_idx = 0; tgt_idx < msrh_pkg::REL_BUS_SIZE; tgt_idx++) begin : rs_tgt_loop
      assign w_ex2_rs1_fwd_valid[tgt_idx] = r_ex2_issue.rs1_valid & ex1_i_phy_wr[tgt_idx].valid &
                                            (r_ex2_issue.rs1_type == ex1_i_phy_wr[tgt_idx].rd_type) &
                                            (r_ex2_issue.rs1_rnid == ex1_i_phy_wr[tgt_idx].rd_rnid) &
                                            (r_ex2_issue.rs1_rnid != 'h0);   // GPR[x0] always zero


      assign w_ex2_rs2_fwd_valid[tgt_idx] = r_ex2_issue.rs2_valid & ex1_i_phy_wr[tgt_idx].valid &
                                            (r_ex2_issue.rs2_type == ex1_i_phy_wr[tgt_idx].rd_type) &
                                            (r_ex2_issue.rs2_rnid == ex1_i_phy_wr[tgt_idx].rd_rnid) &
                                            (r_ex2_issue.rs2_rnid != 'h0);   // GPR[x0] always zero
      assign w_ex2_tgt_data[tgt_idx] = ex1_i_phy_wr[tgt_idx].rd_data;
    end
  endgenerate

  bit_oh_or #(
      .WIDTH(riscv_pkg::XLEN_W),
      .WORDS(msrh_pkg::TGT_BUS_SIZE)
  ) u_rs1_data_select (
      .i_oh(w_ex2_rs1_fwd_valid),
      .i_data(w_ex2_tgt_data),
      .o_selected(w_ex2_rs1_fwd_data)
  );

  bit_oh_or #(
      .WIDTH(riscv_pkg::XLEN_W),
      .WORDS(msrh_pkg::TGT_BUS_SIZE)
  ) u_rs2_data_select (
      .i_oh(w_ex2_rs2_fwd_valid),
      .i_data(w_ex2_tgt_data),
      .o_selected(w_ex2_rs2_fwd_data)
  );

  always_ff @(posedge i_clk, negedge i_reset_n) begin
    if (!i_reset_n) begin
      r_ex2_rs1_data <= 'h0;
      r_ex2_rs2_data <= 'h0;

      r_ex2_issue <= 'h0;
      r_ex2_index <= 'h0;
      r_ex2_pipe_ctrl <= 'h0;
    end else begin
      r_ex2_rs1_data <= ex1_regread_rs1.data;
      r_ex2_rs2_data <= r_ex1_pipe_ctrl.imm == IMM_S  ? {{(riscv_pkg::XLEN_W-12){r_ex1_issue.inst[31]}}, r_ex1_issue.inst[31:20]} :
                        r_ex1_pipe_ctrl.imm == IMM_SH ? {{(riscv_pkg::XLEN_W-5){1'b0}}, r_ex1_issue.inst[24:20]} :
                        ex1_regread_rs2.data;
      r_ex2_issue <= r_ex1_issue;
      r_ex2_index <= r_ex1_index;
      r_ex2_pipe_ctrl <= r_ex1_pipe_ctrl;
    end
  end

assign w_ex2_rs1_selected_data = |w_ex2_rs1_fwd_valid ? w_ex2_rs1_fwd_data : r_ex2_rs1_data;
assign w_ex2_rs2_selected_data = |w_ex2_rs2_fwd_valid ? w_ex2_rs2_fwd_data : r_ex2_rs2_data;

logic [31: 0] tmp_ex2_result_d;
assign tmp_ex2_result_d = r_ex2_pipe_ctrl.op == OP_SIGN_ADD_32 ? w_ex2_rs1_selected_data[31:0] +   w_ex2_rs2_selected_data[31:0] :
                          r_ex2_pipe_ctrl.op == OP_SLL_32      ? w_ex2_rs1_selected_data[31:0] <<  w_ex2_rs2_selected_data[ 4:0] :
                          r_ex2_pipe_ctrl.op == OP_SRL_32      ? w_ex2_rs1_selected_data[31:0] >>  w_ex2_rs2_selected_data[ 4:0] :
                          r_ex2_pipe_ctrl.op == OP_SRA_32      ? w_ex2_rs1_selected_data[31:0] >>> w_ex2_rs2_selected_data[ 4:0] :
                          'h0;

always_ff @(posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_ex3_result <= 'h0;
    r_ex3_index <= 'h0;
    r_ex3_issue <= 'h0;
  end else begin
    r_ex3_issue <= r_ex2_issue;
    r_ex3_index <= r_ex2_index;

    case (r_ex2_pipe_ctrl.op)
      OP_SIGN_LUI: r_ex3_result <= {{(riscv_pkg::XLEN_W-32){r_ex2_issue.inst[31]}}, r_ex2_issue.inst[31:12], 12'h000};
      /* verilator lint_off WIDTH */
      OP_SIGN_AUIPC:  r_ex3_result <= r_ex2_issue.pc_addr +
                                      {{(riscv_pkg::XLEN_W-32){r_ex2_issue.inst[31]}}, r_ex2_issue.inst[31:12], 12'h000};
      OP_SIGN_ADD:    r_ex3_result <= w_ex2_rs1_selected_data + w_ex2_rs2_selected_data;
      OP_SIGN_SUB:    r_ex3_result <= w_ex2_rs1_selected_data - w_ex2_rs2_selected_data;
      OP_SIGN_ADD_32, OP_SRL_32, OP_SRA_32:
        r_ex3_result <= {{(riscv_pkg::XLEN_W-32){tmp_ex2_result_d[31]}}, tmp_ex2_result_d[31: 0]};
      OP_SLL:         r_ex3_result <= w_ex2_rs1_selected_data <<  w_ex2_rs2_selected_data[$clog2(riscv_pkg::XLEN_W)-1: 0];
      OP_SRL:         r_ex3_result <= w_ex2_rs1_selected_data >>  w_ex2_rs2_selected_data[$clog2(riscv_pkg::XLEN_W)-1: 0];
      OP_SRA:         r_ex3_result <= w_ex2_rs1_selected_data >>> w_ex2_rs2_selected_data[$clog2(riscv_pkg::XLEN_W)-1: 0];
      default : r_ex3_result <= {riscv_pkg::XLEN_W{1'b0}};
    endcase // case (r_ex2_pipe_ctrl.op)
  end
end

assign o_ex3_phy_wr.valid = r_ex3_issue.valid & r_ex3_issue.rd_valid;
assign o_ex3_phy_wr.rd_rnid = r_ex3_issue.rd_rnid;
assign o_ex3_phy_wr.rd_type = r_ex3_issue.rd_type;
assign o_ex3_phy_wr.rd_data = r_ex3_result;

assign ex3_done_if.done     = r_ex3_issue.valid;
assign ex3_done_if.index_oh = r_ex3_index;

endmodule // msrh_alu_pipe
