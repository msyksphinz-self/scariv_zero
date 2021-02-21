module msrh_alu_pipe
  #(
    parameter RV_ENTRY_SIZE = 32
    )
(
    input logic i_clk,
    input logic i_reset_n,

    input msrh_pkg::issue_t rv0_issue,
    input logic [RV_ENTRY_SIZE-1:0] rv0_index,
    input msrh_pkg::target_t ex1_target_in[msrh_pkg::TGT_BUS_SIZE],

    regread_if.master ex0_regread_rs1,
    regread_if.master ex0_regread_rs2,

    output msrh_pkg::release_t ex1_release_out,
    output msrh_pkg::target_t  ex3_target_out,

 output logic o_ex3_done,
 output logic [RV_ENTRY_SIZE-1: 0] o_ex3_index

);

  typedef struct packed {
    logic [2:0] op;
    logic imm;
    logic size;
    logic sign;
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

  // always_ff @(posedge i_clk, negedge i_reset_n) begin
  //   if (!i_reset_n) begin
  //     r_ex0_issue <= 'h0;
  //   end else begin
  //     r_ex0_issue <= rv0_issue;
  //   end
  // end

always_comb begin
  r_ex0_issue = rv0_issue;
  w_ex0_index = rv0_index;
end

  decoder_inst_ctrl u_pipe_ctrl (
      .inst(r_ex0_issue.inst),
      .op  (w_ex0_pipe_ctrl.op),
      .imm (w_ex0_pipe_ctrl.imm),
      .size(w_ex0_pipe_ctrl.size),
      .sign(w_ex0_pipe_ctrl.sign)
  );

  assign ex0_regread_rs1.valid = r_ex0_issue.valid & r_ex0_issue.rs1_valid;
  assign ex0_regread_rs1.rnid = r_ex0_issue.rs1_rnid;

  assign ex0_regread_rs2.valid = r_ex0_issue.valid & r_ex0_issue.rs2_valid;
  assign ex0_regread_rs2.rnid = r_ex0_issue.rs2_rnid;

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

  assign ex1_release_out.valid = r_ex1_issue.valid & r_ex1_issue.rd_valid;
  assign ex1_release_out.rd_rnid = r_ex1_issue.rd_rnid;
  assign ex1_release_out.rd_type = msrh_pkg::GPR;

  generate
    for (genvar tgt_idx = 0; tgt_idx < msrh_pkg::REL_BUS_SIZE; tgt_idx++) begin : rs_tgt_loop
      assign w_ex2_rs1_fwd_valid[tgt_idx] = r_ex2_issue.rs1_valid & ex1_target_in[tgt_idx].valid &
                                           (r_ex2_issue.rs1_type == ex1_target_in[tgt_idx].rd_type) &
                                           (r_ex2_issue.rs1_rnid == ex1_target_in[tgt_idx].rd_rnid);

      assign w_ex2_rs2_fwd_valid[tgt_idx] = r_ex2_issue.rs2_valid & ex1_target_in[tgt_idx].valid &
                                           (r_ex2_issue.rs2_type == ex1_target_in[tgt_idx].rd_type) &
                                           (r_ex2_issue.rs2_rnid == ex1_target_in[tgt_idx].rd_rnid);
      assign w_ex2_tgt_data[tgt_idx] = ex1_target_in[tgt_idx].rd_data;
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
      r_ex2_rs1_data <= ex0_regread_rs1.data;
      r_ex2_rs2_data <= r_ex1_pipe_ctrl.imm ? {{(riscv_pkg::XLEN_W-12){r_ex1_issue.inst[31]}}, r_ex1_issue.inst[31:20]} :
                        ex0_regread_rs2.data;

      r_ex2_issue <= r_ex1_issue;
      r_ex2_index <= r_ex1_index;
      r_ex2_pipe_ctrl <= r_ex1_pipe_ctrl;
    end
  end

assign w_ex2_rs1_selected_data = |w_ex2_rs1_fwd_valid ? w_ex2_rs1_fwd_data : r_ex2_rs1_data;
assign w_ex2_rs2_selected_data = |w_ex2_rs2_fwd_valid ? w_ex2_rs2_fwd_data : r_ex2_rs2_data;


  always_ff @(posedge i_clk, negedge i_reset_n) begin
    if (!i_reset_n) begin
      r_ex3_result <= 'h0;
      r_ex3_index <= 'h0;
      r_ex3_issue <= 'h0;
    end else begin
      r_ex3_issue <= r_ex2_issue;
      r_ex3_index <= r_ex2_index;

      case (r_ex2_pipe_ctrl.op)
        3'b001: r_ex3_result <= {{(riscv_pkg::XLEN_W-32){r_ex2_issue.inst[31]}}, r_ex2_issue.inst[31:12], 12'h000};
        3'b010: r_ex3_result <= 'h0;
        3'b011: r_ex3_result <= w_ex2_rs1_selected_data + w_ex2_rs2_selected_data;
        3'b100: r_ex3_result <= w_ex2_rs1_selected_data - w_ex2_rs2_selected_data;
        default : r_ex3_result <= {riscv_pkg::XLEN_W{1'bx}};
      endcase
    end
  end

  assign ex3_target_out.valid = r_ex3_issue.valid & r_ex3_issue.rd_valid;
  assign ex3_target_out.rd_rnid = r_ex3_issue.rd_rnid;
  assign ex3_target_out.rd_type = r_ex3_issue.rd_type;
  assign ex3_target_out.rd_data = r_ex3_result;

assign o_ex3_done = r_ex3_issue.valid;
assign o_ex3_index = r_ex3_index;

endmodule // msrh_alu_pipe
