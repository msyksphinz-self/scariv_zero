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

    output logic o_muldiv_stall,

    regread_if.master ex1_regread_rs1,
    regread_if.master ex1_regread_rs2,

    input msrh_pkg::mispred_t i_mispred_lsu[msrh_conf_pkg::LSU_INST_NUM],

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

  logic                                    w_ex1_rs1_lsu_mispred;
  logic                                    w_ex1_rs2_lsu_mispred;
  logic                                    w_ex1_rs1_mispred;
  logic                                    w_ex1_rs2_mispred;

  pipe_ctrl_t                              r_ex2_pipe_ctrl;
  msrh_pkg::issue_t                         r_ex2_issue;
  logic [RV_ENTRY_SIZE-1: 0] r_ex2_index;
  logic            [riscv_pkg::XLEN_W-1:0] r_ex2_rs1_data;
  logic            [riscv_pkg::XLEN_W-1:0] r_ex2_rs2_data;
  logic                                    r_ex2_wr_valid;

  msrh_pkg::issue_t                        r_ex3_issue;
  logic            [riscv_pkg::XLEN_W-1:0] r_ex3_result;
  logic [RV_ENTRY_SIZE-1: 0] r_ex3_index;
  logic                                    r_ex3_wr_valid;

// ----------------------
// Multiplier Variables
// ----------------------
localparam MUL_UNROLL = 8;
localparam MUL_PIPE_MAX = riscv_pkg::XLEN_W/MUL_UNROLL;

logic                                      w_mul_stall_pipe;
logic                                      w_ex1_muldiv_valid;
logic                                      w_ex1_muldiv_type_valid;
logic                                      w_muldiv_res_valid;
logic [riscv_pkg::XLEN_W-1: 0]             w_muldiv_res;

logic                                      r_ex2_muldiv_valid;

logic                                      r_ex3_muldiv_valid;

logic [msrh_pkg::RNID_W-1: 0]              w_muldiv_rd_rnid;
msrh_pkg::reg_t                            w_muldiv_rd_type;
logic [RV_ENTRY_SIZE-1: 0]                 w_muldiv_index_oh;

logic                                      w_ex0_div_stall;
logic                                      r_ex1_div_stall;
logic                                      r_ex2_div_stall;
logic                                      w_ex3_muldiv_stall;

assign o_muldiv_stall = w_ex3_muldiv_stall | r_ex2_div_stall | r_ex1_div_stall;


always_comb begin
  r_ex0_issue = rv0_issue;
  w_ex0_index = rv0_index;
end

// ---------------------
// EX0
// ---------------------

decoder_alu_ctrl u_pipe_ctrl (
    .inst(r_ex0_issue.inst),
    .op  (w_ex0_pipe_ctrl.op),
    .imm (w_ex0_pipe_ctrl.imm)
);

assign w_ex0_div_stall = (w_ex0_pipe_ctrl.op == OP_SDIV  ) |
                         (w_ex0_pipe_ctrl.op == OP_UDIV  ) |
                         (w_ex0_pipe_ctrl.op == OP_SREM  ) |
                         (w_ex0_pipe_ctrl.op == OP_UREM  ) |
                         (w_ex0_pipe_ctrl.op == OP_DIVW  ) |
                         (w_ex0_pipe_ctrl.op == OP_DIVUW ) |
                         (w_ex0_pipe_ctrl.op == OP_REMW  ) |
                         (w_ex0_pipe_ctrl.op == OP_REMUW );

// ---------------------
// EX1
// ---------------------

assign ex1_regread_rs1.valid = r_ex1_issue.valid & r_ex1_issue.rs1_valid;
assign ex1_regread_rs1.rnid  = r_ex1_issue.rs1_rnid;

assign ex1_regread_rs2.valid = r_ex1_issue.valid & r_ex1_issue.rs2_valid;
assign ex1_regread_rs2.rnid  = r_ex1_issue.rs2_rnid;

always_ff @(posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_ex1_issue <= 'h0;
    r_ex1_index <= 'h0;
    r_ex1_pipe_ctrl <= 'h0;
    r_ex1_div_stall <= 1'b0;
  end else begin
    r_ex1_issue <= r_ex0_issue;
    r_ex1_index <= w_ex0_index;
    r_ex1_pipe_ctrl <= w_ex0_pipe_ctrl;
    r_ex1_div_stall <= w_ex0_div_stall;
  end
end


select_mispred_bus rs1_mispred_select
(
 .i_entry_rnid (r_ex1_issue.rs1_rnid),
 .i_entry_type (r_ex1_issue.rs1_type),
 .i_mispred    (i_mispred_lsu),

 .o_mispred    (w_ex1_rs1_lsu_mispred)
 );


select_mispred_bus rs2_mispred_select
(
 .i_entry_rnid (r_ex1_issue.rs2_rnid),
 .i_entry_type (r_ex1_issue.rs2_type),
 .i_mispred    (i_mispred_lsu),

 .o_mispred    (w_ex1_rs2_lsu_mispred)
 );

// -----------------------------
// EX1 : Multiplier Control
// -----------------------------
assign w_ex1_muldiv_type_valid = (r_ex1_pipe_ctrl.op == OP_SMUL  ) |
                                 (r_ex1_pipe_ctrl.op == OP_MULH  ) |
                                 (r_ex1_pipe_ctrl.op == OP_MULHSU) |
                                 (r_ex1_pipe_ctrl.op == OP_MULHU ) |
                                 (r_ex1_pipe_ctrl.op == OP_SDIV  ) |
                                 (r_ex1_pipe_ctrl.op == OP_UDIV  ) |
                                 (r_ex1_pipe_ctrl.op == OP_SREM  ) |
                                 (r_ex1_pipe_ctrl.op == OP_UREM  ) |
                                 (r_ex1_pipe_ctrl.op == OP_MULW  ) |
                                 (r_ex1_pipe_ctrl.op == OP_DIVW  ) |
                                 (r_ex1_pipe_ctrl.op == OP_DIVUW ) |
                                 (r_ex1_pipe_ctrl.op == OP_REMW  ) |
                                 (r_ex1_pipe_ctrl.op == OP_REMUW );

assign w_ex1_muldiv_valid = r_ex1_issue.valid & w_ex1_muldiv_type_valid;

assign w_ex1_rs1_mispred = r_ex1_issue.rs1_valid & r_ex1_issue.rs1_pred_ready ? w_ex1_rs1_lsu_mispred : 1'b0;
assign w_ex1_rs2_mispred = r_ex1_issue.rs2_valid & r_ex1_issue.rs2_pred_ready ? w_ex1_rs2_lsu_mispred : 1'b0;

assign o_ex1_early_wr.valid = r_ex1_issue.valid & r_ex1_issue.rd_valid &
                              ~w_ex1_rs1_mispred & ~w_ex1_rs2_mispred &
                              ~w_ex1_muldiv_valid;

assign o_ex1_early_wr.rd_rnid = r_ex1_issue.rd_rnid;
assign o_ex1_early_wr.rd_type = msrh_pkg::GPR;
assign o_ex1_early_wr.may_mispred = 1'b0;

// -----------------------------
// EX2 Stage
// -----------------------------

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
    .T(logic[riscv_pkg::XLEN_W-1:0]),
    .WORDS(msrh_pkg::TGT_BUS_SIZE)
) u_rs1_data_select (
    .i_oh(w_ex2_rs1_fwd_valid),
    .i_data(w_ex2_tgt_data),
    .o_selected(w_ex2_rs1_fwd_data)
);

bit_oh_or #(
    .T(logic[riscv_pkg::XLEN_W-1:0]),
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

    r_ex2_wr_valid <= 1'b0;

    r_ex2_muldiv_valid <= 1'b0;

    r_ex2_div_stall <= 1'b0;
  end else begin
    r_ex2_rs1_data <= ex1_regread_rs1.data;
    r_ex2_rs2_data <= r_ex1_pipe_ctrl.imm == IMM_S  ? {{(riscv_pkg::XLEN_W-12){r_ex1_issue.inst[31]}}, r_ex1_issue.inst[31:20]} :
                      r_ex1_pipe_ctrl.imm == IMM_I  ? {{(riscv_pkg::XLEN_W-12){r_ex1_issue.inst[31]}}, r_ex1_issue.inst[31:20]} :
                      r_ex1_pipe_ctrl.imm == IMM_SH ? {{(riscv_pkg::XLEN_W-$clog2(riscv_pkg::XLEN_W)){1'b0}}, r_ex1_issue.inst[20+:$clog2(riscv_pkg::XLEN_W)]} :
                      ex1_regread_rs2.data;
    r_ex2_issue <= r_ex1_issue;
    r_ex2_index <= r_ex1_index;
    r_ex2_pipe_ctrl <= r_ex1_pipe_ctrl;

    r_ex2_wr_valid <= o_ex1_early_wr.valid;

    r_ex2_muldiv_valid <= w_ex1_muldiv_valid & (~w_ex1_rs1_mispred & ~w_ex1_rs2_mispred);

    r_ex2_div_stall <= r_ex1_div_stall;
  end
end

assign w_ex2_rs1_selected_data = |w_ex2_rs1_fwd_valid ? w_ex2_rs1_fwd_data : r_ex2_rs1_data;
assign w_ex2_rs2_selected_data = |w_ex2_rs2_fwd_valid ? w_ex2_rs2_fwd_data : r_ex2_rs2_data;

logic signed [31: 0] tmp_ex2_result_d;
logic signed [31: 0] w_ex2_rs1_selected_data_32;
logic signed [31: 0] w_ex2_rs1_selected_data_sra;
assign w_ex2_rs1_selected_data_32 = w_ex2_rs1_selected_data[31:0];
assign tmp_ex2_result_d = r_ex2_pipe_ctrl.op == OP_SIGN_ADD_32 ? w_ex2_rs1_selected_data_32 +   w_ex2_rs2_selected_data[31:0] :
                          r_ex2_pipe_ctrl.op == OP_SIGN_SUB_32 ? w_ex2_rs1_selected_data_32 -   w_ex2_rs2_selected_data[31:0] :
                          r_ex2_pipe_ctrl.op == OP_SLL_32      ? w_ex2_rs1_selected_data_32 <<  w_ex2_rs2_selected_data[ 4:0] :
                          r_ex2_pipe_ctrl.op == OP_SRL_32      ? w_ex2_rs1_selected_data_32 >>  w_ex2_rs2_selected_data[ 4:0] :
                          r_ex2_pipe_ctrl.op == OP_SRA_32      ? w_ex2_rs1_selected_data_sra :
                          'h0;
// Memo: I don't know why but if this sentence is integrated into above, test pattern fail.
assign w_ex2_rs1_selected_data_sra = $signed(w_ex2_rs1_selected_data_32) >>> w_ex2_rs2_selected_data[ 4:0];

always_ff @(posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_ex3_result <= 'h0;
    r_ex3_index <= 'h0;
    r_ex3_issue <= 'h0;

    r_ex3_wr_valid <= 1'b0;
  end else begin
    r_ex3_issue <= r_ex2_issue;
    r_ex3_index <= r_ex2_index;

    r_ex3_wr_valid <= r_ex2_wr_valid;

    r_ex3_muldiv_valid <= r_ex2_muldiv_valid;

    case (r_ex2_pipe_ctrl.op)
      OP_SIGN_LUI: r_ex3_result <= {{(riscv_pkg::XLEN_W-32){r_ex2_issue.inst[31]}}, r_ex2_issue.inst[31:12], 12'h000};
      OP_SIGN_AUIPC:  r_ex3_result <= {{(riscv_pkg::XLEN_W-riscv_pkg::VADDR_W){r_ex2_issue.pc_addr[riscv_pkg::VADDR_W-1]}},
                                       r_ex2_issue.pc_addr} +
                                      {{(riscv_pkg::XLEN_W-32){r_ex2_issue.inst[31]}}, r_ex2_issue.inst[31:12], 12'h000};
      OP_SIGN_ADD:    r_ex3_result <= w_ex2_rs1_selected_data + w_ex2_rs2_selected_data;
      OP_SIGN_SUB:    r_ex3_result <= w_ex2_rs1_selected_data - w_ex2_rs2_selected_data;
      OP_SIGN_ADD_32, OP_SIGN_SUB_32, OP_SLL_32, OP_SRL_32, OP_SRA_32:
        r_ex3_result <= {{(riscv_pkg::XLEN_W-32){tmp_ex2_result_d[31]}}, tmp_ex2_result_d[31: 0]};
      OP_XOR:         r_ex3_result <= w_ex2_rs1_selected_data ^   w_ex2_rs2_selected_data;
      OP_OR :         r_ex3_result <= w_ex2_rs1_selected_data |   w_ex2_rs2_selected_data;
      OP_AND:         r_ex3_result <= w_ex2_rs1_selected_data &   w_ex2_rs2_selected_data;
      OP_SLL:         r_ex3_result <= w_ex2_rs1_selected_data <<  w_ex2_rs2_selected_data[$clog2(riscv_pkg::XLEN_W)-1: 0];
      OP_SRL:         r_ex3_result <= w_ex2_rs1_selected_data >>  w_ex2_rs2_selected_data[$clog2(riscv_pkg::XLEN_W)-1: 0];
      OP_SRA:         r_ex3_result <= $signed(w_ex2_rs1_selected_data) >>> w_ex2_rs2_selected_data[$clog2(riscv_pkg::XLEN_W)-1: 0];
      /* verilator lint_off WIDTH */
      OP_SIGN_SLT:    r_ex3_result <= $signed(w_ex2_rs1_selected_data) < $signed(w_ex2_rs2_selected_data);
      OP_UNSIGN_SLT:  r_ex3_result <= w_ex2_rs1_selected_data < w_ex2_rs2_selected_data;
      default : r_ex3_result <= {riscv_pkg::XLEN_W{1'b0}};
    endcase // case (r_ex2_pipe_ctrl.op)
  end
end

// ----------------------
// Multiplier Pipeline
// ----------------------
msrh_muldiv_pipe
  #(
    .RV_ENTRY_SIZE (RV_ENTRY_SIZE),
    .MUL_UNROLL(MUL_UNROLL)
    )
u_msrh_muldiv_pipe
  (
   .i_clk    (i_clk),
   .i_reset_n(i_reset_n),

   .i_valid  (r_ex2_muldiv_valid),
   .i_op     (r_ex2_pipe_ctrl.op),

   .i_rd_rnid  (r_ex2_issue.rd_rnid),
   .i_rd_type  (r_ex2_issue.rd_type),
   .i_index_oh (r_ex2_index        ),

   .i_rs1 (w_ex2_rs1_selected_data),
   .i_rs2 (w_ex2_rs2_selected_data),

   .o_stall (w_ex3_muldiv_stall),
   .o_valid (w_muldiv_res_valid),
   .o_res   (w_muldiv_res),

   .o_rd_rnid  (w_muldiv_rd_rnid ),
   .o_rd_type  (w_muldiv_rd_type ),
   .o_index_oh (w_muldiv_index_oh)
   );

always_comb begin
  if (w_muldiv_res_valid) begin
    o_ex3_phy_wr.valid   = 1'b1;
    o_ex3_phy_wr.rd_rnid = w_muldiv_rd_rnid;
    o_ex3_phy_wr.rd_type = w_muldiv_rd_type;
    o_ex3_phy_wr.rd_data = w_muldiv_res;

    ex3_done_if.done          = w_muldiv_res_valid;
    ex3_done_if.index_oh      = w_muldiv_index_oh;
    ex3_done_if.except_valid  = 1'b0;
    ex3_done_if.except_type   = msrh_pkg::except_t'('h0);
  end else begin
    o_ex3_phy_wr.valid   = r_ex3_wr_valid;
    o_ex3_phy_wr.rd_rnid = r_ex3_issue.rd_rnid;
    o_ex3_phy_wr.rd_type = r_ex3_issue.rd_type;
    o_ex3_phy_wr.rd_data = r_ex3_result;

    ex3_done_if.done         = r_ex3_issue.valid & ~r_ex3_muldiv_valid;
    ex3_done_if.index_oh     = r_ex3_index;
    ex3_done_if.except_valid = 1'b0;
    ex3_done_if.except_type  = msrh_pkg::except_t'('h0);
  end // else: !if(w_muldiv_res_valid)
end // always_comb


`ifdef SIMULATION
always_ff @(negedge i_clk, negedge i_reset_n) begin
  if (i_reset_n) begin
    if (w_muldiv_res_valid & r_ex3_issue.valid) begin
      $fatal(0, "Mul/Div Pipeline and ALU integer output valid signal must not be asserted in same time.");
    end
  end
end
`endif // SIMULATION

endmodule // msrh_alu_pipe
