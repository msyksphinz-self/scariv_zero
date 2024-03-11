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

module scariv_alu_pipe
  import decoder_alu_ctrl_pkg::*;
#(
  parameter RV_ENTRY_SIZE = 32
  )
(
    input logic i_clk,
    input logic i_reset_n,

    // Commit notification
    commit_if.monitor commit_if,
    br_upd_if.slave              br_upd_if,

    input scariv_alu_pkg::issue_t   ex0_issue,
    input logic [RV_ENTRY_SIZE-1:0] ex0_index,
    phy_wr_if.slave ex1_phy_wr_if[scariv_pkg::TGT_BUS_SIZE],

    output logic o_muldiv_stall,

    regread_if.master ex0_regread_rs1,
    regread_if.master ex0_regread_rs2,

    lsu_mispred_if.slave mispred_lsu_if[scariv_conf_pkg::LSU_INST_NUM],

    early_wr_if.master ex0_early_wr_if,
    phy_wr_if.master   ex2_phy_wr_if,

    done_report_if.master done_report_if
);

typedef struct packed {
  op_t  op;
  imm_t imm;
} pipe_ctrl_t;

scariv_alu_pkg::issue_t    w_ex0_issue;
logic [RV_ENTRY_SIZE-1: 0] w_ex0_index;
pipe_ctrl_t                w_ex0_pipe_ctrl;

logic                      w_ex0_rs1_lsu_mispred;
logic                      w_ex0_rs2_lsu_mispred;
logic                      w_ex0_rs1_mispred;
logic                      w_ex0_rs2_mispred;

riscv_pkg::xlen_t                    w_ex0_rs_fwd_data[2];


pipe_ctrl_t                r_ex1_pipe_ctrl;
scariv_alu_pkg::issue_t    r_ex1_issue;
scariv_alu_pkg::issue_t    w_ex1_issue_next;
logic [RV_ENTRY_SIZE-1: 0] r_ex1_index;
logic                      w_ex1_commit_flush;
logic                      w_ex1_br_flush;
logic                      w_ex1_flush;

riscv_pkg::xlen_t w_ex1_tgt_data      [scariv_pkg::TGT_BUS_SIZE];
riscv_pkg::xlen_t w_ex1_rs_fwd_data[2];

riscv_pkg::xlen_t w_ex1_rs1_selected_data;
riscv_pkg::xlen_t w_ex1_rs2_selected_data;

logic                              r_ex1_wr_valid;

logic                              w_ex1_bitmanip_valid;
riscv_pkg::xlen_t                  w_ex1_bitmanip_result;
logic                              w_ex1_zicond_valid;
riscv_pkg::xlen_t                  w_ex1_zicond_result;
riscv_pkg::xlen_t                  r_ex1_rs1_data;
riscv_pkg::xlen_t                  r_ex1_rs2_data;
logic                              r_ex1_rs2_imm_valid;

pipe_ctrl_t                        r_ex2_pipe_ctrl;
scariv_alu_pkg::issue_t            r_ex2_issue;
scariv_alu_pkg::issue_t            w_ex2_issue_next;
logic [RV_ENTRY_SIZE-1: 0]         r_ex2_index;

logic                              r_ex2_wr_valid;
logic                              w_ex2_muldiv_stall;
riscv_pkg::xlen_t                  r_ex2_result;

// ----------------------
// Multiplier Variables
// ----------------------
localparam MUL_UNROLL = 8;
localparam MUL_PIPE_MAX = riscv_pkg::XLEN_W/MUL_UNROLL;

logic                                      w_mul_stall_pipe;
logic                                      w_ex0_muldiv_valid;
logic                                      w_ex0_muldiv_type_valid;
logic                                      w_muldiv_res_valid;
scariv_pkg::cmt_id_t                       w_muldiv_res_cmt_id;
scariv_pkg::grp_id_t                       w_muldiv_res_grp_id;
riscv_pkg::xlen_t                          w_muldiv_res;

logic                                      r_ex1_muldiv_valid;
logic                                      r_ex2_muldiv_valid;

scariv_pkg::rnid_t                         w_muldiv_rd_rnid;
scariv_pkg::reg_t                          w_muldiv_rd_type;
logic [RV_ENTRY_SIZE-1: 0]                 w_muldiv_index_oh;

logic                                      w_ex0_div_stall;
logic                                      r_ex1_div_stall;
logic                                      r_ex2_div_stall;

assign o_muldiv_stall = w_ex2_muldiv_stall | r_ex1_div_stall;


logic                                      w_ex0_commit_flush;
logic                                      w_ex0_br_flush;
logic                                      w_ex0_flush;
assign w_ex0_commit_flush = scariv_pkg::is_flushed_commit(commit_if.commit_valid, commit_if.payload);
assign w_ex0_br_flush     = scariv_pkg::is_br_flush_target(w_ex0_issue.cmt_id, w_ex0_issue.grp_id, br_upd_if.cmt_id, br_upd_if.grp_id,
                                                          br_upd_if.dead, br_upd_if.mispredict) & br_upd_if.update;
assign w_ex0_flush = w_ex0_commit_flush | w_ex0_br_flush;

always_comb begin
  w_ex0_issue = ex0_issue;
  w_ex0_index = ex0_index;
end

// ---------------------
// EX0
// ---------------------

decoder_alu_ctrl u_pipe_ctrl (
    .inst(w_ex0_issue.inst),
    .op  (w_ex0_pipe_ctrl.op),
    .imm (w_ex0_pipe_ctrl.imm)
);

assign ex0_regread_rs1.valid = w_ex0_issue.valid & w_ex0_issue.rd_regs[0].valid;
assign ex0_regread_rs1.rnid  = w_ex0_issue.rd_regs[0].rnid;

assign ex0_regread_rs2.valid = w_ex0_issue.valid & w_ex0_issue.rd_regs[1].valid;
assign ex0_regread_rs2.rnid  = w_ex0_issue.rd_regs[1].rnid;

assign w_ex0_muldiv_type_valid = (w_ex0_pipe_ctrl.op == OP_SMUL  ) |
                                 (w_ex0_pipe_ctrl.op == OP_MULH  ) |
                                 (w_ex0_pipe_ctrl.op == OP_MULHSU) |
                                 (w_ex0_pipe_ctrl.op == OP_MULHU ) |
                                 (w_ex0_pipe_ctrl.op == OP_SDIV  ) |
                                 (w_ex0_pipe_ctrl.op == OP_UDIV  ) |
                                 (w_ex0_pipe_ctrl.op == OP_SREM  ) |
                                 (w_ex0_pipe_ctrl.op == OP_UREM  ) |
`ifdef RV64
                                 (w_ex0_pipe_ctrl.op == OP_MULW  ) |
                                 (w_ex0_pipe_ctrl.op == OP_DIVW  ) |
                                 (w_ex0_pipe_ctrl.op == OP_DIVUW ) |
                                 (w_ex0_pipe_ctrl.op == OP_REMW  ) |
                                 (w_ex0_pipe_ctrl.op == OP_REMUW ) |
`endif // RV64
                                 1'b0;

assign w_ex0_muldiv_valid = w_ex0_issue.valid & w_ex0_muldiv_type_valid & !w_ex0_flush;

assign w_ex0_div_stall = (w_ex0_pipe_ctrl.op == OP_SDIV  ) |
                         (w_ex0_pipe_ctrl.op == OP_UDIV  ) |
                         (w_ex0_pipe_ctrl.op == OP_SREM  ) |
                         (w_ex0_pipe_ctrl.op == OP_UREM  ) |
`ifdef RV64
                         (w_ex0_pipe_ctrl.op == OP_DIVW  ) |
                         (w_ex0_pipe_ctrl.op == OP_DIVUW ) |
                         (w_ex0_pipe_ctrl.op == OP_REMW  ) |
                         (w_ex0_pipe_ctrl.op == OP_REMUW ) |
`endif // RV64
                         1'b0;

assign w_ex0_rs1_mispred = w_ex0_issue.rd_regs[0].valid & w_ex0_issue.rd_regs[0].predict_ready ? w_ex0_rs1_lsu_mispred : 1'b0;
assign w_ex0_rs2_mispred = w_ex0_issue.rd_regs[1].valid & w_ex0_issue.rd_regs[1].predict_ready ? w_ex0_rs2_lsu_mispred : 1'b0;

assign ex0_early_wr_if.valid = w_ex0_issue.valid & w_ex0_issue.wr_reg.valid &
                              ~w_ex0_rs1_mispred & ~w_ex0_rs2_mispred &
                              ~w_ex0_muldiv_valid;

assign ex0_early_wr_if.rd_rnid = w_ex0_issue.wr_reg.rnid;
assign ex0_early_wr_if.rd_type = w_ex0_issue.wr_reg.typ;
assign ex0_early_wr_if.may_mispred = 1'b0;

generate for (genvar rs_idx = 0; rs_idx < 2; rs_idx++) begin : ex0_rs_loop
  riscv_pkg::xlen_t w_ex0_tgt_data [scariv_pkg::TGT_BUS_SIZE];
  for (genvar tgt_idx = 0; tgt_idx < scariv_pkg::TGT_BUS_SIZE; tgt_idx++) begin : rs_tgt_loop
    assign w_ex0_tgt_data[tgt_idx] = ex1_phy_wr_if[tgt_idx].rd_data;
  end
  assign w_ex0_rs_fwd_data [rs_idx] = w_ex0_tgt_data[w_ex0_issue.rd_regs[rs_idx].early_index];
end endgenerate // block: ex1_rs_loop

// ---------------------
// EX1
// ---------------------

assign w_ex1_commit_flush = scariv_pkg::is_flushed_commit(commit_if.commit_valid, commit_if.payload);
assign w_ex1_br_flush     = scariv_pkg::is_br_flush_target(r_ex1_issue.cmt_id, r_ex1_issue.grp_id, br_upd_if.cmt_id, br_upd_if.grp_id,
                                                           br_upd_if.dead, br_upd_if.mispredict) & br_upd_if.update;
assign w_ex1_flush = w_ex1_commit_flush | w_ex1_br_flush;


always_comb begin
  w_ex1_issue_next = w_ex0_issue;
  w_ex1_issue_next.valid = w_ex0_issue.valid & !w_ex0_flush & (~w_ex0_rs1_mispred & ~w_ex0_rs2_mispred);
end

always_ff @(posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_ex1_issue <= 'h0;
    r_ex1_index <= 'h0;
    r_ex1_pipe_ctrl <= 'h0;
    r_ex1_div_stall <= 1'b0;

    r_ex1_rs1_data <= 'h0;
    r_ex1_rs2_data <= 'h0;

    r_ex1_issue <= 'h0;
    r_ex1_index <= 'h0;
    r_ex1_pipe_ctrl <= 'h0;

    r_ex1_wr_valid <= 1'b0;

    r_ex1_muldiv_valid <= 1'b0;

    r_ex1_div_stall <= 1'b0;
  end else begin
    r_ex1_issue <= w_ex1_issue_next;
    r_ex1_index <= w_ex0_index;
    r_ex1_pipe_ctrl <= w_ex0_pipe_ctrl;
    r_ex1_div_stall <= w_ex0_muldiv_valid & w_ex0_div_stall;

    // r_ex1_rs1_data <= w_ex0_issue.rd_regs[0].predict_ready[1] ? w_ex0_rs_fwd_data[0] : ex0_regread_rs1.data;
    // r_ex1_rs2_data <= w_ex0_pipe_ctrl.imm == IMM_S  ? {{(riscv_pkg::XLEN_W-12){w_ex0_issue.inst[31]}}, w_ex0_issue.inst[31:20]} :
    //                   w_ex0_pipe_ctrl.imm == IMM_I  ? {{(riscv_pkg::XLEN_W-12){w_ex0_issue.inst[31]}}, w_ex0_issue.inst[31:20]} :
    //                   w_ex0_pipe_ctrl.imm == IMM_SH ? {{(riscv_pkg::XLEN_W-$clog2(riscv_pkg::XLEN_W)){1'b0}}, w_ex0_issue.inst[20+:$clog2(riscv_pkg::XLEN_W)]} :
    //                   w_ex0_issue.rd_regs[1].predict_ready[1] ? w_ex0_rs_fwd_data[1] : ex0_regread_rs2.data;
    r_ex1_rs1_data <= w_ex0_rs_fwd_data[0];
    r_ex1_rs2_imm_valid  <= w_ex0_pipe_ctrl.imm != IMM__;
    r_ex1_rs2_data <= w_ex0_pipe_ctrl.imm == IMM_S  ? {{(riscv_pkg::XLEN_W-12){w_ex0_issue.inst[31]}}, w_ex0_issue.inst[31:20]} :
                      w_ex0_pipe_ctrl.imm == IMM_I  ? {{(riscv_pkg::XLEN_W-12){w_ex0_issue.inst[31]}}, w_ex0_issue.inst[31:20]} :
                      w_ex0_pipe_ctrl.imm == IMM_SH ? {{(riscv_pkg::XLEN_W-$clog2(riscv_pkg::XLEN_W)){1'b0}}, w_ex0_issue.inst[20+:$clog2(riscv_pkg::XLEN_W)]} :
                      w_ex0_rs_fwd_data[1];

    r_ex1_wr_valid <= ex0_early_wr_if.valid;

    r_ex1_muldiv_valid <= w_ex0_muldiv_valid & (~w_ex0_rs1_mispred & ~w_ex0_rs2_mispred) & !w_ex0_flush;
  end
end


select_mispred_bus rs1_mispred_select
(
 .i_entry_rnid (w_ex0_issue.rd_regs[0].rnid),
 .i_entry_type (w_ex0_issue.rd_regs[0].typ),
 .i_mispred    (mispred_lsu_if),

 .o_mispred    (w_ex0_rs1_lsu_mispred)
 );


select_mispred_bus rs2_mispred_select
(
 .i_entry_rnid (w_ex0_issue.rd_regs[1].rnid),
 .i_entry_type (w_ex0_issue.rd_regs[1].typ),
 .i_mispred    (mispred_lsu_if),

 .o_mispred    (w_ex0_rs2_lsu_mispred)
 );


// -----------------------------
// EX2 Stage
// -----------------------------

generate for (genvar rs_idx = 0; rs_idx < 2; rs_idx++) begin : ex1_rs_loop
  riscv_pkg::xlen_t w_ex1_tgt_data [scariv_pkg::TGT_BUS_SIZE];
  for (genvar tgt_idx = 0; tgt_idx < scariv_pkg::TGT_BUS_SIZE; tgt_idx++) begin : rs_tgt_loop
    assign w_ex1_tgt_data[tgt_idx] = ex1_phy_wr_if[tgt_idx].rd_data;
  end
  assign w_ex1_rs_fwd_data [rs_idx] = w_ex1_tgt_data[r_ex1_issue.rd_regs[rs_idx].early_index];
end endgenerate // block: ex1_rs_loop

assign w_ex1_rs1_selected_data = r_ex1_issue.rd_regs[0].predict_ready[0] ? w_ex1_rs_fwd_data[0] :
                                 r_ex1_issue.rd_regs[0].predict_ready[1] ? r_ex1_rs1_data :
                                 ex0_regread_rs1.data;
assign w_ex1_rs2_selected_data = r_ex1_issue.rd_regs[1].predict_ready[0] ? w_ex1_rs_fwd_data[1] :
                                 r_ex1_rs2_imm_valid | r_ex1_issue.rd_regs[1].predict_ready[1] ? r_ex1_rs2_data :
                                 ex0_regread_rs2.data;

logic signed [31: 0] tmp_ex1_result_d;
logic signed [31: 0] w_ex1_rs1_selected_data_32;
logic signed [31: 0] w_ex1_rs1_selected_data_sra;
assign w_ex1_rs1_selected_data_32 = w_ex1_rs1_selected_data[31:0];
`ifdef RV64
assign tmp_ex1_result_d = r_ex1_pipe_ctrl.op == OP_SIGN_ADD_32 ? w_ex1_rs1_selected_data_32 +   w_ex1_rs2_selected_data[31:0] :
                          r_ex1_pipe_ctrl.op == OP_SIGN_SUB_32 ? w_ex1_rs1_selected_data_32 -   w_ex1_rs2_selected_data[31:0] :
                          r_ex1_pipe_ctrl.op == OP_SLL_32      ? w_ex1_rs1_selected_data_32 <<  w_ex1_rs2_selected_data[ 4:0] :
                          r_ex1_pipe_ctrl.op == OP_SRL_32      ? w_ex1_rs1_selected_data_32 >>  w_ex1_rs2_selected_data[ 4:0] :
                          r_ex1_pipe_ctrl.op == OP_SRA_32      ? w_ex1_rs1_selected_data_sra :
                          'h0;
`else // RV64
assign tmp_ex1_result_d = 'h0;
`endif // RV64

// Memo: I don't know why but if this sentence is integrated into above, test pattern fail.
assign w_ex1_rs1_selected_data_sra = $signed(w_ex1_rs1_selected_data_32) >>> w_ex1_rs2_selected_data[ 4:0];

logic                                      w_ex2_commit_flush;
logic                                      w_ex2_br_flush;
logic                                      w_ex2_flush;
assign w_ex2_commit_flush = scariv_pkg::is_flushed_commit(commit_if.commit_valid, commit_if.payload);
assign w_ex2_br_flush     = scariv_pkg::is_br_flush_target(r_ex2_issue.cmt_id, r_ex2_issue.grp_id, br_upd_if.cmt_id, br_upd_if.grp_id,
                                                           br_upd_if.dead, br_upd_if.mispredict) & br_upd_if.update;
assign w_ex2_flush = w_ex2_commit_flush | w_ex2_br_flush;

always_comb begin
  w_ex2_issue_next = r_ex1_issue;
  w_ex2_issue_next.valid = r_ex1_issue.valid & !w_ex1_flush;
end

always_ff @(posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_ex2_result <= 'h0;
    r_ex2_index <= 'h0;
    r_ex2_issue <= 'h0;

    r_ex2_wr_valid <= 1'b0;
  end else begin
    r_ex2_issue <= w_ex2_issue_next;
    r_ex2_index <= r_ex1_index;

    r_ex2_wr_valid <= r_ex1_wr_valid;

    r_ex2_muldiv_valid <= r_ex1_muldiv_valid & !w_ex1_flush;

    case (r_ex1_pipe_ctrl.op)
      OP_SIGN_LUI:    r_ex2_result <= {{(riscv_pkg::XLEN_W-32){r_ex1_issue.inst[31]}}, r_ex1_issue.inst[31:12], 12'h000};
      OP_SIGN_ADD:    r_ex2_result <= w_ex1_rs1_selected_data + w_ex1_rs2_selected_data;
      OP_SIGN_SUB:    r_ex2_result <= w_ex1_rs1_selected_data - w_ex1_rs2_selected_data;
`ifdef RV64
      OP_SIGN_ADD_32, OP_SIGN_SUB_32, OP_SLL_32, OP_SRL_32, OP_SRA_32:
        r_ex2_result <= {{(riscv_pkg::XLEN_W-32){tmp_ex1_result_d[31]}}, tmp_ex1_result_d[31: 0]};
`endif // RV64
      OP_XOR:         r_ex2_result <= w_ex1_rs1_selected_data ^   w_ex1_rs2_selected_data;
      OP_OR :         r_ex2_result <= w_ex1_rs1_selected_data |   w_ex1_rs2_selected_data;
      OP_AND:         r_ex2_result <= w_ex1_rs1_selected_data &   w_ex1_rs2_selected_data;
      OP_SLL:         r_ex2_result <= w_ex1_rs1_selected_data <<  w_ex1_rs2_selected_data[$clog2(riscv_pkg::XLEN_W)-1: 0];
      OP_SRL:         r_ex2_result <= w_ex1_rs1_selected_data >>  w_ex1_rs2_selected_data[$clog2(riscv_pkg::XLEN_W)-1: 0];
      OP_SRA:         r_ex2_result <= $signed(w_ex1_rs1_selected_data) >>> w_ex1_rs2_selected_data[$clog2(riscv_pkg::XLEN_W)-1: 0];
      /* verilator lint_off WIDTH */
      OP_SIGN_SLT:    r_ex2_result <= $signed(w_ex1_rs1_selected_data) < $signed(w_ex1_rs2_selected_data);
      OP_UNSIGN_SLT:  r_ex2_result <= w_ex1_rs1_selected_data < w_ex1_rs2_selected_data;
      default         r_ex2_result <= w_ex1_bitmanip_valid ? w_ex1_bitmanip_result :
                                      w_ex1_zicond_valid   ? w_ex1_zicond_result   : 'h0;
      // default : r_ex2_result <= {riscv_pkg::XLEN_W{1'b0}};
    endcase // case (r_ex1_pipe_ctrl.op)
  end
end

scariv_bitmanip_alu u_bitmanip_alu (.i_rs1(w_ex1_rs1_selected_data), .i_rs2(w_ex1_rs2_selected_data), .i_op(r_ex1_pipe_ctrl.op), .o_valid(w_ex1_bitmanip_valid), .o_out(w_ex1_bitmanip_result));
scariv_zicond_alu   u_zicond_alu   (.i_rs1(w_ex1_rs1_selected_data), .i_rs2(w_ex1_rs2_selected_data), .i_op(r_ex1_pipe_ctrl.op), .o_valid(w_ex1_zicond_valid),   .o_out(w_ex1_zicond_result));


// ----------------------
// Multiplier Pipeline
// ----------------------
scariv_muldiv_pipe
  #(
    .RV_ENTRY_SIZE (RV_ENTRY_SIZE),
    .MUL_UNROLL(MUL_UNROLL)
    )
u_scariv_muldiv_pipe
  (
   .i_clk    (i_clk),
   .i_reset_n(i_reset_n),

   .commit_if   (commit_if),
   .br_upd_if  (br_upd_if),

   .i_valid  (r_ex1_muldiv_valid),
   .i_op     (r_ex1_pipe_ctrl.op),

   .i_cmt_id   (r_ex1_issue.cmt_id),
   .i_grp_id   (r_ex1_issue.grp_id),
   .i_rd_rnid  (r_ex1_issue.wr_reg.rnid),
   .i_rd_type  (r_ex1_issue.wr_reg.typ),
   .i_index_oh (r_ex1_index        ),

   .i_rs1 (w_ex1_rs1_selected_data),
   .i_rs2 (w_ex1_rs2_selected_data),

   .o_stall (w_ex2_muldiv_stall),
   .o_valid (w_muldiv_res_valid),
   .o_cmt_id (w_muldiv_res_cmt_id),
   .o_grp_id (w_muldiv_res_grp_id),
   .o_res   (w_muldiv_res),

   .o_rd_rnid  (w_muldiv_rd_rnid ),
   .o_rd_type  (w_muldiv_rd_type ),
   .o_index_oh (w_muldiv_index_oh)
   );

always_comb begin
  if (w_muldiv_res_valid) begin
    ex2_phy_wr_if.valid   = 1'b1;
    ex2_phy_wr_if.rd_rnid = w_muldiv_rd_rnid;
    ex2_phy_wr_if.rd_type = w_muldiv_rd_type;
    ex2_phy_wr_if.rd_data = w_muldiv_res;

    done_report_if.valid  = w_muldiv_res_valid;
    done_report_if.cmt_id = w_muldiv_res_cmt_id;
    done_report_if.grp_id = w_muldiv_res_grp_id;
    done_report_if.fflags_update_valid = 1'b0;
    done_report_if.fflags = 'h0;
  end else begin
    ex2_phy_wr_if.valid   = r_ex2_wr_valid;
    ex2_phy_wr_if.rd_rnid = r_ex2_issue.wr_reg.rnid;
    ex2_phy_wr_if.rd_type = r_ex2_issue.wr_reg.typ;
    ex2_phy_wr_if.rd_data = r_ex2_result;

    done_report_if.valid  = r_ex2_issue.valid & ~r_ex2_muldiv_valid;
    done_report_if.cmt_id = r_ex2_issue.cmt_id;
    done_report_if.grp_id = r_ex2_issue.grp_id;
    done_report_if.fflags_update_valid = 1'b0;
    done_report_if.fflags = 'h0;
  end // else: !if(w_muldiv_res_valid)
end // always_comb


`ifdef SIMULATION
always_ff @(negedge i_clk, negedge i_reset_n) begin
  if (i_reset_n) begin
    if (w_muldiv_res_valid & r_ex2_issue.valid) begin
      $fatal(0, "Mul/Div Pipeline and ALU integer output valid signal must not be asserted in same time.");
    end
  end
end


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

`endif // SIMULATION

endmodule // scariv_alu_pipe
