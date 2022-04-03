module msrh_fpu_pipe
  import decoder_fpu_ctrl_pkg::*;
  import msrh_fpu_pkg::*;
#(
  parameter RV_ENTRY_SIZE = 32
  )
(
    input logic i_clk,
    input logic i_reset_n,

    /* CSR information */
    csr_info_if.slave  csr_info,

    input msrh_pkg::issue_t rv0_issue,
    input logic [RV_ENTRY_SIZE-1:0] rv0_index,
    input msrh_pkg::phy_wr_t ex1_i_phy_wr[msrh_pkg::TGT_BUS_SIZE],

    regread_if.master ex1_regread_int_rs1,

    regread_if.master ex1_regread_rs1,
    regread_if.master ex1_regread_rs2,
    regread_if.master ex1_regread_rs3,

    input msrh_pkg::mispred_t i_mispred_lsu[msrh_conf_pkg::LSU_INST_NUM],

    output msrh_pkg::early_wr_t o_ex1_early_wr,
    output msrh_pkg::phy_wr_t   o_ex3_phy_wr,

    done_if.master ex3_done_if
);

  msrh_pkg::issue_t                         r_ex0_issue;
  logic [RV_ENTRY_SIZE-1: 0] w_ex0_index;
  pipe_ctrl_t                              w_ex0_pipe_ctrl;

  pipe_ctrl_t                              r_ex1_pipe_ctrl;
  msrh_pkg::issue_t                         r_ex1_issue;
  logic [RV_ENTRY_SIZE-1: 0] r_ex1_index;

  logic [msrh_pkg::TGT_BUS_SIZE-1:0] w_ex2_rs1_fwd_valid;
  logic [msrh_pkg::TGT_BUS_SIZE-1:0] w_ex2_rs2_fwd_valid;
  logic [msrh_pkg::TGT_BUS_SIZE-1:0] w_ex2_rs3_fwd_valid;
  msrh_pkg::alen_t w_ex2_tgt_data          [msrh_pkg::TGT_BUS_SIZE];
  msrh_pkg::alen_t w_ex2_rs1_fwd_data;
  msrh_pkg::alen_t w_ex2_rs2_fwd_data;
  msrh_pkg::alen_t w_ex2_rs3_fwd_data;

  msrh_pkg::alen_t w_ex2_rs1_selected_data;
  msrh_pkg::alen_t w_ex2_rs2_selected_data;
  msrh_pkg::alen_t w_ex2_rs3_selected_data;

  logic                                    w_ex1_rs1_lsu_mispred;
  logic                                    w_ex1_rs2_lsu_mispred;
  logic                                    w_ex1_rs1_mispred;
  logic                                    w_ex1_rs2_mispred;

  pipe_ctrl_t                              r_ex2_pipe_ctrl;
  msrh_pkg::issue_t                         r_ex2_issue;
  logic [RV_ENTRY_SIZE-1: 0] r_ex2_index;
  msrh_pkg::alen_t r_ex2_rs1_data;
  msrh_pkg::alen_t r_ex2_rs2_data;
  msrh_pkg::alen_t r_ex2_rs3_data;
  logic                                    r_ex2_wr_valid;

  msrh_pkg::issue_t                        r_ex3_issue;
  logic                                    w_fpnew_result_valid;
  msrh_pkg::alen_t            w_fpnew_result_data;
logic [ 4: 0]                              w_fpnew_result_fflags;
  logic [RV_ENTRY_SIZE-1: 0] r_ex3_index;
  logic                                    r_ex3_wr_valid;
pipe_ctrl_t                                r_ex3_pipe_ctrl;
msrh_pkg::alen_t             w_ex2_res_data;
msrh_pkg::alen_t             r_ex3_res_data;

always_comb begin
  r_ex0_issue = rv0_issue;
  w_ex0_index = rv0_index;
end

// ---------------------
// EX0
// ---------------------

decoder_fpu_ctrl u_pipe_ctrl (
  .inst(r_ex0_issue.inst),
  .size(w_ex0_pipe_ctrl.size),
  .op  (w_ex0_pipe_ctrl.op)
);

// ---------------------
// EX1
// ---------------------

assign ex1_regread_rs1.valid = r_ex1_issue.valid & r_ex1_issue.rd_regs[0].valid & (r_ex1_issue.rd_regs[0].typ == msrh_pkg::FPR);
assign ex1_regread_rs1.rnid  = r_ex1_issue.rd_regs[0].rnid;

assign ex1_regread_rs2.valid = r_ex1_issue.valid & r_ex1_issue.rd_regs[1].valid & (r_ex1_issue.rd_regs[1].typ == msrh_pkg::FPR);
assign ex1_regread_rs2.rnid  = r_ex1_issue.rd_regs[1].rnid;

assign ex1_regread_rs3.valid = r_ex1_issue.valid & r_ex1_issue.rd_regs[2].valid & (r_ex1_issue.rd_regs[2].typ == msrh_pkg::FPR);
assign ex1_regread_rs3.rnid  = r_ex1_issue.rd_regs[2].rnid;

assign ex1_regread_int_rs1.valid = r_ex1_issue.valid & r_ex1_issue.rd_regs[0].valid & (r_ex1_issue.rd_regs[0].typ == msrh_pkg::GPR);
assign ex1_regread_int_rs1.rnid  = r_ex1_issue.rd_regs[0].rnid;

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

// -----------------------------
// EX1 :
// -----------------------------

assign w_ex1_rs1_mispred = r_ex1_issue.rd_regs[0].valid & r_ex1_issue.rd_regs[0].predict_ready ? w_ex1_rs1_lsu_mispred : 1'b0;
assign w_ex1_rs2_mispred = r_ex1_issue.rd_regs[1].valid & r_ex1_issue.rd_regs[1].predict_ready ? w_ex1_rs2_lsu_mispred : 1'b0;

assign o_ex1_early_wr.valid = r_ex1_issue.valid & r_ex1_issue.wr_reg.valid &
                              ~w_ex1_rs1_mispred & ~w_ex1_rs2_mispred;

assign o_ex1_early_wr.rd_rnid = r_ex1_issue.wr_reg.rnid;
assign o_ex1_early_wr.rd_type = r_ex1_issue.wr_reg.typ;
assign o_ex1_early_wr.may_mispred = 1'b0;

// -----------------------------
// EX2 Stage
// -----------------------------

generate
  for (genvar tgt_idx = 0; tgt_idx < msrh_pkg::REL_BUS_SIZE; tgt_idx++) begin : rs_tgt_loop
    assign w_ex2_rs1_fwd_valid[tgt_idx] = r_ex2_issue.rd_regs[0].valid & ex1_i_phy_wr[tgt_idx].valid &
                                          (r_ex2_issue.rd_regs[0].typ  == ex1_i_phy_wr[tgt_idx].rd_type) &
                                          (r_ex2_issue.rd_regs[0].rnid == ex1_i_phy_wr[tgt_idx].rd_rnid);


    assign w_ex2_rs2_fwd_valid[tgt_idx] = r_ex2_issue.rd_regs[1].valid & ex1_i_phy_wr[tgt_idx].valid &
                                          (r_ex2_issue.rd_regs[1].typ  == ex1_i_phy_wr[tgt_idx].rd_type) &
                                          (r_ex2_issue.rd_regs[1].rnid == ex1_i_phy_wr[tgt_idx].rd_rnid);

    assign w_ex2_rs3_fwd_valid[tgt_idx] =  r_ex2_issue.rd_regs[2].valid & ex1_i_phy_wr[tgt_idx].valid &
                                           (r_ex2_issue.rd_regs[2].typ  == ex1_i_phy_wr[tgt_idx].rd_type) &
                                           (r_ex2_issue.rd_regs[2].rnid == ex1_i_phy_wr[tgt_idx].rd_rnid);

    assign w_ex2_tgt_data[tgt_idx] = ex1_i_phy_wr[tgt_idx].rd_data;
  end
endgenerate

bit_oh_or #(
    .T(msrh_pkg::alen_t),
    .WORDS(msrh_pkg::TGT_BUS_SIZE)
) u_rs1_data_select (
    .i_oh(w_ex2_rs1_fwd_valid),
    .i_data(w_ex2_tgt_data),
    .o_selected(w_ex2_rs1_fwd_data)
);

bit_oh_or #(
    .T(msrh_pkg::alen_t),
    .WORDS(msrh_pkg::TGT_BUS_SIZE)
) u_rs2_data_select (
    .i_oh(w_ex2_rs2_fwd_valid),
    .i_data(w_ex2_tgt_data),
    .o_selected(w_ex2_rs2_fwd_data)
);

bit_oh_or #(
    .T(msrh_pkg::alen_t),
    .WORDS(msrh_pkg::TGT_BUS_SIZE)
) u_rs3_data_select (
    .i_oh(w_ex2_rs3_fwd_valid),
    .i_data(w_ex2_tgt_data),
    .o_selected(w_ex2_rs3_fwd_data)
);

always_ff @(posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_ex2_rs1_data <= 'h0;
    r_ex2_rs2_data <= 'h0;
    r_ex2_rs3_data <= 'h0;

    r_ex2_issue <= 'h0;
    r_ex2_index <= 'h0;
    r_ex2_pipe_ctrl <= 'h0;

    r_ex2_wr_valid <= 1'b0;
  end else begin
    r_ex2_rs1_data <= (r_ex1_issue.rd_regs[0].typ == msrh_pkg::GPR) ? ex1_regread_int_rs1.data : ex1_regread_rs1.data;
    r_ex2_rs2_data <= ex1_regread_rs2.data;
    r_ex2_rs3_data <= ex1_regread_rs3.data;

    r_ex2_issue <= r_ex1_issue;
    r_ex2_index <= r_ex1_index;
    r_ex2_pipe_ctrl <= r_ex1_pipe_ctrl;

    r_ex2_wr_valid <= o_ex1_early_wr.valid;
  end
end

assign w_ex2_rs1_selected_data = |w_ex2_rs1_fwd_valid ? w_ex2_rs1_fwd_data : r_ex2_rs1_data;
assign w_ex2_rs2_selected_data = |w_ex2_rs2_fwd_valid ? w_ex2_rs2_fwd_data : r_ex2_rs2_data;
assign w_ex2_rs3_selected_data = |w_ex2_rs3_fwd_valid ? w_ex2_rs3_fwd_data : r_ex2_rs3_data;

logic signed [31: 0] tmp_ex2_result_d;
logic signed [31: 0] w_ex2_rs1_selected_data_32;
logic signed [31: 0] w_ex2_rs1_selected_data_sra;
assign w_ex2_rs1_selected_data_32 = w_ex2_rs1_selected_data[31:0];
assign tmp_ex2_result_d = 'h0;

// Memo: I don't know why but if this sentence is integrated into above, test pattern fail.
assign w_ex2_rs1_selected_data_sra = $signed(w_ex2_rs1_selected_data_32) >>> w_ex2_rs2_selected_data[ 4:0];

`ifdef RV64
logic [ 63: 0]       w_ex2_rs1_canonical;
logic [ 63: 0]       w_ex2_rs2_canonical;
assign w_ex2_rs1_canonical = !(&w_ex2_rs1_selected_data[63:32]) ? 64'hffffffff_7fc00000 : w_ex2_rs1_selected_data;
assign w_ex2_rs2_canonical = !(&w_ex2_rs2_selected_data[63:32]) ? 64'hffffffff_7fc00000 : w_ex2_rs2_selected_data;
`else  // RV64
logic [ 31: 0]       w_ex2_rs1_canonical;
logic [ 31: 0]       w_ex2_rs2_canonical;
assign w_ex2_rs1_canonical = w_ex2_rs1_selected_data;
assign w_ex2_rs2_canonical = w_ex2_rs2_selected_data;
`endif // RV64

logic                w_ex2_fpnew_valid;

always_comb begin
  case (r_ex2_pipe_ctrl.op)
    OP_FMV_X_W  : begin
      w_ex2_res_data = {{32{w_ex2_rs1_selected_data[31]}}, w_ex2_rs1_selected_data[31: 0]};
      w_ex2_fpnew_valid = 1'b0;
    end
`ifdef RV64
    OP_FMV_W_X  : begin
      w_ex2_res_data = {{32{1'b1}}, w_ex2_rs1_selected_data[31: 0]};
      w_ex2_fpnew_valid = 1'b0;
    end
`else  // RV64
    OP_FMV_W_X  : begin
      w_ex2_res_data = w_ex2_rs1_selected_data;
      w_ex2_fpnew_valid = 1'b0;
    end
`endif // RV64
`ifdef RV64
    OP_FMV_X_D  : begin
      w_ex2_res_data = w_ex2_rs1_selected_data;
      w_ex2_fpnew_valid = 1'b0;
    end
    OP_FMV_D_X  : begin
      w_ex2_res_data = w_ex2_rs1_selected_data;
      w_ex2_fpnew_valid = 1'b0;
    end
    OP_FSGNJ_D  : begin
      w_ex2_res_data = { w_ex2_rs2_selected_data[63], w_ex2_rs1_selected_data[62:0]};
      w_ex2_fpnew_valid = 1'b0;
    end
    OP_FSGNJN_D : begin
      w_ex2_res_data = {~w_ex2_rs2_selected_data[63], w_ex2_rs1_selected_data[62:0]};
      w_ex2_fpnew_valid = 1'b0;
    end
    OP_FSGNJX_D : begin
      w_ex2_res_data = { w_ex2_rs1_selected_data[63] ^ w_ex2_rs2_selected_data[63],
                         w_ex2_rs1_selected_data[62:0]};
      w_ex2_fpnew_valid = 1'b0;
    end
`endif // RV64
`ifdef RV64
    OP_FSGNJ_S  : begin
      w_ex2_res_data = {w_ex2_rs1_canonical[63:32],  w_ex2_rs2_canonical[31], w_ex2_rs1_canonical[30:0]};
      w_ex2_fpnew_valid = 1'b0;
    end
    OP_FSGNJN_S : begin
      w_ex2_res_data = {w_ex2_rs1_canonical[63:32], ~w_ex2_rs2_canonical[31], w_ex2_rs1_canonical[30:0]};
      w_ex2_fpnew_valid = 1'b0;
    end
    OP_FSGNJX_S : begin
      w_ex2_res_data = {w_ex2_rs1_canonical[63:32],
                        w_ex2_rs1_canonical[31] ^ w_ex2_rs2_canonical[31],
                        w_ex2_rs1_canonical[30: 0]};
      w_ex2_fpnew_valid = 1'b0;
    end
`else  // RV64
    OP_FSGNJ_S  : begin
      w_ex2_res_data = {w_ex2_rs2_canonical[31], w_ex2_rs1_canonical[30:0]};
      w_ex2_fpnew_valid = 1'b0;
    end
    OP_FSGNJN_S : begin
      w_ex2_res_data = {~w_ex2_rs2_canonical[31], w_ex2_rs1_canonical[30:0]};
      w_ex2_fpnew_valid = 1'b0;
    end
    OP_FSGNJX_S : begin
      w_ex2_res_data = {w_ex2_rs1_canonical[31] ^ w_ex2_rs2_canonical[31],
                        w_ex2_rs1_canonical[30: 0]};
      w_ex2_fpnew_valid = 1'b0;
    end
`endif // RV64
    default    : begin
      w_ex2_res_data = 'h0;
      w_ex2_fpnew_valid = 1'b1;
    end
  endcase // case (r_ex3_pipe_ctrl.op)
end // always_comb

always_ff @(posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    // r_ex3_result <= 'h0;
    r_ex3_index <= 'h0;
    r_ex3_issue <= 'h0;
    r_ex3_wr_valid  <= 1'b0;
    r_ex3_pipe_ctrl <= 'h0;
    r_ex3_res_data  <= 'h0;
  end else begin
    r_ex3_issue <= r_ex2_issue;
    r_ex3_index <= r_ex2_index;
    r_ex3_wr_valid  <= r_ex2_wr_valid;
    r_ex3_pipe_ctrl <= r_ex2_pipe_ctrl;
    r_ex3_res_data  <= w_ex2_res_data;
  end
end

// ----------------------
// FPNew Pipeline
// ----------------------
msrh_fpnew_wrapper
u_msrh_fpnew_wrapper
  (
   .i_clk     (i_clk    ),
   .i_reset_n (i_reset_n),

   .i_valid (r_ex2_issue.valid & w_ex2_fpnew_valid),
   .o_ready (),
   .i_pipe_ctrl (r_ex2_pipe_ctrl),
   .i_rnd_mode  (r_ex2_issue.inst[14:12] == 3'b111 ? csr_info.fcsr[ 7: 5] : r_ex2_issue.inst[14:12]),

   .i_rs1 (w_ex2_rs1_selected_data),
   .i_rs2 (w_ex2_rs2_selected_data),
   .i_rs3 (w_ex2_rs3_selected_data),

   .o_valid (w_fpnew_result_valid ),
   .o_result(w_fpnew_result_data  ),
   .o_fflags(w_fpnew_result_fflags)
   );


always_comb begin
  o_ex3_phy_wr.valid   = r_ex3_wr_valid;
  o_ex3_phy_wr.rd_rnid = r_ex3_issue.wr_reg.rnid;
  o_ex3_phy_wr.rd_type = r_ex3_issue.wr_reg.typ;
  o_ex3_phy_wr.rd_data = w_fpnew_result_valid ? w_fpnew_result_data : r_ex3_res_data;

  ex3_done_if.done                = r_ex3_issue.valid;
  ex3_done_if.index_oh            = r_ex3_index;
  ex3_done_if.except_valid        = 1'b0;
  ex3_done_if.except_type         = msrh_pkg::except_t'('h0);
  ex3_done_if.fflags_update_valid = w_fpnew_result_valid;
  ex3_done_if.fflags              = w_fpnew_result_valid ? w_fpnew_result_fflags : 'h0;
end // always_comb


endmodule // msrh_fpu_pipe
