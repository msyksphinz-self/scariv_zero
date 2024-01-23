// ------------------------------------------------------------------------
// NAME : scariv_fpu_pipe
// TYPE : module
// ------------------------------------------------------------------------
// FPU Pipeline
// ------------------------------------------------------------------------
// ex0: Decode instruction
// ex1: Send Early-release
// ex2: Get Forwarding data
// ex3: FPU Execute
// ...
//    : FPU Execution Done
// ------------------------------------------------------------------------

module scariv_fpu_pipe
  import decoder_fpu_ctrl_pkg::*;
  import scariv_fpu_pkg::*;
#(
  parameter RV_ENTRY_SIZE = 32
  )
(
    input logic i_clk,
    input logic i_reset_n,

    /* CSR information */
    csr_info_if.slave  csr_info,

    output logic o_fpnew_block,

    // Commit notification
    commit_if.monitor commit_if,
    br_upd_if.slave                br_upd_if,

    input scariv_pkg::issue_t ex0_issue,
    input logic [RV_ENTRY_SIZE-1:0] ex0_index,
    phy_wr_if.slave ex1_phy_wr_if[scariv_pkg::TGT_BUS_SIZE],

    regread_if.master ex0_regread_int_rs1,

    regread_if.master ex0_regread_rs1,
    regread_if.master ex0_regread_rs2,
    regread_if.master ex0_regread_rs3,

    lsu_mispred_if.slave mispred_if[scariv_conf_pkg::LSU_INST_NUM],

    early_wr_if.master    ex1_mv_early_wr_if,
    phy_wr_if.master      ex3_mv_phy_wr_if,
    done_report_if.master mv_done_report_if,

    phy_wr_if.master      fpnew_phy_wr_if,
    done_report_if.master fp_done_report_if
);

scariv_pkg::issue_t                       w_ex0_issue;
logic [RV_ENTRY_SIZE-1: 0]                w_ex0_index;
pipe_ctrl_t                               w_ex0_pipe_ctrl;

logic [scariv_pkg::TGT_BUS_SIZE-1:0]      w_ex0_rs_fwd_valid[3];
scariv_pkg::alen_t                        w_ex0_rs_fwd_data [3];

logic [ 2: 0]                             w_ex0_rs_lsu_mispred;
logic [ 2: 0]                             w_ex0_rs_mispred;
logic [ 2: 0]                             r_ex1_rs_mispred;

logic [ 2: 0]                             r_ex1_fwd_valid;
scariv_pkg::alen_t                        r_ex1_rs1_data;
scariv_pkg::alen_t                        r_ex1_rs2_data;
scariv_pkg::alen_t                        r_ex1_rs3_data;

pipe_ctrl_t                               r_ex1_pipe_ctrl;
scariv_pkg::issue_t                       r_ex1_issue;
scariv_pkg::issue_t                       w_ex1_issue_next;
logic [RV_ENTRY_SIZE-1: 0]                r_ex1_index;
logic                                     w_ex1_frm_invalid;

logic [scariv_pkg::TGT_BUS_SIZE-1:0] w_ex1_rs_fwd_valid[3];
scariv_pkg::alen_t                   w_ex1_rs_fwd_data [3];

logic [scariv_pkg::TGT_BUS_SIZE-1:0] w_ex2_rs1_fwd_valid;
logic [scariv_pkg::TGT_BUS_SIZE-1:0] w_ex2_rs2_fwd_valid;
logic [scariv_pkg::TGT_BUS_SIZE-1:0] w_ex2_rs3_fwd_valid;
scariv_pkg::alen_t w_ex2_tgt_data          [scariv_pkg::TGT_BUS_SIZE];
scariv_pkg::alen_t w_ex2_rs1_fwd_data;
scariv_pkg::alen_t w_ex2_rs2_fwd_data;
scariv_pkg::alen_t w_ex2_rs3_fwd_data;

/* verilator lint_off UNOPTFLAT */
scariv_pkg::alen_t w_ex2_rs1_selected_data;
/* verilator lint_off UNOPTFLAT */
scariv_pkg::alen_t w_ex2_rs2_selected_data;
/* verilator lint_off UNOPTFLAT */
scariv_pkg::alen_t w_ex2_rs3_selected_data;

logic [ 2: 0]                      w_ex1_rs_lsu_mispred;
logic [ 2: 0]                      w_ex1_rs_mispred;

pipe_ctrl_t                        r_ex2_pipe_ctrl;
scariv_pkg::issue_t                r_ex2_issue;
scariv_pkg::issue_t                w_ex2_issue_next;
logic [RV_ENTRY_SIZE-1: 0]         r_ex2_index;
scariv_pkg::alen_t                 r_ex2_rs1_data;
scariv_pkg::alen_t                 r_ex2_rs2_data;
scariv_pkg::alen_t                 r_ex2_rs3_data;
logic                              r_ex2_wr_valid;
logic [ 2: 0]                      r_ex2_rs_mispred;
logic                              r_ex2_frm_invalid;


scariv_pkg::issue_t                r_ex3_issue;
logic                              w_fpnew_result_valid;
scariv_pkg::alen_t                 w_fpnew_result_data;
logic [ 4: 0]                      w_fpnew_result_fflags;
logic [RV_ENTRY_SIZE-1: 0]         r_ex3_index;
logic                              r_ex3_wr_valid;
pipe_ctrl_t                        r_ex3_pipe_ctrl;
scariv_pkg::alen_t                 w_ex2_res_data;
scariv_pkg::alen_t                 r_ex3_res_data;
logic                              r_ex3_frm_invalid;

logic                              w_fpnew_busy;

always_comb begin
  w_ex0_issue = ex0_issue;
  w_ex0_index = ex0_index;
end

// ---------------------
// EX0
// ---------------------

decoder_fpu_ctrl u_pipe_ctrl (
  .inst    (w_ex0_issue.inst        ),
  .size    (w_ex0_pipe_ctrl.size    ),
  .op      (w_ex0_pipe_ctrl.op      ),
  .pipe    (w_ex0_pipe_ctrl.pipe    ),
  .use_frm (w_ex0_pipe_ctrl.use_frm )
);

generate for (genvar rs_idx = 0; rs_idx < 3; rs_idx++) begin : ex0_mispred_loop
   select_mispred_bus rs1_mispred_select
   (
    .i_entry_rnid (w_ex0_issue.rd_regs[rs_idx].rnid),
    .i_entry_type (w_ex0_issue.rd_regs[rs_idx].typ),
    .i_mispred    (mispred_if),

    .o_mispred    (w_ex0_rs_lsu_mispred[rs_idx])
    );

  assign w_ex0_rs_mispred[rs_idx] = w_ex0_issue.rd_regs[rs_idx].valid &
                                    w_ex0_issue.rd_regs[rs_idx].predict_ready ? w_ex0_rs_lsu_mispred[rs_idx] : 1'b0;

  scariv_pkg::alen_t w_ex0_tgt_data [scariv_pkg::TGT_BUS_SIZE];
  for (genvar tgt_idx = 0; tgt_idx < scariv_pkg::TGT_BUS_SIZE; tgt_idx++) begin : rs_tgt_loop
    assign w_ex0_rs_fwd_valid[rs_idx][tgt_idx] = ex0_issue.rd_regs[rs_idx].valid & ex1_phy_wr_if[tgt_idx].valid &
                                                 (ex0_issue.rd_regs[rs_idx].typ  == scariv_pkg::GPR ? ex0_issue.rd_regs[rs_idx].regidx != 'h0 : 1'b1) &
                                                 (ex0_issue.rd_regs[rs_idx].typ  == ex1_phy_wr_if[tgt_idx].rd_type) &
                                                 (ex0_issue.rd_regs[rs_idx].rnid == ex1_phy_wr_if[tgt_idx].rd_rnid);
    assign w_ex0_tgt_data[tgt_idx] = ex1_phy_wr_if[tgt_idx].rd_data;
  end
    bit_oh_or #(
      .T(scariv_pkg::alen_t),
      .WORDS(scariv_pkg::TGT_BUS_SIZE)
  ) u_rs_data_select (
      .i_oh      (w_ex0_rs_fwd_valid[rs_idx]),
      .i_data    (w_ex0_tgt_data            ),
      .o_selected(w_ex0_rs_fwd_data [rs_idx])
  );
end endgenerate


// ---------------------
// EX1
// ---------------------

assign ex0_regread_rs1.valid = ex0_issue.valid & ex0_issue.rd_regs[0].valid & (ex0_issue.rd_regs[0].typ == scariv_pkg::FPR);
assign ex0_regread_rs1.rnid  = ex0_issue.rd_regs[0].rnid;

assign ex0_regread_rs2.valid = ex0_issue.valid & ex0_issue.rd_regs[1].valid & (ex0_issue.rd_regs[1].typ == scariv_pkg::FPR);
assign ex0_regread_rs2.rnid  = ex0_issue.rd_regs[1].rnid;

assign ex0_regread_rs3.valid = ex0_issue.valid & ex0_issue.rd_regs[2].valid & (ex0_issue.rd_regs[2].typ == scariv_pkg::FPR);
assign ex0_regread_rs3.rnid  = ex0_issue.rd_regs[2].rnid;

assign ex0_regread_int_rs1.valid = ex0_issue.valid & ex0_issue.rd_regs[0].valid & (ex0_issue.rd_regs[0].typ == scariv_pkg::GPR);
assign ex0_regread_int_rs1.rnid  = ex0_issue.rd_regs[0].rnid;

logic                                      w_ex0_commit_flush;
logic                                      w_ex0_br_flush;
logic                                      w_ex0_flush;
assign w_ex0_commit_flush = commit_if.is_flushed_commit();
assign w_ex0_br_flush     = scariv_pkg::is_br_flush_target(w_ex0_issue.cmt_id, w_ex0_issue.grp_id, br_upd_if.cmt_id, br_upd_if.grp_id,
                                                          br_upd_if.dead, br_upd_if.mispredict) & br_upd_if.update;
assign w_ex0_flush = w_ex0_commit_flush | w_ex0_br_flush;

assign o_fpnew_block = w_fpnew_busy |
                       r_ex1_pipe_ctrl.op inside {OP_FDIV_S, OP_FDIV_D, OP_FSQRT_S, OP_FSQRT_D};

always_comb begin
  w_ex1_issue_next = w_ex0_issue;
  w_ex1_issue_next.valid = w_ex0_issue.valid & !w_ex0_flush & (~|w_ex0_rs_mispred);
end

always_ff @(posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_ex1_issue <= 'h0;
    r_ex1_index <= 'h0;
    r_ex1_pipe_ctrl <= 'h0;
    r_ex1_rs_mispred <= 'h0;
  end else begin
    r_ex1_issue <= w_ex1_issue_next;
    r_ex1_index <= w_ex0_index;
    r_ex1_pipe_ctrl <= w_ex0_pipe_ctrl;
    r_ex1_rs_mispred <= w_ex0_rs_mispred;

    r_ex1_rs1_data <= w_ex0_rs_fwd_data[0];
    r_ex1_rs2_data <= w_ex0_rs_fwd_data[1];
    r_ex1_rs3_data <= w_ex0_rs_fwd_data[2];

    r_ex1_fwd_valid[0] <= |w_ex0_rs_fwd_valid[0];
    r_ex1_fwd_valid[1] <= |w_ex0_rs_fwd_valid[1];
    r_ex1_fwd_valid[2] <= |w_ex0_rs_fwd_valid[2];
  end
end


generate for (genvar rs_idx = 0; rs_idx < 3; rs_idx++) begin : mispred_loop
   select_mispred_bus rs1_mispred_select
   (
    .i_entry_rnid (r_ex1_issue.rd_regs[rs_idx].rnid),
    .i_entry_type (r_ex1_issue.rd_regs[rs_idx].typ),
    .i_mispred    (mispred_if),

    .o_mispred    (w_ex1_rs_lsu_mispred[rs_idx])
    );

  assign w_ex1_rs_mispred[rs_idx] = r_ex1_issue.rd_regs[rs_idx].valid &
                                    r_ex1_issue.rd_regs[rs_idx].predict_ready ? w_ex1_rs_lsu_mispred[rs_idx] : 1'b0;
end
endgenerate


// -----------------------------
// EX1 :
// -----------------------------
assign ex1_mv_early_wr_if.valid = r_ex1_issue.valid & r_ex1_issue.wr_reg.valid & (r_ex1_pipe_ctrl.pipe == PIPE_FAST) &
                                 &(~(w_ex1_rs_mispred | r_ex1_rs_mispred));

assign ex1_mv_early_wr_if.rd_rnid = r_ex1_issue.wr_reg.rnid;
assign ex1_mv_early_wr_if.rd_type = r_ex1_issue.wr_reg.typ;
assign ex1_mv_early_wr_if.may_mispred = 1'b0;

generate for (genvar rs_idx = 0; rs_idx < 3; rs_idx++) begin : ex1_rs_loop
  scariv_pkg::alen_t w_ex1_tgt_data [scariv_pkg::TGT_BUS_SIZE];
  for (genvar tgt_idx = 0; tgt_idx < scariv_pkg::TGT_BUS_SIZE; tgt_idx++) begin : rs_tgt_loop
    assign w_ex1_rs_fwd_valid[rs_idx][tgt_idx] = r_ex1_issue.rd_regs[rs_idx].valid & ex1_phy_wr_if[tgt_idx].valid &
                                                 (r_ex1_issue.rd_regs[rs_idx].typ == scariv_pkg::GPR ? r_ex1_issue.rd_regs[rs_idx].regidx != 'h0 : 1'b1) &
                                                 (r_ex1_issue.rd_regs[rs_idx].typ  == ex1_phy_wr_if[tgt_idx].rd_type) &
                                                 (r_ex1_issue.rd_regs[rs_idx].rnid == ex1_phy_wr_if[tgt_idx].rd_rnid);
    assign w_ex1_tgt_data[tgt_idx] = ex1_phy_wr_if[tgt_idx].rd_data;
  end
    bit_oh_or #(
      .T(scariv_pkg::alen_t),
      .WORDS(scariv_pkg::TGT_BUS_SIZE)
  ) u_rs_data_select (
      .i_oh      (w_ex1_rs_fwd_valid[rs_idx]),
      .i_data    (w_ex1_tgt_data            ),
      .o_selected(w_ex1_rs_fwd_data [rs_idx])
  );
end endgenerate


assign w_ex1_frm_invalid = r_ex1_pipe_ctrl.use_frm & ((r_ex1_issue.inst[14:12] == 3'b111) ? (csr_info.fcsr[7:5] == 3'b101) | (csr_info.fcsr[7:5] == 3'b110) | (csr_info.fcsr[7:5] == 3'b111) :
                                                      (r_ex1_issue.inst[14:12] == 3'b101) | (r_ex1_issue.inst[14:12] == 3'b110));

// -----------------------------
// EX2 Stage
// -----------------------------

generate
  for (genvar tgt_idx = 0; tgt_idx < scariv_pkg::TGT_BUS_SIZE; tgt_idx++) begin : rs_tgt_loop
    assign w_ex2_rs1_fwd_valid[tgt_idx] = r_ex2_issue.rd_regs[0].valid & ex1_phy_wr_if[tgt_idx].valid &
                                          (r_ex2_issue.rd_regs[0].typ == scariv_pkg::GPR ? r_ex2_issue.rd_regs[0].regidx != 'h0 : 1'b1) &
                                          (r_ex2_issue.rd_regs[0].typ  == ex1_phy_wr_if[tgt_idx].rd_type) &
                                          (r_ex2_issue.rd_regs[0].rnid == ex1_phy_wr_if[tgt_idx].rd_rnid);


    assign w_ex2_rs2_fwd_valid[tgt_idx] = r_ex2_issue.rd_regs[1].valid & ex1_phy_wr_if[tgt_idx].valid &
                                          (r_ex2_issue.rd_regs[1].typ == scariv_pkg::GPR ? r_ex2_issue.rd_regs[1].regidx != 'h0 : 1'b1) &
                                          (r_ex2_issue.rd_regs[1].typ  == ex1_phy_wr_if[tgt_idx].rd_type) &
                                          (r_ex2_issue.rd_regs[1].rnid == ex1_phy_wr_if[tgt_idx].rd_rnid);

    assign w_ex2_rs3_fwd_valid[tgt_idx] =  r_ex2_issue.rd_regs[2].valid & ex1_phy_wr_if[tgt_idx].valid &
                                           (r_ex2_issue.rd_regs[2].typ == scariv_pkg::GPR ? r_ex2_issue.rd_regs[2].regidx != 'h0 : 1'b1) &
                                           (r_ex2_issue.rd_regs[2].typ  == ex1_phy_wr_if[tgt_idx].rd_type) &
                                           (r_ex2_issue.rd_regs[2].rnid == ex1_phy_wr_if[tgt_idx].rd_rnid);

    assign w_ex2_tgt_data[tgt_idx] = ex1_phy_wr_if[tgt_idx].rd_data;
  end
endgenerate

bit_oh_or #(
    .T(scariv_pkg::alen_t),
    .WORDS(scariv_pkg::TGT_BUS_SIZE)
) u_rs1_data_select (
    .i_oh(w_ex2_rs1_fwd_valid),
    .i_data(w_ex2_tgt_data),
    .o_selected(w_ex2_rs1_fwd_data)
);

bit_oh_or #(
    .T(scariv_pkg::alen_t),
    .WORDS(scariv_pkg::TGT_BUS_SIZE)
) u_rs2_data_select (
    .i_oh(w_ex2_rs2_fwd_valid),
    .i_data(w_ex2_tgt_data),
    .o_selected(w_ex2_rs2_fwd_data)
);

bit_oh_or #(
    .T(scariv_pkg::alen_t),
    .WORDS(scariv_pkg::TGT_BUS_SIZE)
) u_rs3_data_select (
    .i_oh(w_ex2_rs3_fwd_valid),
    .i_data(w_ex2_tgt_data),
    .o_selected(w_ex2_rs3_fwd_data)
);

logic                                      w_ex1_commit_flush;
logic                                      w_ex1_br_flush;
logic                                      w_ex1_flush;
assign w_ex1_commit_flush = commit_if.is_flushed_commit();
assign w_ex1_br_flush     = scariv_pkg::is_br_flush_target(r_ex1_issue.cmt_id, r_ex1_issue.grp_id, br_upd_if.cmt_id, br_upd_if.grp_id,
                                                           br_upd_if.dead, br_upd_if.mispredict) & br_upd_if.update;
assign w_ex1_flush = w_ex1_commit_flush | w_ex1_br_flush;


always_comb begin
  w_ex2_issue_next = r_ex1_issue;
  w_ex2_issue_next.valid = r_ex1_issue.valid & !w_ex1_flush;
end

always_ff @(posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_ex2_rs1_data <= 'h0;
    r_ex2_rs2_data <= 'h0;
    r_ex2_rs3_data <= 'h0;

    r_ex2_issue <= 'h0;
    r_ex2_index <= 'h0;
    r_ex2_pipe_ctrl <= 'h0;

    r_ex2_wr_valid <= 1'b0;

    r_ex2_rs_mispred <= 3'b000;

    r_ex2_frm_invalid <= 1'b0;
  end else begin
    r_ex2_rs1_data <= r_ex1_fwd_valid[0]     ? r_ex1_rs1_data :
                      |w_ex1_rs_fwd_valid[0] ? w_ex1_rs_fwd_data[0] :
                      (r_ex1_issue.rd_regs[0].typ == scariv_pkg::GPR) ? ex0_regread_int_rs1.data : ex0_regread_rs1.data;
    r_ex2_rs2_data <= r_ex1_fwd_valid[1]     ? r_ex1_rs2_data :
                      |w_ex1_rs_fwd_valid[1] ? w_ex1_rs_fwd_data[1] : ex0_regread_rs2.data;
    r_ex2_rs3_data <= r_ex1_fwd_valid[2]     ? r_ex1_rs3_data :
                      |w_ex1_rs_fwd_valid[2] ? w_ex1_rs_fwd_data[2] : ex0_regread_rs3.data;

    r_ex2_issue <= w_ex2_issue_next;
    r_ex2_index <= r_ex1_index;
    r_ex2_pipe_ctrl <= r_ex1_pipe_ctrl;

    r_ex2_wr_valid <= ex1_mv_early_wr_if.valid;

    r_ex2_rs_mispred <= r_ex1_rs_mispred | w_ex1_rs_mispred;

    r_ex2_frm_invalid <= w_ex1_frm_invalid;
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

logic [63: 0] w_ex2_rs1_canonical;
logic [63: 0] w_ex2_rs2_canonical;
generate if (riscv_fpu_pkg::FLEN_W == 64) begin
  assign w_ex2_rs1_canonical = !(&w_ex2_rs1_selected_data[63:32]) ? 64'hffffffff_7fc00000 : w_ex2_rs1_selected_data;
  assign w_ex2_rs2_canonical = !(&w_ex2_rs2_selected_data[63:32]) ? 64'hffffffff_7fc00000 : w_ex2_rs2_selected_data;
end else begin
  assign w_ex2_rs1_canonical = w_ex2_rs1_selected_data;
  assign w_ex2_rs2_canonical = w_ex2_rs2_selected_data;
end
endgenerate

logic                w_ex2_fpnew_valid;

always_comb begin
  case (r_ex2_pipe_ctrl.op)
    OP_FMV_X_W  : begin
      w_ex2_res_data = {{32{w_ex2_rs1_selected_data[31]}}, w_ex2_rs1_selected_data[31: 0]};
      w_ex2_fpnew_valid = 1'b0;
    end
    OP_FMV_W_X  : begin
      if (riscv_fpu_pkg::FLEN_W == 64) begin
        w_ex2_res_data = {{32{1'b1}}, w_ex2_rs1_selected_data[31: 0]};
        w_ex2_fpnew_valid = 1'b0;
      end else begin
        w_ex2_res_data = w_ex2_rs1_selected_data;
        w_ex2_fpnew_valid = 1'b0;
      end
    end
    OP_FMV_X_D  : begin
      w_ex2_res_data = w_ex2_rs1_selected_data;
      w_ex2_fpnew_valid = 1'b0;
    end
    OP_FMV_D_X  : begin
      w_ex2_res_data = w_ex2_rs1_selected_data;
      w_ex2_fpnew_valid = 1'b0;
    end
    OP_FSGNJ_D  : begin
      w_ex2_res_data = { w_ex2_rs2_selected_data[riscv_fpu_pkg::FLEN_W-1], w_ex2_rs1_selected_data[riscv_fpu_pkg::FLEN_W-2:0]};
      w_ex2_fpnew_valid = 1'b0;
    end
    OP_FSGNJN_D : begin
      w_ex2_res_data = {~w_ex2_rs2_selected_data[riscv_fpu_pkg::FLEN_W-1], w_ex2_rs1_selected_data[riscv_fpu_pkg::FLEN_W-2:0]};
      w_ex2_fpnew_valid = 1'b0;
    end
    OP_FSGNJX_D : begin
      w_ex2_res_data = { w_ex2_rs1_selected_data[riscv_fpu_pkg::FLEN_W-1] ^ w_ex2_rs2_selected_data[riscv_fpu_pkg::FLEN_W-1],
                         w_ex2_rs1_selected_data[riscv_fpu_pkg::FLEN_W-2:0]};
      w_ex2_fpnew_valid = 1'b0;
    end
    OP_FSGNJ_S  : begin
      if (riscv_fpu_pkg::FLEN_W == 64) begin
        w_ex2_res_data = {w_ex2_rs1_canonical[63:32],  w_ex2_rs2_canonical[31], w_ex2_rs1_canonical[30:0]};
        w_ex2_fpnew_valid = 1'b0;
      end else begin
        w_ex2_res_data = {w_ex2_rs2_canonical[31], w_ex2_rs1_canonical[30:0]};
        w_ex2_fpnew_valid = 1'b0;
      end
    end
    OP_FSGNJN_S : begin
      if (riscv_fpu_pkg::FLEN_W == 64) begin
        w_ex2_res_data = {w_ex2_rs1_canonical[63:32], ~w_ex2_rs2_canonical[31], w_ex2_rs1_canonical[30:0]};
        w_ex2_fpnew_valid = 1'b0;
      end else begin
        w_ex2_res_data = {~w_ex2_rs2_canonical[31], w_ex2_rs1_canonical[30:0]};
        w_ex2_fpnew_valid = 1'b0;
      end
    end
    OP_FSGNJX_S : begin
      if (riscv_fpu_pkg::FLEN_W == 64) begin
        w_ex2_res_data = {w_ex2_rs1_canonical[63:32],
                          w_ex2_rs1_canonical[31] ^ w_ex2_rs2_canonical[31],
                          w_ex2_rs1_canonical[30: 0]};
        w_ex2_fpnew_valid = 1'b0;
      end else begin
        w_ex2_res_data = {w_ex2_rs1_canonical[31] ^ w_ex2_rs2_canonical[31],
                          w_ex2_rs1_canonical[30: 0]};
        w_ex2_fpnew_valid = 1'b0;
      end
    end
    default    : begin
      w_ex2_res_data = 'h0;
      w_ex2_fpnew_valid = 1'b1;
    end
  endcase // case (r_ex3_pipe_ctrl.op)
end // always_comb

logic                                      w_ex2_commit_flush;
logic                                      w_ex2_br_flush;
logic                                      w_ex2_flush;
assign w_ex2_commit_flush = commit_if.is_flushed_commit();
assign w_ex2_br_flush     = scariv_pkg::is_br_flush_target(r_ex2_issue.cmt_id, r_ex2_issue.grp_id, br_upd_if.cmt_id, br_upd_if.grp_id,
                                                           br_upd_if.dead, br_upd_if.mispredict) & br_upd_if.update;
assign w_ex2_flush = w_ex2_commit_flush | w_ex2_br_flush;


always_ff @(posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    // r_ex3_result <= 'h0;
    r_ex3_index <= 'h0;
    r_ex3_issue <= 'h0;
    r_ex3_wr_valid  <= 1'b0;
    r_ex3_pipe_ctrl <= 'h0;
    r_ex3_res_data  <= 'h0;
    r_ex3_frm_invalid <= 1'b0;
  end else begin
    r_ex3_issue <= r_ex2_issue;
    r_ex3_index <= r_ex2_index;
    r_ex3_wr_valid  <= r_ex2_wr_valid;
    r_ex3_pipe_ctrl <= r_ex2_pipe_ctrl;
    r_ex3_res_data  <= w_ex2_res_data;
    r_ex3_frm_invalid <= r_ex2_frm_invalid;
  end
end

// ----------------------
// FPNew Pipeline
// ----------------------
scariv_pkg::cmt_id_t       w_fpnew_cmt_id;
scariv_pkg::grp_id_t       w_fpnew_grp_id;
scariv_pkg::rnid_t         w_fpnew_rnid;
scariv_pkg::reg_t          w_fpnew_reg_type;
logic                      w_fpnew_frm_invalid;

scariv_fpnew_wrapper
u_scariv_fpnew_wrapper
  (
   .i_clk     (i_clk    ),
   .i_reset_n (i_reset_n),

   .commit_if  (commit_if),
   .br_upd_if (br_upd_if),

   .i_valid (r_ex2_issue.valid & w_ex2_fpnew_valid & (&(~r_ex2_rs_mispred))),
   .i_pipe_ctrl (r_ex2_pipe_ctrl),
   .i_cmt_id    (r_ex2_issue.cmt_id),
   .i_grp_id    (r_ex2_issue.grp_id),
   .i_rnid      (r_ex2_issue.wr_reg.rnid),
   .i_frm_invalid (r_ex2_frm_invalid),
   .i_reg_type  (r_ex2_issue.wr_reg.typ),
   .i_rnd_mode  (r_ex2_issue.inst[14:12] == 3'b111 ? csr_info.fcsr[ 7: 5] : r_ex2_issue.inst[14:12]),

   .o_busy (w_fpnew_busy),

   .i_rs1 (w_ex2_rs1_selected_data),
   .i_rs2 (w_ex2_rs2_selected_data),
   .i_rs3 (w_ex2_rs3_selected_data),

   .o_valid      (w_fpnew_result_valid ),
   .o_result     (w_fpnew_result_data  ),
   .o_fflags     (w_fpnew_result_fflags),
   .o_cmt_id     (w_fpnew_cmt_id       ),
   .o_grp_id     (w_fpnew_grp_id       ),
   .o_rnid       (w_fpnew_rnid         ),
   .o_frm_invalid (w_fpnew_frm_invalid),
   .o_reg_type   (w_fpnew_reg_type     )
   );


always_comb begin
  ex3_mv_phy_wr_if.valid   = r_ex3_wr_valid & ~r_ex3_frm_invalid & (r_ex3_pipe_ctrl.pipe == PIPE_FAST);
  ex3_mv_phy_wr_if.rd_rnid = r_ex3_issue.wr_reg.rnid;
  ex3_mv_phy_wr_if.rd_type = r_ex3_issue.wr_reg.typ;
  ex3_mv_phy_wr_if.rd_data = r_ex3_res_data;

  mv_done_report_if.valid               = r_ex3_issue.valid & r_ex3_wr_valid & (r_ex3_pipe_ctrl.pipe == PIPE_FAST);
  mv_done_report_if.cmt_id              = r_ex3_issue.cmt_id;
  mv_done_report_if.grp_id              = r_ex3_issue.grp_id;
  mv_done_report_if.except_valid        = r_ex3_frm_invalid;
  mv_done_report_if.except_type         = scariv_pkg::ILLEGAL_INST;
  mv_done_report_if.fflags_update_valid = 1'b0;
  mv_done_report_if.fflags              = 'h0;

  fpnew_phy_wr_if.valid   = w_fpnew_result_valid;
  fpnew_phy_wr_if.rd_rnid = w_fpnew_rnid;
  fpnew_phy_wr_if.rd_type = w_fpnew_reg_type;
  fpnew_phy_wr_if.rd_data = w_fpnew_result_data;

  fp_done_report_if.valid               = w_fpnew_result_valid;
  fp_done_report_if.cmt_id              = w_fpnew_cmt_id;
  fp_done_report_if.grp_id              = w_fpnew_grp_id;
  fp_done_report_if.except_valid        = w_fpnew_frm_invalid;
  fp_done_report_if.except_type         = scariv_pkg::ILLEGAL_INST;
  fp_done_report_if.fflags_update_valid = w_fpnew_result_valid;
  fp_done_report_if.fflags              = w_fpnew_result_fflags;

end // always_comb


endmodule // scariv_fpu_pipe
