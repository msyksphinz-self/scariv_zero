module msrh_bru_pipe
  import decoder_bru_ctrl_pkg::*;
#(
  parameter RV_ENTRY_SIZE = 32
  )
(
  input logic                       i_clk,
  input logic                       i_reset_n,

  input                             msrh_pkg::issue_t rv0_issue,
  input logic [RV_ENTRY_SIZE-1:0]   rv0_index,
  input                             msrh_pkg::phy_wr_t ex1_i_phy_wr[msrh_pkg::TGT_BUS_SIZE],

  // Commit notification
  input msrh_pkg::commit_blk_t      i_commit,

  input msrh_pkg::mispred_t         i_mispred_lsu[msrh_conf_pkg::LSU_INST_NUM],

 regread_if.master ex1_regread_rs1,
 regread_if.master ex1_regread_rs2,

  output                            msrh_pkg::early_wr_t o_ex1_early_wr,
  output                            msrh_pkg::phy_wr_t o_ex3_phy_wr,

  done_if.master   ex3_done_if,
  br_upd_if.master ex3_br_upd_if
);

typedef struct packed {
  op_t  op;
  imm_t imm;
  logic wr_rd;
} pipe_ctrl_t;

logic   w_commit_flushed;

msrh_pkg::issue_t                        r_ex0_issue;
logic [RV_ENTRY_SIZE-1: 0] w_ex0_index;
pipe_ctrl_t                              w_ex0_pipe_ctrl;
logic                      w_ex0_br_flush;

pipe_ctrl_t                              r_ex1_pipe_ctrl;
msrh_pkg::issue_t                        r_ex1_issue;
msrh_pkg::issue_t                        w_ex1_issue_next;
logic [RV_ENTRY_SIZE-1: 0] r_ex1_index;
logic                      w_ex1_br_flush;
logic                      r_ex1_dead;

logic [msrh_pkg::TGT_BUS_SIZE-1:0] w_ex2_rs1_fwd_valid;
logic [msrh_pkg::TGT_BUS_SIZE-1:0] w_ex2_rs2_fwd_valid;
logic            [riscv_pkg::XLEN_W-1:0] w_ex2_tgt_data          [msrh_pkg::TGT_BUS_SIZE];
logic            [riscv_pkg::XLEN_W-1:0] w_ex2_rs1_fwd_data;
logic            [riscv_pkg::XLEN_W-1:0] w_ex2_rs2_fwd_data;

logic            [riscv_pkg::XLEN_W-1:0] w_ex2_rs1_selected_data;
logic            [riscv_pkg::XLEN_W-1:0] w_ex2_rs2_selected_data;

logic                                    w_ex2_rs1_pred_hit;
logic                                    w_ex2_rs2_pred_hit;

logic                                    w_ex1_rs1_lsu_mispred;
logic                                    w_ex1_rs2_lsu_mispred;
logic                                    w_ex1_rs1_mispred;
logic                                    w_ex1_rs2_mispred;

pipe_ctrl_t                              r_ex2_pipe_ctrl;
msrh_pkg::issue_t                        r_ex2_issue;
msrh_pkg::issue_t                        w_ex2_issue_next;
logic [RV_ENTRY_SIZE-1: 0]               r_ex2_index;
logic [riscv_pkg::XLEN_W-1:0]            r_ex2_rs1_data;
logic [riscv_pkg::XLEN_W-1:0]            r_ex2_rs2_data;
logic [riscv_pkg::VADDR_W-1: 0]          w_ex2_br_vaddr;
logic                                    r_ex2_wr_valid;
logic                                    w_ex2_br_flush;
logic                                    r_ex2_dead;

msrh_pkg::issue_t                        r_ex3_issue;
msrh_pkg::issue_t                        w_ex3_issue_next;
pipe_ctrl_t                              r_ex3_pipe_ctrl;
logic                                    r_ex3_result;
logic [RV_ENTRY_SIZE-1: 0]               r_ex3_index;
logic [riscv_pkg::VADDR_W-1: 0]          r_ex3_br_vaddr;
logic                                    r_ex3_rs1_pred_hit;
logic                                    r_ex3_rs2_pred_hit;
logic                                    r_ex3_dead;

always_comb begin
  r_ex0_issue = rv0_issue;
  w_ex0_index = rv0_index;
end

decoder_bru_ctrl u_pipe_ctrl (
  .inst(r_ex0_issue.inst),
  .op  (w_ex0_pipe_ctrl.op),
  .imm (w_ex0_pipe_ctrl.imm),
  .wr_rd (w_ex0_pipe_ctrl.wr_rd)
);

assign ex1_regread_rs1.valid = r_ex1_issue.valid & r_ex1_issue.rs1_valid;
assign ex1_regread_rs1.rnid  = r_ex1_issue.rs1_rnid;

assign ex1_regread_rs2.valid = r_ex1_issue.valid & r_ex1_issue.rs2_valid;
assign ex1_regread_rs2.rnid  = r_ex1_issue.rs2_rnid;

// EX0 brtag flush check
assign w_ex0_br_flush  = msrh_pkg::is_br_flush_target(r_ex0_issue.br_mask, ex3_br_upd_if.brtag) & ex3_br_upd_if.update & ~ex3_br_upd_if.dead & ex3_br_upd_if.mispredict & r_ex0_issue.valid;

always_comb begin
  w_ex1_issue_next = r_ex0_issue;
end

always_ff @(posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_ex1_issue <= 'h0;
    r_ex1_index <= 'h0;
    r_ex1_pipe_ctrl <= 'h0;
    r_ex1_dead <= 1'b0;
  end else begin
    r_ex1_issue <= r_ex0_issue;
    r_ex1_index <= w_ex0_index;
    r_ex1_pipe_ctrl <= w_ex0_pipe_ctrl;
    r_ex1_dead <= r_ex0_issue.valid & (w_ex0_br_flush | w_commit_flushed);
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

assign w_commit_flushed = msrh_pkg::is_flushed_commit(i_commit);


assign w_ex1_rs1_mispred = r_ex1_issue.rs1_valid & r_ex1_issue.rs1_pred_ready ? w_ex1_rs1_lsu_mispred : 1'b0;
assign w_ex1_rs2_mispred = r_ex1_issue.rs2_valid & r_ex1_issue.rs2_pred_ready ? w_ex1_rs2_lsu_mispred : 1'b0;

assign o_ex1_early_wr.valid = r_ex1_issue.valid & r_ex1_issue.rd_valid &
                              ~w_ex1_rs1_mispred & ~w_ex1_rs2_mispred;
assign o_ex1_early_wr.rd_rnid = r_ex1_issue.rd_rnid;
assign o_ex1_early_wr.rd_type = msrh_pkg::GPR;
assign o_ex1_early_wr.may_mispred = 1'b0;

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

// EX1 brtag flush check
assign w_ex1_br_flush  = msrh_pkg::is_br_flush_target(r_ex1_issue.br_mask, ex3_br_upd_if.brtag) & ex3_br_upd_if.update & ~ex3_br_upd_if.dead & ex3_br_upd_if.mispredict & r_ex1_issue.valid;

always_comb begin
  w_ex2_issue_next = r_ex1_issue;
end

always_ff @(posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_ex2_rs1_data <= 'h0;
    r_ex2_rs2_data <= 'h0;

    r_ex2_issue <= 'h0;
    r_ex2_index <= 'h0;
    r_ex2_pipe_ctrl <= 'h0;
    r_ex2_dead <= 1'b0;

    r_ex2_wr_valid <= 1'b0;
  end else begin
    r_ex2_rs1_data <= ex1_regread_rs1.data;
    r_ex2_rs2_data <= ex1_regread_rs2.data;

    r_ex2_issue <= w_ex2_issue_next;
    r_ex2_index <= r_ex1_index;
    r_ex2_pipe_ctrl <= r_ex1_pipe_ctrl;
    r_ex2_dead <= r_ex1_dead | r_ex1_issue.valid & (w_ex1_br_flush | w_commit_flushed);

    r_ex2_wr_valid <= o_ex1_early_wr.valid;
  end
end

assign w_ex2_rs1_selected_data = |w_ex2_rs1_fwd_valid ? w_ex2_rs1_fwd_data : r_ex2_rs1_data;
assign w_ex2_rs2_selected_data = |w_ex2_rs2_fwd_valid ? w_ex2_rs2_fwd_data : r_ex2_rs2_data;

assign w_ex2_rs1_pred_hit = r_ex2_issue.rs1_valid & r_ex2_issue.rs1_pred_ready ? |w_ex2_rs1_fwd_valid : 1'b1;
assign w_ex2_rs2_pred_hit = r_ex2_issue.rs2_valid & r_ex2_issue.rs2_pred_ready ? |w_ex2_rs2_fwd_valid : 1'b1;

// EX2 brtag flush check
assign w_ex2_br_flush  = msrh_pkg::is_br_flush_target(r_ex2_issue.br_mask, ex3_br_upd_if.brtag) & ex3_br_upd_if.update & ~ex3_br_upd_if.dead & ex3_br_upd_if.mispredict & r_ex3_issue.valid;

always_comb begin
  w_ex3_issue_next = r_ex2_issue;
end

always_ff @(posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_ex3_result   <= 'h0;
    r_ex3_index    <= 'h0;
    r_ex3_issue    <= 'h0;
    r_ex3_br_vaddr <= 'h0;
    r_ex3_pipe_ctrl <= 'h0;
    r_ex3_dead <= 1'b0;

    r_ex3_rs1_pred_hit <= 1'b0;
    r_ex3_rs2_pred_hit <= 1'b0;
  end else begin
    r_ex3_issue    <= w_ex3_issue_next;
    r_ex3_index    <= r_ex2_index;
    r_ex3_br_vaddr <= w_ex2_br_vaddr;
    r_ex3_pipe_ctrl <= r_ex2_pipe_ctrl;
    r_ex3_dead <= r_ex2_dead | r_ex2_issue.valid & (w_ex2_br_flush | w_commit_flushed);

    r_ex3_rs1_pred_hit <= w_ex2_rs1_pred_hit;
    r_ex3_rs2_pred_hit <= w_ex2_rs2_pred_hit;

    case (r_ex2_pipe_ctrl.op)
      OP_EQ : r_ex3_result <= w_ex2_rs1_selected_data == w_ex2_rs2_selected_data;
      OP_NE : r_ex3_result <= w_ex2_rs1_selected_data != w_ex2_rs2_selected_data;
      OP_LT : r_ex3_result <= $signed(w_ex2_rs1_selected_data) <  $signed(w_ex2_rs2_selected_data);
      OP_GE : r_ex3_result <= $signed(w_ex2_rs1_selected_data) >= $signed(w_ex2_rs2_selected_data);
      OP_LTU: r_ex3_result <= w_ex2_rs1_selected_data <  w_ex2_rs2_selected_data;
      OP_GEU: r_ex3_result <= w_ex2_rs1_selected_data >= w_ex2_rs2_selected_data;
      OP__  : r_ex3_result <= 1'b1;   // Unconditional Jump
      default : r_ex3_result <= 1'bx;
    endcase
  end
end

assign o_ex3_phy_wr.valid   = r_ex3_issue.valid &
                              r_ex3_pipe_ctrl.wr_rd & (r_ex3_issue.rd_regidx != 'h0) &
                              r_ex3_rs1_pred_hit & r_ex3_rs2_pred_hit;
assign o_ex3_phy_wr.rd_rnid = r_ex3_issue.rd_rnid;
assign o_ex3_phy_wr.rd_type = r_ex3_issue.rd_type;
assign o_ex3_phy_wr.rd_data = {{(riscv_pkg::XLEN_W-riscv_pkg::VADDR_W){r_ex3_issue.pc_addr[riscv_pkg::VADDR_W-1]}},
                               r_ex3_issue.pc_addr} + (r_ex3_issue.is_rvc ? 'h2 : 'h4);

assign ex3_done_if.done     = r_ex3_issue.valid & r_ex3_rs1_pred_hit & r_ex3_rs2_pred_hit;
assign ex3_done_if.index_oh = r_ex3_index;
assign ex3_done_if.except_valid  = 1'b0;
assign ex3_done_if.except_type = msrh_pkg::except_t'('h0);

logic [riscv_pkg::VADDR_W-1: 0] w_ex2_offset_uj;
logic [riscv_pkg::VADDR_W-1: 0] w_ex2_offset_sb;

assign w_ex2_offset_uj = {{(riscv_pkg::VADDR_W-21){r_ex2_issue.inst[31]}},
                          r_ex2_issue.inst[31],
                          r_ex2_issue.inst[19:12],
                          r_ex2_issue.inst[20],
                          r_ex2_issue.inst[30:21],
                          1'b0};
assign w_ex2_offset_sb = {{(riscv_pkg::VADDR_W-13){r_ex2_issue.inst[31]}},
                          r_ex2_issue.inst[31],
                          r_ex2_issue.inst[ 7],
                          r_ex2_issue.inst[30:25],
                          r_ex2_issue.inst[11: 8],
                          1'b0};

always_comb begin
  case (r_ex2_pipe_ctrl.imm)
    IMM_SB : w_ex2_br_vaddr = r_ex2_issue.pc_addr + w_ex2_offset_sb;
    IMM_UJ : w_ex2_br_vaddr = r_ex2_issue.pc_addr + w_ex2_offset_uj;
    IMM_I  : w_ex2_br_vaddr = w_ex2_rs1_selected_data[riscv_pkg::VADDR_W-1: 0] + {{(riscv_pkg::VADDR_W-12){r_ex2_issue.inst[31]}},
                                                                                  r_ex2_issue.inst[31:20]};
    default : w_ex2_br_vaddr = {riscv_pkg::VADDR_W{1'bx}};
  endcase // case (w_ex2_pipe_ctrl.imm)
end // always_comb

assign ex3_br_upd_if.update        = r_ex3_issue.valid & r_ex3_rs1_pred_hit & r_ex3_rs2_pred_hit;
assign ex3_br_upd_if.taken         = r_ex3_result;
assign ex3_br_upd_if.dead          = r_ex3_dead;
assign ex3_br_upd_if.mispredict    = ~r_ex3_issue.btb_valid & r_ex3_result |
                                      r_ex3_issue.btb_valid &
                                     ((r_ex3_result != r_ex3_issue.pred_taken) |
                                      (r_ex3_result & r_ex3_issue.pred_taken &
                                       (r_ex3_br_vaddr != r_ex3_issue.btb_target_vaddr)));
assign ex3_br_upd_if.bim_value     = r_ex3_issue.bim_value;
assign ex3_br_upd_if.pc_vaddr      = r_ex3_issue.is_rvc ? r_ex3_issue.pc_addr : r_ex3_issue.pc_addr + 'h2;
assign ex3_br_upd_if.target_vaddr  = r_ex3_result ? r_ex3_br_vaddr :
                                     r_ex3_issue.is_rvc ? r_ex3_issue.pc_addr + 'h2 : r_ex3_issue.pc_addr + 'h4;
assign ex3_br_upd_if.cmt_id        = r_ex3_issue.cmt_id;
assign ex3_br_upd_if.grp_id        = r_ex3_issue.grp_id;
assign ex3_br_upd_if.brtag         = r_ex3_issue.brtag;
assign ex3_br_upd_if.br_mask       = r_ex3_issue.br_mask;


`ifdef SIMULATION
logic [63: 0] r_cycle_count;
logic [10: 0] r_bru_valid_count;
logic [10: 0] r_bru_cmp_count;
logic [10: 0] r_bru_cmp_hit_count;
logic [10: 0] r_bru_ret_count;
logic [10: 0] r_bru_ret_hit_count;
logic [10: 0] r_bru_other_count;
logic [10: 0] r_bru_other_hit_count;

always_ff @ (negedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_cycle_count  <= 'h0;
  end else begin
    r_cycle_count <= r_cycle_count + 'h1;
  end
end

always_ff @ (negedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_bru_valid_count <= 'h0;
    r_bru_cmp_count <= 'h0;
    r_bru_cmp_hit_count    <= 'h0;
    r_bru_ret_count     <= 'h0;
    r_bru_ret_hit_count <= 'h0;
    r_bru_other_count     <= 'h0;
    r_bru_other_hit_count <= 'h0;
  end else begin
    if (r_cycle_count % sim_pkg::COUNT_UNIT == sim_pkg::COUNT_UNIT-1) begin
      r_bru_valid_count <= 'h0;
      r_bru_cmp_count <= 'h0;
      r_bru_cmp_hit_count <= 'h0;
      r_bru_ret_count     <= 'h0;
      r_bru_ret_hit_count <= 'h0;
      r_bru_other_count     <= 'h0;
      r_bru_other_hit_count <= 'h0;
    end else begin
      if (ex3_br_upd_if.update) begin
        r_bru_valid_count <= r_bru_valid_count + 'h1;
        if (r_ex3_pipe_ctrl.op != OP__) begin
          r_bru_cmp_count <= r_bru_cmp_count + 'h1;
          if (!ex3_br_upd_if.mispredict) begin
            r_bru_cmp_hit_count <= r_bru_cmp_hit_count + 'h1;
          end
        end else begin
          if (r_ex3_issue.inst == 32'h00008067) begin  // RET
            r_bru_ret_count <= r_bru_ret_count + 'h1;
            if (!ex3_br_upd_if.mispredict) begin
              r_bru_ret_hit_count <= r_bru_ret_hit_count + 'h1;
            end
          end else begin
            r_bru_other_count <= r_bru_other_count + 'h1;
            if (!ex3_br_upd_if.mispredict) begin
              r_bru_other_hit_count <= r_bru_other_hit_count + 'h1;
            end
          end // else: !if(r_ex3_issue.inst == 32'h00008082)
        end
      end
    end // else: !if(r_cycle_count % sim_pkg::COUNT_UNIT == sim_pkg::COUNT_UNIT-1)
  end // else: !if(!i_reset_n)
end // always_ff @ (negedge i_clk, negedge i_reset_n)

function void dump_perf (int fp);

  $fwrite(fp, "  \"branch\" : {");
  $fwrite(fp, "    \"execute\" : %5d, ", r_bru_valid_count);
  $fwrite(fp, "    \"cmp\" : { \"execute\" : %5d, \"hit\" : %5d }, ", r_bru_cmp_count, r_bru_cmp_hit_count);
  $fwrite(fp, "    \"uncond\" : { \"ret\" : { \"execute\" : %5d, \"hit\" : %5d}, ",
          r_bru_ret_count, r_bru_ret_hit_count);
  $fwrite(fp, "\"others\" : { \"execute\" : %5d, \"hit\" : %5d }}, ",
          r_bru_other_count, r_bru_other_hit_count);
  $fwrite(fp, "  },\n");

endfunction // dump_perfto

integer bim_fp;
initial begin
  bim_fp = $fopen("bru_detail.log", "w");
end

always_ff @ (negedge i_clk, negedge i_reset_n) begin
  if (i_reset_n) begin
    if (ex3_br_upd_if.update) begin
      if (r_ex3_pipe_ctrl.op != OP__) begin
        $fwrite(bim_fp, "%t : pc_vaddr = %08x, target_addr = %08x, %s, bim=%1d, %s, DASM(0x%08x)\n",
                $time,
                r_ex3_issue.pc_addr,
                ex3_br_upd_if.target_vaddr,
                r_ex3_result ? "Taken   " : "NotTaken",
                ex3_br_upd_if.bim_value,
                ex3_br_upd_if.mispredict ? "Miss" : "Succ",
                r_ex3_issue.inst);
      end
    end
  end
end // always_ff @ (negedge i_clk, negedge i_reset_n)

final begin
  $fclose(bim_fp);
end

`endif // SIMULATION

endmodule // msrh_bru_pipe
