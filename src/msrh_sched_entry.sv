module msrh_sched_entry
  #(
    parameter IS_STORE = 1'b0,
    parameter IS_BRANCH = 1'b0,
    parameter EN_OLDEST = 1'b0
    )
(
   input logic                                 i_clk,
   input logic                                 i_reset_n,

   // ROB notification interface
   rob_info_if.slave                           rob_info_if,

   input logic                                 i_put,
   input logic [msrh_pkg::CMT_ID_W-1:0]        i_cmt_id,
   input logic [msrh_conf_pkg::DISP_SIZE-1:0]  i_grp_id,
   input                                       msrh_pkg::disp_t i_put_data,

   output logic                                o_entry_valid,
   output logic                                o_entry_ready,
   output                                      msrh_pkg::issue_t o_entry,

   input logic                                 i_ex0_rs_conflicted,

   /* Forwarding path */
   input                                       msrh_pkg::early_wr_t i_early_wr[msrh_pkg::REL_BUS_SIZE],
   input                                       msrh_pkg::phy_wr_t i_phy_wr [msrh_pkg::TGT_BUS_SIZE],
   input                                       msrh_pkg::mispred_t i_mispred_lsu[msrh_conf_pkg::LSU_INST_NUM],

   input logic                                 i_entry_picked,

   // Done Interface
   input logic                                 i_pipe_done,
                                               done_if.slave pipe_done_if,

   // Commit notification
   input                                       msrh_pkg::commit_blk_t i_commit,
   // Branch Flush Notification
   br_upd_if.slave                             br_upd_if,

   output logic                                o_entry_done,
   output logic                                o_entry_wait_complete,
   output logic                                o_entry_finish,
   output logic [msrh_pkg::CMT_ID_W-1:0]       o_cmt_id,
   output logic [msrh_conf_pkg::DISP_SIZE-1:0] o_grp_id,
   output logic                                o_except_valid,
   output                                      msrh_pkg::except_t o_except_type
   );

logic    r_issued;
logic    r_dead;
msrh_pkg::issue_t r_entry;
msrh_pkg::issue_t w_entry;
msrh_pkg::issue_t w_init_entry;

logic    w_oldest_ready;

logic [msrh_pkg::RNID_W-1:0] w_rs1_rnid;
logic [msrh_pkg::RNID_W-1:0] w_rs2_rnid;
msrh_pkg::reg_t w_rs1_type;
msrh_pkg::reg_t w_rs2_type;

logic     w_rs1_rel_hit;
logic     w_rs2_rel_hit;

logic     w_rs1_may_mispred;
logic     w_rs2_may_mispred;

logic     w_rs1_phy_hit;
logic     w_rs2_phy_hit;

logic     w_rs1_mispredicted;
logic     w_rs2_mispredicted;

logic     w_entry_flush;
logic     w_commit_flush;
logic     w_br_flush;
logic     w_entry_complete;
logic     w_dead_state_clear;

// When previous instruction generates exception or jump
logic w_pc_update_before_entry;

msrh_pkg::sched_state_t r_state;

function logic all_operand_ready(msrh_pkg::issue_t entry);
  logic     ret;
  if (IS_STORE) begin
    ret = (!entry.rs1_valid | entry.rs1_valid  & (entry.rs1_ready | entry.rs1_pred_ready));
  end else begin
    ret = (!entry.rs1_valid | entry.rs1_valid  & (entry.rs1_ready | entry.rs1_pred_ready)) &
          (!entry.rs2_valid | entry.rs2_valid  & (entry.rs2_ready | entry.rs2_pred_ready));
  end
  return ret;
endfunction // all_operand_ready

assign w_rs1_rnid = i_put ? i_put_data.rs1_rnid : r_entry.rs1_rnid;
assign w_rs2_rnid = i_put ? i_put_data.rs2_rnid : r_entry.rs2_rnid;

assign w_rs1_type = i_put ? i_put_data.rs1_type : r_entry.rs1_type;
assign w_rs2_type = i_put ? i_put_data.rs2_type : r_entry.rs2_type;

select_early_wr_bus rs1_rel_select
(
 .i_entry_rnid (w_rs1_rnid),
 .i_entry_type (w_rs1_type),
 .i_early_wr   (i_early_wr),

 .o_valid      (w_rs1_rel_hit),
 .o_may_mispred(w_rs1_may_mispred)
 );


select_early_wr_bus rs2_rel_select
(
 .i_entry_rnid (w_rs2_rnid),
 .i_entry_type (w_rs2_type),
 .i_early_wr   (i_early_wr),

 .o_valid      (w_rs2_rel_hit),
 .o_may_mispred(w_rs2_may_mispred)
 );

select_phy_wr_bus rs1_phy_select
(
 .i_entry_rnid (w_rs1_rnid),
 .i_entry_type (w_rs1_type),
 .i_phy_wr     (i_phy_wr),

 .o_valid      (w_rs1_phy_hit)
 );


select_phy_wr_bus rs2_phy_select
(
 .i_entry_rnid (w_rs2_rnid),
 .i_entry_type (w_rs2_type),
 .i_phy_wr     (i_phy_wr),

 .o_valid      (w_rs2_phy_hit)
 );


select_mispred_bus rs1_mispred_select
(
 .i_entry_rnid (w_rs1_rnid),
 .i_entry_type (w_rs1_type),
 .i_mispred    (i_mispred_lsu),

 .o_mispred    (w_rs1_mispredicted)
 );


select_mispred_bus rs2_mispred_select
(
 .i_entry_rnid (w_rs2_rnid),
 .i_entry_type (w_rs2_type),
 .i_mispred    (i_mispred_lsu),

 .o_mispred    (w_rs2_mispredicted)
 );


always_comb begin
  w_entry = r_entry;
  w_entry.rs1_ready = r_entry.rs1_ready /* | r_entry.rs1_pred_ready */ | (w_rs1_rel_hit & ~w_rs1_may_mispred) | w_rs1_phy_hit;
  w_entry.rs2_ready = r_entry.rs2_ready /* | r_entry.rs2_pred_ready */ | (w_rs2_rel_hit & ~w_rs2_may_mispred) | w_rs2_phy_hit;

  w_entry.rs1_pred_ready = w_rs1_rel_hit & w_rs1_may_mispred;
  w_entry.rs2_pred_ready = w_rs2_rel_hit & w_rs2_may_mispred;
end


assign w_init_entry = msrh_pkg::assign_issue_t(i_put_data, i_cmt_id, i_grp_id,
                                               w_rs1_rel_hit, w_rs2_rel_hit,
                                               w_rs1_phy_hit, w_rs2_phy_hit,
                                               w_rs1_may_mispred, w_rs2_may_mispred);

assign w_commit_flush = msrh_pkg::is_commit_flush_target(r_entry.cmt_id, r_entry.grp_id, i_commit) & r_entry.valid;
assign w_br_flush     = msrh_pkg::is_br_flush_target(r_entry.br_mask, br_upd_if.brtag) & br_upd_if.update & r_entry.valid;
assign w_entry_flush = w_commit_flush | w_br_flush;

// assign w_entry_to_dead = w_entry_flush &
// (i_commit.cmt_id != r_entry.cmt_id);
assign w_dead_state_clear = i_commit.commit &
                            /* i_commit.all_dead & */
                            (i_commit.cmt_id == r_entry.cmt_id);

assign w_entry_complete = (i_commit.commit & (i_commit.cmt_id == r_entry.cmt_id));

always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_entry <= 'h0;

    r_state <= msrh_pkg::INIT;
    r_issued <= 1'b0;
    r_dead   <= 1'b0;
  end else begin
    case (r_state)
      msrh_pkg::INIT : begin
        if (w_entry_flush) begin
          r_state <= msrh_pkg::INIT;
        end else if (i_put) begin
          r_entry <= w_init_entry;
          r_state <= msrh_pkg::WAIT;
        end
      end
      msrh_pkg::WAIT : begin
        if (w_entry_flush) begin
          r_state <= msrh_pkg::DEAD;
          r_dead  <= 1'b1;
        end else begin
          r_entry <= w_entry;
          if (o_entry_valid & w_pc_update_before_entry & w_oldest_ready) begin
            r_state <= msrh_pkg::DONE;
          end else if (o_entry_valid & o_entry_ready & i_entry_picked) begin
            r_issued <= 1'b1;
            r_state <= msrh_pkg::ISSUED;
          end
        end
      end
      msrh_pkg::ISSUED : begin
        if (w_entry_flush) begin
          r_state <= msrh_pkg::DEAD;
          r_dead  <= 1'b1;
        end else begin
          if (i_pipe_done) begin
            r_state <= msrh_pkg::DONE;
            r_entry.except_valid <= pipe_done_if.except_valid;
            r_entry.except_type  <= pipe_done_if.except_type;
          end
          if (i_ex0_rs_conflicted) begin
            r_state <= msrh_pkg::WAIT;
            r_issued <= 1'b0;
          end
          if (r_entry.rs1_pred_ready & w_rs1_mispredicted ||
              r_entry.rs2_pred_ready & w_rs2_mispredicted) begin
            r_state <= msrh_pkg::WAIT;
            r_issued <= 1'b0;
            r_entry.rs1_pred_ready <= 1'b0;
            r_entry.rs2_pred_ready <= 1'b0;
          end
        end
      end
      msrh_pkg::DONE : begin
        if (w_entry_flush) begin
          r_state <= msrh_pkg::DEAD;
          r_dead  <= 1'b1;
        end else begin
          if (IS_BRANCH & w_entry_complete) begin
            // Branch updates ROB from EX3 stage, may become commit in DONE (one cycle earlier).
            r_state <= msrh_pkg::INIT;
            r_entry.valid <= 1'b0;
            r_issued <= 1'b0;
            r_dead   <= 1'b0;
            // prevent all updates from Pipeline
            r_entry.cmt_id <= 'h0;
            r_entry.grp_id <= 'h0;
          end else begin
            r_state <= msrh_pkg::WAIT_COMPLETE;
          end // else: !if(IS_BRANCH & w_entry_complete)
        end
      end
      msrh_pkg::WAIT_COMPLETE : begin
        /* if (w_entry_to_dead) begin
          r_state <= msrh_pkg::DEAD;
        end else */
        if (w_entry_complete) begin
          r_state <= msrh_pkg::INIT;
          r_entry.valid <= 1'b0;
          r_issued <= 1'b0;
          r_dead   <= 1'b0;
          // prevent all updates from Pipeline
          r_entry.cmt_id <= 'h0;
          r_entry.grp_id <= 'h0;
        end
      end
      msrh_pkg::DEAD : begin
        if (w_dead_state_clear) begin
          r_state       <= msrh_pkg::INIT;
          r_entry.valid <= 1'b0;
          r_issued      <= 1'b0;
          r_dead        <= 1'b0;
          // prevent all updates from Pipeline
          r_entry.cmt_id <= 'h0;
          r_entry.grp_id <= 'h0;
        end
      end // case: msrh_pkg::DEAD
      default : begin
        r_state <= msrh_pkg::INIT;
`ifdef SIMULATION
        $fatal(0, "Unknown state reached\n");
`endif // SIMULATION
      end
    endcase // case (r_state)
  end // else: !if(!i_reset_n)
end

generate if (EN_OLDEST == 1'b1) begin
  assign w_oldest_ready = (rob_info_if.cmt_id == r_entry.cmt_id) &
                          ((rob_info_if.done_grp_id & r_entry.grp_id-1) == r_entry.grp_id-1);
  assign w_pc_update_before_entry = |((r_entry.grp_id - 1) & (rob_info_if.upd_pc_valid | rob_info_if.except_valid) & rob_info_if.done_grp_id);
end else begin
  assign w_oldest_ready = 1'b1;
  assign w_pc_update_before_entry = 1'b0;
end
endgenerate


assign o_entry_valid = r_entry.valid;
assign o_entry_ready = r_entry.valid & !(r_issued | r_dead) & !w_entry_flush &
                       w_oldest_ready & !w_pc_update_before_entry & all_operand_ready(w_entry);
assign o_entry       = w_entry;

assign o_entry_done          = (r_state == msrh_pkg::DONE) & !w_entry_flush;
assign o_entry_wait_complete = (r_state == msrh_pkg::WAIT_COMPLETE);
assign o_cmt_id = r_entry.cmt_id;
assign o_grp_id = r_entry.grp_id;
assign o_except_valid = r_entry.except_valid;
assign o_except_type  = r_entry.except_type;
assign o_entry_finish = (r_state == msrh_pkg::DEAD) & w_dead_state_clear |
                        ((r_state == msrh_pkg::DONE) | (r_state == msrh_pkg::WAIT_COMPLETE)) & w_entry_complete;

endmodule // msrh_sched_entry
