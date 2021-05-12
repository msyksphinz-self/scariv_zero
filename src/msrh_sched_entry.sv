module msrh_sched_entry
  #(
    parameter IS_STORE = 1'b0,
    parameter EN_OLDEST = 1'b0
    )
(
   input logic                                 i_clk,
   input logic                                 i_reset_n,

   input logic                                 i_put,
   input logic [msrh_pkg::CMT_ID_W-1:0]       i_cmt_id,
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

   output logic                                o_entry_done,
   output logic                                o_entry_wait_complete,
   output logic                                o_entry_finish,
   output logic [msrh_pkg::CMT_ID_W-1:0]       o_cmt_id,
   output logic [msrh_conf_pkg::DISP_SIZE-1:0] o_grp_id,
   output logic                                o_except_valid,
   output                                      msrh_pkg::except_t o_except_type
   );

logic    r_issued;
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
// logic     w_entry_to_dead;
logic     w_entry_complete;
logic     w_dead_state_clear;

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

assign w_entry_flush = i_commit.commit &
                       i_commit.flush_valid &
                       !i_commit.all_dead &
                       r_entry.valid;
// assign w_entry_to_dead = w_entry_flush &
// (i_commit.cmt_id != r_entry.cmt_id);
assign w_dead_state_clear = i_commit.commit &
                            i_commit.all_dead &
                            (i_commit.cmt_id == r_entry.cmt_id);

assign w_entry_complete = (i_commit.commit & (i_commit.cmt_id == r_entry.cmt_id));

always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_entry <= 'h0;

    r_state <= msrh_pkg::INIT;
    r_issued <= 1'b0;
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
        end else begin
          r_entry <= w_entry;
          if (o_entry_valid & o_entry_ready & i_entry_picked) begin
            r_issued <= 1'b1;
            r_state <= msrh_pkg::ISSUED;
          end
        end
      end
      msrh_pkg::ISSUED : begin
        if (w_entry_flush) begin
          r_state <= msrh_pkg::DEAD;
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
        end else begin
          r_state <= msrh_pkg::WAIT_COMPLETE;
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
          // prevent all updates from Pipeline
          r_entry.cmt_id <= 'h0;
          r_entry.grp_id <= 'h0;
        end
      end // case: msrh_pkg::DEAD
      default : begin
        r_state <= msrh_pkg::INIT;
        $fatal(0, "Unknown state reached\n");
      end
    endcase // case (r_state)
  end // else: !if(!i_reset_n)
end

assign w_oldest_ready = EN_OLDEST ? (i_commit.cmt_id == r_entry.cmt_id) &
                        ((i_commit.grp_id & r_entry.grp_id-1) == r_entry.grp_id-1) :
                        1'b1;

assign o_entry_valid = r_entry.valid;
assign o_entry_ready = r_entry.valid & !r_issued & w_oldest_ready & all_operand_ready(w_entry);
assign o_entry       = w_entry;

assign o_entry_done          = (r_state == msrh_pkg::DONE) & !w_entry_flush;
assign o_entry_wait_complete = (r_state == msrh_pkg::WAIT_COMPLETE);
assign o_cmt_id = r_entry.cmt_id;
assign o_grp_id = r_entry.grp_id;
assign o_except_valid = r_entry.except_valid;
assign o_except_type  = r_entry.except_type;
assign o_entry_finish = (r_state == msrh_pkg::DEAD) & w_dead_state_clear |
                        (r_state == msrh_pkg::WAIT_COMPLETE) & w_entry_complete;

endmodule // msrh_sched_entry
