// ------------------------------------------------------------------------
// NAME : scariv_vlsu_uop_gen
// TYPE : module
// ------------------------------------------------------------------------
// UOP Generator for Vector LSU
// ------------------------------------------------------------------------
//
// ------------------------------------------------------------------------

module scariv_vlsu_uop_gen
  import scariv_pkg::*;
# (
   parameter NUM_OPERANDS = 3
   )
(
 input logic  i_clk,
 input logic  i_reset_n,

 input another_flush_t i_pipe_flush_self,

 output logic o_ready,

 input scariv_vec_pkg::issue_t            i_issue,
 input logic                              i_replay_selected,
 input scariv_vec_pkg::vlsu_replay_info_t i_replay_info,

 output scariv_vec_pkg::issue_t            o_issue,
 output logic                              o_replay_selected,
 output scariv_vec_pkg::vlsu_replay_info_t o_replay_info,

 input logic  i_ready
 );

typedef enum logic {
   INIT = 0,
   UOP_GEN = 1
} state_t;

state_t r_state;
state_t w_state_next;
scariv_vec_pkg::issue_t r_uop;
scariv_vec_pkg::issue_t w_uop_next;
scariv_vec_pkg::vlsu_replay_info_t r_replay_info;
scariv_vec_pkg::vlsu_replay_info_t w_replay_info_next;
logic        r_replay_selected;
logic        w_replay_selected_next;

always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_state <= INIT;
  end else begin
    r_state           <= w_state_next;
    r_uop             <= w_uop_next;
    r_replay_info     <= w_replay_info_next;
    r_replay_selected <= w_replay_selected_next;
  end
end

logic w_is_last_uop;
assign w_is_last_uop = (i_issue.vec_lmul_index == scariv_vec_pkg::calc_num_req(i_issue)-1) &
                       ((scariv_vec_pkg::VEC_STEP_W == 1) |
                        (i_issue.vec_step_index == scariv_vec_pkg::VEC_STEP_W-1));

logic w_issue_vec_stex_max;
assign w_issue_vec_stex_max = (i_issue.vec_step_index == scariv_vec_pkg::VEC_STEP_W-1);

always_comb begin
  case (r_state)
    INIT : begin
      w_uop_next = i_issue;
      w_replay_info_next = i_replay_info;
      w_replay_selected_next = i_replay_selected;

      if (i_issue.valid & i_ready) begin
        if (!w_is_last_uop) begin
          w_state_next = UOP_GEN;
          w_uop_next.vec_step_index = i_issue.vec_step_index + 'h1;
          w_uop_next.vec_lmul_index = i_issue.vec_lmul_index + w_issue_vec_stex_max;

          for (int rs_idx = 0; rs_idx < NUM_OPERANDS; rs_idx++) begin
            if (i_issue.rd_regs[rs_idx].valid & i_issue.rd_regs[rs_idx].typ == scariv_pkg::VPR) begin
              w_uop_next.rd_regs[rs_idx].rnid = i_issue.rd_regs[rs_idx].rnid + w_issue_vec_stex_max;
            end
          end
          w_uop_next.wr_old_reg.rnid = i_issue.wr_old_reg.rnid + w_issue_vec_stex_max;
          w_uop_next.wr_reg.rnid     = i_issue.wr_reg.rnid + w_issue_vec_stex_max;

          w_replay_info_next.haz_1st_req = 1'b0;
        end // else: !if(i_issue.vec_lmul_index == (1 << i_issue.vlvtype.vtype.vlmul)-1)
      end // if (i_issue.valid)
    end // case: INIT
    UOP_GEN : begin
      if (i_pipe_flush_self.valid & (r_uop.cmt_id == i_pipe_flush_self.cmt_id) & (r_uop.grp_id == i_pipe_flush_self.grp_id)) begin
        w_state_next = INIT;
      end else if (i_ready) begin
        w_uop_next.vec_step_index = r_uop.vec_step_index + 'h1;
        if (r_uop.vec_step_index == scariv_vec_pkg::VEC_STEP_W-1) begin
          if (r_uop.vec_lmul_index == scariv_vec_pkg::calc_num_req(r_uop)-1) begin
            w_state_next = INIT;
            w_uop_next.vec_lmul_index = 'h0;
          end else begin
            w_uop_next.vec_lmul_index = r_uop.vec_lmul_index + 'h1;
          end

          for (int rs_idx = 0; rs_idx < NUM_OPERANDS; rs_idx++) begin
            if (r_uop.rd_regs[rs_idx].valid & r_uop.rd_regs[rs_idx].typ == scariv_pkg::VPR) begin
              w_uop_next.rd_regs[rs_idx].rnid = r_uop.rd_regs[rs_idx].rnid + 'h1;
            end
          end
          w_uop_next.wr_old_reg.rnid = r_uop.wr_old_reg.rnid + 'h1;
          w_uop_next.wr_reg.rnid     = r_uop.wr_reg.rnid + 'h1;
        end // else: !if(r_uop.vec_lmul_index == (1 << r_uop.vlvtype.vtype.vlmul)-1)
      end // if (i_ready)
    end // case: UOP_GEN
    default : begin
    end
  endcase // case (r_state)
end // always_comb

assign o_ready           = (r_state == INIT) & i_ready;
assign o_issue           = (r_state == INIT) ? i_issue           : r_uop;
assign o_replay_selected = (r_state == INIT) ? i_replay_selected : r_replay_selected;
assign o_replay_info     = (r_state == INIT) ? i_replay_info     : r_replay_info;


endmodule // scariv_vlsu_uop_gen
