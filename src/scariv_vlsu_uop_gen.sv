// ------------------------------------------------------------------------
// NAME : scariv_vlsu_address_gen
// TYPE : module
// ------------------------------------------------------------------------
// Address Generator for Vector LSU
// ------------------------------------------------------------------------
//
// ------------------------------------------------------------------------

module scariv_vlsu_uop_gen
(
 input logic i_clk,
 input logic i_reset_n,

 input logic i_valid,

 output scariv_vec_pkg::issue_t i_issue_entry,
 output scariv_vec_pkg::issue_t o_issue_entry
 );

typedef enum logic {
   INIT = 0,
   UOP_GEN = 1
} state_t;

state_t r_state;
state_t w_state_next;
scariv_vec_pkg::issue_t r_uop;
scariv_vec_pkg::issue_t w_uop_next;

always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_state <= INIT;
  end else begin
    r_state <= w_state_next;
    r_uop <= w_uop_next;
  end
end

always_comb begin
  case (r_state)
    INIT : begin
      w_uop_next = i_issue_entry;
      if (i_valid) begin
        if ((scariv_vec_pkg::VEC_STEP_W == 1) |
            (i_issue_entry.vec_step_index == scariv_vec_pkg::VEC_STEP_W-1)) begin
          if (i_issue_entry.vec_lmul_index != scariv_vec_pkg::calc_num_req(i_issue_entry)-1) begin
            w_state_next = UOP_GEN;
            w_uop_next.vec_lmul_index = i_issue_entry.vec_lmul_index + 'h1;
            w_uop_next.vec_step_index = i_issue_entry.vec_step_index + 'h1;
          end

          for (int rs_idx = 0; rs_idx < NUM_OPERANDS; rs_idx++) begin
            if (i_issue_entry.rd_regs[rs_idx].valid & i_issue_entry.rd_regs[rs_idx].typ == scariv_pkg::VPR) begin
              w_uop_next.rd_regs[rs_idx].rnid = i_issue_entry.rd_regs[rs_idx].rnid + 'h1;
            end
          end
          w_uop_next.wr_old_reg.rnid = i_issue_entry.wr_old_reg.rnid + 'h1;
          w_uop_next.wr_reg.rnid     = i_issue_entry.wr_reg.rnid + 'h1;
        end // else: !if(i_issue_entry.vec_lmul_index == (1 << i_issue_entry.vlvtype.vtype.vlmul)-1)
      end // if (i_valid)
    end // case: INIT
    UOP_GEN : begin
      if (i_issue_entry.vec_step_index == scariv_vec_pkg::VEC_STEP_W-1) begin
        if (i_issue_entry.vec_lmul_index == scariv_vec_pkg::calc_num_req(i_issue_entry)-1) begin
          w_state_next = UOP_GEN;
          w_uop_next.vec_lmul_index = i_issue_entry.vec_lmul_index + 'h1;
          w_uop_next.vec_step_index = i_issue_entry.vec_step_index + 'h1;
        end

        for (int rs_idx = 0; rs_idx < NUM_OPERANDS; rs_idx++) begin
          if (i_issue_entry.rd_regs[rs_idx].valid & i_issue_entry.rd_regs[rs_idx].typ == scariv_pkg::VPR) begin
            w_uop_next.rd_regs[rs_idx].rnid = i_issue_entry.rd_regs[rs_idx].rnid + 'h1;
          end
        end
        w_uop_next.wr_old_reg.rnid = i_issue_entry.wr_old_reg.rnid + 'h1;
        w_uop_next.wr_reg.rnid     = i_issue_entry.wr_reg.rnid + 'h1;
      end // else: !if(i_issue_entry.vec_lmul_index == (1 << i_issue_entry.vlvtype.vtype.vlmul)-1)
    end // if (i_valid)




endmodule // scariv_vlsu_uop_gen
