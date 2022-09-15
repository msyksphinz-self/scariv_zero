// ------------------------------------------------------------------------
// NAME : MRSH Fetch Target Queue
// TYPE : module
// ------------------------------------------------------------------------
// FTQ remembers the order of branch instruction.
// ------------------------------------------------------------------------
//
// ------------------------------------------------------------------------

module msrh_ftq
  import msrh_pkg::*;
  (
   input logic i_clk,
   input logic i_reset_n,

   disp_if.watch   sc_disp,
   br_upd_if.slave br_upd_if,

   output logic o_is_ftq_empty,

   // PC Update from Committer
   input msrh_pkg::commit_blk_t i_commit,

   // Fetch direction update to Frontend
   br_upd_if.master br_upd_fe_if
   );

localparam FTQ_SIZE = msrh_conf_pkg::RV_BRU_ENTRY_SIZE;

logic          w_in_valid;
logic          w_out_valid;
logic [FTQ_SIZE-1: 0] w_in_ptr_oh;
logic [FTQ_SIZE-1: 0] w_out_ptr_oh;

logic [FTQ_SIZE-1: 0] w_entry_valids;

logic                 w_commit_flush;

ftq_entry_t r_ftq_entry[FTQ_SIZE];
ftq_entry_t w_out_ftq_entry;

assign o_is_ftq_empty = (w_entry_valids == 'h0);

assign w_in_valid = sc_disp.valid &
                    sc_disp.ready &
                    sc_disp.is_br_included;
assign w_out_valid = w_out_ftq_entry.valid &
                     w_out_ftq_entry.done;

inoutptr_oh
  #(.SIZE(FTQ_SIZE))
u_ptr
  (
   .i_clk        (i_clk    ),
   .i_reset_n    (i_reset_n),

   .i_in_valid  (w_in_valid  ),
   .o_in_ptr    (w_in_ptr_oh ),
   .i_out_valid (w_out_valid ),
   .o_out_ptr   (w_out_ptr_oh)
   );

assign w_commit_flush = msrh_pkg::is_flushed_commit(i_commit);

disp_t w_sc_br_inst;
grp_id_t sc_br_inst_array;
generate for (genvar d_idx = 0; d_idx < msrh_conf_pkg::DISP_SIZE; d_idx++) begin : sc_disp_loop
  assign sc_br_inst_array[d_idx] = sc_disp.inst[d_idx].valid &
                                   (sc_disp.inst[d_idx].cat == decoder_inst_cat_pkg::INST_CAT_BR);
end
endgenerate

bit_oh_or_packed #(.T(disp_t), .WORDS(msrh_conf_pkg::DISP_SIZE))
bit_br_select(.i_oh(sc_br_inst_array), .i_data(sc_disp.inst), .o_selected(w_sc_br_inst));

generate for (genvar e_idx = 0; e_idx < FTQ_SIZE; e_idx++) begin : entry_loop
  logic w_load;
  ftq_entry_t w_ftq_entry_next;
  assign w_load = w_in_valid & w_in_ptr_oh[e_idx];

  assign w_entry_valids[e_idx] = r_ftq_entry[e_idx].valid;

  always_comb begin
    w_ftq_entry_next = r_ftq_entry[e_idx];

    if (w_load) begin
      w_ftq_entry_next = assign_ftq_entry (sc_disp.cmt_id,
                                           sc_br_inst_array,
                                           w_sc_br_inst);
    end

    if (w_out_valid & w_out_ptr_oh[e_idx]) begin
      w_ftq_entry_next.valid = 1'b0;
    end else if (br_upd_if.update & r_ftq_entry[e_idx].valid &
                 (br_upd_if.cmt_id == r_ftq_entry[e_idx].cmt_id) &
                 (br_upd_if.grp_id == r_ftq_entry[e_idx].grp_id)) begin
      w_ftq_entry_next.done       = 1'b1;
      w_ftq_entry_next.is_cond    = br_upd_if.is_cond;
      w_ftq_entry_next.dead       = br_upd_if.dead;
      w_ftq_entry_next.taken      = br_upd_if.taken;
      w_ftq_entry_next.mispredict = br_upd_if.mispredict;
      w_ftq_entry_next.target_vaddr = br_upd_if.target_vaddr;
    end
    if (w_commit_flush |
        br_upd_fe_if.update &
        (r_ftq_entry[e_idx].valid & is_br_flush_target (r_ftq_entry[e_idx].br_mask, br_upd_fe_if.brtag, br_upd_fe_if.dead, br_upd_fe_if.mispredict) |
         w_load &                   is_br_flush_target (w_ftq_entry_next.br_mask,   br_upd_fe_if.brtag, br_upd_fe_if.dead, br_upd_fe_if.mispredict))) begin
      w_ftq_entry_next.done       = 1'b1;
      w_ftq_entry_next.dead       = 1'b1;
    end // else: !if(w_load)
  end // always_comb

  always_ff @ (posedge i_clk, negedge i_reset_n) begin
    if (!i_reset_n) begin
      r_ftq_entry[e_idx].valid <= 1'b0;
    end else begin
      r_ftq_entry[e_idx] <= w_ftq_entry_next;
    end
  end

end
endgenerate

// ---------------------------------------
// Outputting Branch Result into Frontend
// ---------------------------------------

bit_oh_or #(.T(ftq_entry_t), .WORDS(FTQ_SIZE))
sel_out_entry
  (
   .i_oh      (w_out_ptr_oh),
   .i_data    (r_ftq_entry),
   .o_selected(w_out_ftq_entry)
   );

assign br_upd_fe_if.update           = w_out_ftq_entry.valid &
                                       w_out_ftq_entry.done;
assign br_upd_fe_if.taken            = w_out_ftq_entry.taken;
assign br_upd_fe_if.mispredict       = w_out_ftq_entry.mispredict;
assign br_upd_fe_if.is_cond          = w_out_ftq_entry.is_cond;
assign br_upd_fe_if.is_call          = w_out_ftq_entry.is_call;
assign br_upd_fe_if.is_ret           = w_out_ftq_entry.is_ret;
assign br_upd_fe_if.is_rvc           = w_out_ftq_entry.is_rvc;
assign br_upd_fe_if.ras_index        = w_out_ftq_entry.ras_index;
assign br_upd_fe_if.bim_value        = w_out_ftq_entry.bim_value;
assign br_upd_fe_if.pc_vaddr         = w_out_ftq_entry.pc_vaddr;
assign br_upd_fe_if.target_vaddr     = w_out_ftq_entry.target_vaddr;
assign br_upd_fe_if.ras_prev_vaddr   = w_out_ftq_entry.ras_prev_vaddr;
assign br_upd_fe_if.dead             = w_out_ftq_entry.dead;
assign br_upd_fe_if.cmt_id           = w_out_ftq_entry.cmt_id;
assign br_upd_fe_if.grp_id           = w_out_ftq_entry.grp_id;
assign br_upd_fe_if.brtag            = w_out_ftq_entry.brtag;
assign br_upd_fe_if.br_mask          = 'h0;
assign br_upd_fe_if.gshare_index     = w_out_ftq_entry.gshare_index;
assign br_upd_fe_if.gshare_bhr       = w_out_ftq_entry.gshare_bhr  ;


`ifdef SIMULATION
`ifdef MONITOR

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
      if (br_upd_fe_if.update & !br_upd_fe_if.dead) begin
        r_bru_valid_count <= r_bru_valid_count + 'h1;
        if (!br_upd_fe_if.is_call & !br_upd_fe_if.is_ret) begin
          r_bru_cmp_count <= r_bru_cmp_count + 'h1;
          if (!br_upd_fe_if.mispredict) begin
            r_bru_cmp_hit_count <= r_bru_cmp_hit_count + 'h1;
          end
        end else begin
          if (br_upd_fe_if.is_ret) begin  // RET
            r_bru_ret_count <= r_bru_ret_count + 'h1;
            if (!br_upd_fe_if.mispredict) begin
              r_bru_ret_hit_count <= r_bru_ret_hit_count + 'h1;
            end
          end else begin
            r_bru_other_count <= r_bru_other_count + 'h1;
            if (!br_upd_fe_if.mispredict) begin
              r_bru_other_hit_count <= r_bru_other_hit_count + 'h1;
            end
          end // else: !if(r_ex3_issue.inst == 32'h00008082)
        end // else: !if(!br_upd_fe_if.is_call & !br_upd_fe_if.is_ret)
      end // if (br_upd_fe_if.update & !br_upd_fe_if.dead)
    end // else: !if(r_cycle_count % sim_pkg::COUNT_UNIT == sim_pkg::COUNT_UNIT-1)
  end // else: !if(!i_reset_n)
end // always_ff @ (negedge i_clk, negedge i_reset_n)

function void dump_branch_perf (int fp);

  $fwrite(fp, "  \"branch\" : {");
  $fwrite(fp, "    \"execute\" : %5d, ", r_bru_valid_count);
  $fwrite(fp, "    \"cmp\" : { \"execute\" : %5d, \"hit\" : %5d }, ", r_bru_cmp_count, r_bru_cmp_hit_count);
  $fwrite(fp, "    \"uncond\" : { \"ret\" : { \"execute\" : %5d, \"hit\" : %5d}, ",
          r_bru_ret_count, r_bru_ret_hit_count);
  $fwrite(fp, "\"others\" : { \"execute\" : %5d, \"hit\" : %5d }}, ",
          r_bru_other_count, r_bru_other_hit_count);
  $fwrite(fp, "  },\n");

endfunction // dump_perfto

`endif // MONITOR
`endif // SIMULATION

endmodule // msrh_ftq
