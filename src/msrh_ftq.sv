// ------------------------------------------------------------------------
// NAME : MRSH Fetch Target Queue
// TYPE : module
// ------------------------------------------------------------------------
// FTQ remembers the order of branch instruction.
// ------------------------------------------------------------------------
//
// ------------------------------------------------------------------------

typedef struct packed {
  logic                                                valid;
  logic                                                is_call;
  logic                                                is_ret;
  logic [msrh_pkg::CMT_ID_W-1:0]                       cmt_id;
  logic [msrh_pkg::DISP_SIZE-1:0]                      grp_id;
  logic [msrh_pkg::RAS_W-1: 0]                         ras_index;
  logic [$clog2(msrh_conf_pkg::RV_BRU_ENTRY_SIZE)-1:0] brtag;
  logic [msrh_conf_pkg::RV_BRU_ENTRY_SIZE-1:0]         br_mask;

  logic [riscv_pkg::VADDR_W-1: 0]                      target_vaddr;
  logic                                                taken;
  logic                                                mispredict;
  logic                                                done;
  logic                                                dead;
} ftq_entry_t;

function ftq_entry_t assign_ftq_entry(logic [msrh_pkg::CMT_ID_W-1:0]  cmt_id,
                                      logic [msrh_pkg::DISP_SIZE-1:0] grp_id,
                                      msrh_pkg::disp_t inst);
  ftq_entry_t ret;

  ret.valid    = 1'b1;
  ret.is_call  = inst.is_call;
  ret.is_ret   = inst.is_ret;
  ret.cmt_id   = cmt_id;
  ret.grp_id   = grp_id;
  ret.ras_index = inst.ras_index;
  ret.brtag     = inst.brtag;
  ret.br_mask   = inst.br_mask;

  ret.done      = 1'b0;
  ret.dead      = 1'b0;

  return ret;

endfunction // assign_ftq_entry

module msrh_ftq
  (
   input logic i_clk,
   input logic i_reset_n,

   disp_if.watch   sc_disp,
   br_upd_if.slave br_upd_if,

   // Fetch direction update to Frontend
   br_upd_if.master br_upd_fe_if
   );

localparam FTQ_SIZE = msrh_conf_pkg::RV_BRU_ENTRY_SIZE;

logic          w_in_valid;
logic          w_out_valid;
logic [FTQ_SIZE-1: 0] w_in_ptr_oh;
logic [FTQ_SIZE-1: 0] w_out_ptr_oh;

ftq_entry_t r_ftq_entry[FTQ_SIZE];
ftq_entry_t w_out_ftq_entry;

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


msrh_pkg::disp_t w_sc_br_inst;
logic [msrh_conf_pkg::DISP_SIZE-1: 0] sc_br_inst_array;
generate for (genvar d_idx = 0; d_idx < msrh_conf_pkg::DISP_SIZE; d_idx++) begin : sc_disp_loop
  assign sc_br_inst_array[d_idx] = sc_disp.inst[d_idx].valid &
                                   (sc_disp.inst[d_idx].cat == decoder_inst_cat_pkg::INST_CAT_BR);
end
endgenerate

bit_oh_or_packed #(.T(msrh_pkg::disp_t), .WORDS(msrh_conf_pkg::DISP_SIZE))
bit_br_select(.i_oh(sc_br_inst_array), .i_data(sc_disp.inst), .o_selected(w_sc_br_inst));

generate for (genvar e_idx = 0; e_idx < FTQ_SIZE; e_idx++) begin : entry_loop
  logic w_load;
  ftq_entry_t w_ftq_entry_next;
  assign w_load = w_in_valid & w_in_ptr_oh[e_idx];

  always_comb begin
    w_ftq_entry_next = r_ftq_entry[e_idx];

    if (w_load) begin
      w_ftq_entry_next = assign_ftq_entry (sc_disp.cmt_id,
                                           sc_br_inst_array,
                                           w_sc_br_inst);
    end else if (w_out_valid & w_out_ptr_oh[e_idx]) begin
      w_ftq_entry_next.valid = 1'b0;
    end else begin
      if (br_upd_if.update & r_ftq_entry[e_idx].valid &
          (br_upd_if.cmt_id == r_ftq_entry[e_idx].cmt_id) &
          (br_upd_if.grp_id == r_ftq_entry[e_idx].grp_id)) begin
        w_ftq_entry_next.done       = 1'b1;
        w_ftq_entry_next.dead       = br_upd_if.dead;
        w_ftq_entry_next.taken      = br_upd_if.taken;
        w_ftq_entry_next.mispredict = br_upd_if.mispredict;
        w_ftq_entry_next.target_vaddr = br_upd_if.target_vaddr;
      end
    end // else: !if(w_load)
  end // always_comb

  always_ff @ (negedge i_clk, negedge i_reset_n) begin
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

assign br_upd_fe_if.update       = w_out_ftq_entry.valid &
                                   w_out_ftq_entry.done;
assign br_upd_fe_if.taken        = w_out_ftq_entry.taken;
assign br_upd_fe_if.mispredict   = w_out_ftq_entry.mispredict;
assign br_upd_fe_if.is_call      = w_out_ftq_entry.is_call;
assign br_upd_fe_if.is_ret       = w_out_ftq_entry.is_ret;
assign br_upd_fe_if.ras_index    = w_out_ftq_entry.ras_index;
assign br_upd_fe_if.bim_value    = 'h0;
assign br_upd_fe_if.pc_vaddr     = 'h0;
assign br_upd_fe_if.target_vaddr = w_out_ftq_entry.target_vaddr;
assign br_upd_fe_if.dead         = w_out_ftq_entry.dead;
assign br_upd_fe_if.cmt_id       = w_out_ftq_entry.cmt_id;
assign br_upd_fe_if.grp_id       = w_out_ftq_entry.grp_id;
assign br_upd_fe_if.brtag        = 'h0;
assign br_upd_fe_if.br_mask      = 'h0;

endmodule // msrh_ftq
