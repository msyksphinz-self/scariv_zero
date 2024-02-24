// ------------------------------------------------------------------------
// NAME : scariv_inst_buffer
// TYPE : module
// ------------------------------------------------------------------------
// SCARIV Instruction Buffer
// ------------------------------------------------------------------------
//
// ------------------------------------------------------------------------

module scariv_inst_buffer
  import scariv_pkg::*;
  import scariv_ic_pkg::*;
  import decoder_reg_pkg::*;
  (
 input logic i_clk,
 input logic i_reset_n,
 input logic i_flush_valid,

 /* CSR information */
 csr_info_if.slave                csr_info,

 btb_search_if.monitor    btb_search_if,
 bim_search_if.monitor    bim_search_if,
 ras_search_if.slave      ras_search_if,
 gshare_search_if.monitor gshare_search_if,

 input logic                           i_f2_ubtb_predict_valid,
 input scariv_predict_pkg::ubtb_info_t i_f2_ubtb_info,

 output decode_flush_t    o_decode_flush,

 output logic                       o_inst_ready,
 input scariv_pkg::inst_buffer_in_t i_f2_inst,
 scariv_front_if.master             ibuf_front_if,

 br_upd_if.slave br_upd_if
 );

logic  w_ibuf_front_valid_next;
scariv_front_pkg::front_t w_ibuf_front_payload_next;
logic  w_inst_buffer_fire_next;

logic  w_inst_buffer_fire;

logic                                         r_pred_entry_kill_valid;
logic [$clog2(scariv_pkg::INST_BUF_SIZE)-1:0] r_pred_entry_kill_index;

scariv_pkg::grp_id_t w_inst_arith_pick_up;
scariv_pkg::grp_id_t w_inst_muldiv_pick_up;
scariv_pkg::grp_id_t w_inst_mem_pick_up;
scariv_pkg::grp_id_t w_inst_bru_pick_up;
scariv_pkg::grp_id_t w_inst_csu_pick_up;
scariv_pkg::grp_id_t w_inst_fpu_pick_up;
scariv_pkg::grp_id_t w_fetch_except_pick_up;
scariv_pkg::grp_id_t w_inst_illegal_pick_up;

scariv_pkg::grp_id_t w_inst_arith_disp;
scariv_pkg::grp_id_t w_inst_muldiv_disp;
scariv_pkg::grp_id_t w_inst_mem_disp;
scariv_pkg::grp_id_t w_inst_ld_disp;
scariv_pkg::grp_id_t w_inst_st_disp;
scariv_pkg::grp_id_t w_inst_bru_disp;
scariv_pkg::grp_id_t w_inst_csu_disp;
scariv_pkg::grp_id_t w_inst_fpu_disp;
scariv_pkg::grp_id_t w_inst_illegal_disp;
scariv_pkg::grp_id_t w_fetch_except_disp;

scariv_pkg::grp_id_t w_inst_disp_or;
scariv_pkg::grp_id_t w_inst_disp_mask;

localparam ic_word_num = scariv_lsu_pkg::ICACHE_DATA_B_W / 2;
decoder_inst_cat_pkg::inst_cat_t    w_inst_cat   [scariv_conf_pkg::DISP_SIZE];
decoder_inst_cat_pkg::inst_subcat_t w_inst_subcat[scariv_conf_pkg::DISP_SIZE];
scariv_pkg::grp_id_t w_fetch_except;
scariv_pkg::grp_id_t w_inst_is_arith;
scariv_pkg::grp_id_t w_inst_is_muldiv;
scariv_pkg::grp_id_t w_inst_is_ld;
scariv_pkg::grp_id_t w_inst_is_st;
scariv_pkg::grp_id_t w_inst_is_br;
scariv_pkg::grp_id_t w_inst_is_br_branch;
scariv_pkg::grp_id_t w_inst_is_csu;
scariv_pkg::grp_id_t w_inst_is_fpu;
scariv_pkg::grp_id_t w_inst_illegal;

scariv_pkg::grp_id_t w_inst_is_call;
scariv_pkg::grp_id_t w_inst_is_ret;
scariv_pkg::grp_id_t w_inst_is_cond;
scariv_pkg::grp_id_t w_inst_is_call_ret_lsb;

scariv_pkg::except_t [scariv_conf_pkg::DISP_SIZE-1: 0] w_fetch_except_cause;
riscv_pkg::xlen_t    [scariv_conf_pkg::DISP_SIZE-1: 0] w_fetch_except_tval;

rd_t rd_field_type [scariv_conf_pkg::DISP_SIZE];
r1_t rs1_field_type[scariv_conf_pkg::DISP_SIZE];
r2_t rf2_field_type[scariv_conf_pkg::DISP_SIZE];
r3_t rs3_field_type[scariv_conf_pkg::DISP_SIZE];

logic [$clog2(ic_word_num)-1:0] r_head_start_pos;
logic [$clog2(ic_word_num):0]   w_head_start_pos_next;
logic                           w_head_all_inst_issued;
logic                           w_head_predict_taken_issued;
logic                           w_predict_taken_valid;
scariv_pkg::grp_id_t w_predict_taken_valid_array;
scariv_pkg::grp_id_t                     w_predict_taken_valid_lsb;
logic [$clog2(scariv_pkg::INST_BUF_SIZE)-1: 0] w_pred_lsb_index;

scariv_pkg::grp_id_t w_inst_arith_disped;
scariv_pkg::grp_id_t w_inst_muldiv_disped;
scariv_pkg::grp_id_t w_inst_mem_disped;
scariv_pkg::grp_id_t w_inst_ld_disped;
scariv_pkg::grp_id_t w_inst_st_disped;
scariv_pkg::grp_id_t w_inst_bru_disped;
scariv_pkg::grp_id_t w_inst_csu_disped;
scariv_pkg::grp_id_t w_inst_fpu_disped;

logic w_inst_buf_empty;
logic w_inst_buf_full;

scariv_ibuf_pkg::pred_info_t w_expand_pred_info[scariv_conf_pkg::DISP_SIZE];
logic [$clog2(scariv_pkg::INST_BUF_SIZE)-1:0] w_expand_pred_index[scariv_conf_pkg::DISP_SIZE];

scariv_ibuf_pkg::ras_info_t w_expand_ras_info[scariv_conf_pkg::DISP_SIZE];

logic [$clog2(scariv_pkg::INST_BUF_SIZE)-1:0] r_inst_buffer_inptr;
logic [$clog2(scariv_pkg::INST_BUF_SIZE)-1:0] r_inst_buffer_outptr;
logic [$clog2(scariv_pkg::INST_BUF_SIZE)-1:0] w_inst_buffer_outptr_p1;
logic                                       w_ptr_in_fire;
logic                                       w_ptr_out_fire;

logic [ 1: 0]                               w_inst_buf_valid;
scariv_ibuf_pkg::inst_buf_t                 w_inst_buf_data[2];

logic [$clog2(ic_word_num)+1-1:1]           w_out_inst_q_pc;
logic                                       w_inst_queue_pop;

logic                                       w_br_flush;
logic                                       w_flush_pipeline;
assign w_br_flush = br_upd_if.update & ~br_upd_if.dead & br_upd_if.mispredict;

// ----------------------------
// Decode Unit Flush Interface
// ----------------------------
grp_id_t iq_is_call_valid_oh;
grp_id_t iq_is_ret_valid_oh;
vaddr_t  iq_call_next_vaddr_array[scariv_conf_pkg::DISP_SIZE];
vaddr_t  iq_call_stash_vaddr_array[scariv_conf_pkg::DISP_SIZE];
vaddr_t  iq_call_next_vaddr_oh;
vaddr_t  iq_call_stash_vaddr_oh;
vaddr_t  w_iq_ras_ret_vaddr;

scariv_predict_pkg::ras_idx_t r_ras_index;
scariv_predict_pkg::ras_idx_t w_ras_index_next;

`ifdef SIMULATION
`endif // SIMULATION

// =================================
// RVC Expand from 16-bit to 32-bit
// =================================
/* verilator lint_off UNOPTFLAT */
logic [$clog2(ic_word_num): 0]       w_rvc_buf_idx[scariv_conf_pkg::DISP_SIZE + 1];
logic [$clog2(ic_word_num): 0]       w_rvc_buf_idx_with_offset[scariv_conf_pkg::DISP_SIZE + 1];
logic [31: 0]                        w_expand_inst[scariv_conf_pkg::DISP_SIZE];
scariv_pkg::grp_id_t w_expanded_valid;
logic [15: 0]                        w_rvc_inst[scariv_conf_pkg::DISP_SIZE];
scariv_pkg::grp_id_t w_rvc_valid;

/* verilator lint_off WIDTH */
assign w_head_all_inst_issued      = w_inst_buffer_fire_next & ((w_head_start_pos_next + w_out_inst_q_pc) >= ic_word_num);
assign w_head_predict_taken_issued = w_inst_buffer_fire_next & w_predict_taken_valid & w_ibuf_front_payload_next.is_br_included;
assign w_ptr_in_fire  = i_f2_inst.valid & o_inst_ready;
assign w_ptr_out_fire = w_head_all_inst_issued | w_head_predict_taken_issued |
                        w_inst_buf_valid[0] & r_pred_entry_kill_valid ;
assign w_flush_pipeline = i_flush_valid | w_br_flush;

assign w_inst_queue_pop = w_ptr_out_fire;

// Queue Control Pointer
inoutptr
  #(
    .SIZE(scariv_pkg::INST_BUF_SIZE)
    )
inst_buf_ptr
  (
   .i_clk     (i_clk),
   .i_reset_n (i_reset_n),

   .i_clear   (w_flush_pipeline),

   .i_in_valid  (w_ptr_in_fire),
   .o_in_ptr    (r_inst_buffer_inptr),
   .i_out_valid (w_ptr_out_fire),
   .o_out_ptr   (r_inst_buffer_outptr)
   );

assign w_inst_buffer_outptr_p1 = r_inst_buffer_outptr == scariv_pkg::INST_BUF_SIZE-1 ? 'h0 :
                                 r_inst_buffer_outptr + 'h1;

assign w_inst_buffer_fire = ibuf_front_if.valid & ibuf_front_if.ready;

scariv_ibuf_pkg::inst_buf_t w_inst_buf_load;

ring_fifo_2ptr
  #(.T(scariv_ibuf_pkg::inst_buf_t),
    .DEPTH (scariv_pkg::INST_BUF_SIZE)
    )
u_inst_queue
(
 .i_clk (i_clk),
 .i_reset_n (i_reset_n),

 .i_clear (w_flush_pipeline),

 .i_push (w_ptr_in_fire),
 .i_data (w_inst_buf_load),

 .o_empty (w_inst_buf_empty),
 .o_full  (w_inst_buf_full),

 .i_pop  (w_inst_queue_pop),

 .o_valid0 (w_inst_buf_valid[0]),
 .o_data0  (w_inst_buf_data [0]),
 .o_valid1 (w_inst_buf_valid[1]),
 .o_data1  (w_inst_buf_data [1])
 );


always_comb begin
  w_inst_buf_load.data    = i_f2_inst.inst;
  w_inst_buf_load.pc      = i_f2_inst.pc;
  w_inst_buf_load.byte_en = i_f2_inst.byte_en;
  w_inst_buf_load.tlb_except_valid = i_f2_inst.tlb_except_valid;
  w_inst_buf_load.tlb_except_cause = i_f2_inst.tlb_except_cause;

  for (int b_idx = 0; b_idx < scariv_lsu_pkg::ICACHE_DATA_B_W/2; b_idx++) begin : pred_loop
    logic w_f2_ubtb_predict_hit;
    w_f2_ubtb_predict_hit = i_f2_ubtb_predict_valid & i_f2_ubtb_info.taken & ((i_f2_ubtb_info.pc_offset >> 1) == b_idx);
    w_inst_buf_load.pred_info[b_idx].pred_taken        = w_f2_ubtb_predict_hit ? i_f2_ubtb_info.taken : gshare_search_if.f2_pred_taken[b_idx];
    w_inst_buf_load.pred_info[b_idx].is_cond           = btb_search_if.f2_is_cond      [b_idx];
    w_inst_buf_load.pred_info[b_idx].bim_value         = gshare_search_if.f2_bim_value [b_idx];
    w_inst_buf_load.pred_info[b_idx].btb_valid         = w_f2_ubtb_predict_hit ? i_f2_ubtb_info.taken        : btb_search_if.f2_hit          [b_idx];
    w_inst_buf_load.pred_info[b_idx].pred_target_vaddr = w_f2_ubtb_predict_hit ? i_f2_ubtb_info.target_vaddr : btb_search_if.f2_target_vaddr [b_idx];
    w_inst_buf_load.pred_info[b_idx].gshare_index      = gshare_search_if.f2_index     [b_idx];
    w_inst_buf_load.pred_info[b_idx].gshare_bhr        = gshare_search_if.f2_bhr       [b_idx];

    w_inst_buf_load.ras_info[b_idx].is_call           = ras_search_if.f2_is_call[b_idx];
    w_inst_buf_load.ras_info[b_idx].is_ret            = ras_search_if.f2_is_ret [b_idx];
    // w_inst_buf_load.ras_info[b_idx].ras_index         = ras_search_if.f2_ras_be [b_idx/2] & ras_search_if.f2_is_ret [b_idx] ? ras_search_if.f2_ras_index - 1 :
    // ras_search_if.f2_ras_index;
    w_inst_buf_load.ras_info[b_idx].pred_target_vaddr = ras_search_if.f2_is_call[b_idx] ? {ras_search_if.f2_call_target_vaddr, 1'b0} : {ras_search_if.f2_ras_vaddr, 1'b0};
  end // block: pred_loop

`ifdef SIMULATION
  w_inst_buf_load.pc_dbg           = {i_f2_inst.pc, 1'b0};
`endif // SIMULATION
  w_inst_buf_load.int_inserted = i_f2_inst.int_inserted;
// end else if ((w_head_all_inst_issued |
//               w_head_predict_taken_issued |
//               w_inst_buf_load.valid & w_inst_buf_load.dead) & (r_inst_buffer_outptr == idx)) begin
//   w_inst_buf_load.valid  = 1'b0;
//   w_inst_buf_load.dead   = 1'b0;
// end else if (w_head_predict_taken_issued & (w_pred_lsb_index == idx)) begin
//   w_inst_buf_load.dead = 1'b1;
//       end // if (i_f2_inst.valid & o_inst_ready)
//     end // else: !if(!i_reset_n)
//   end // always_ff @ (posedge i_clk, negedge i_reset_n)
//
// end // block: inst_buf_loop
// endgenerate
end // always_comb


assign o_inst_ready = !w_inst_buf_full;

// Extract next start position of decoding
logic [ic_word_num-1: 0] w_bit_next_start_pos_oh;
bit_extract_lsb
  #(.WIDTH(ic_word_num))
u_start_pos_bit
  (
   .in({{(ic_word_num - scariv_conf_pkg::DISP_SIZE){1'b1}}, ~w_inst_disp_mask}),
   .out(w_bit_next_start_pos_oh)
   );
// Note: MSB (DISP_SIZE) bit is dummy.
bit_oh_or #(.T(logic[$clog2(ic_word_num): 0]), .WORDS(scariv_conf_pkg::DISP_SIZE+1))
u_select_next_pos (
 .i_oh       (w_bit_next_start_pos_oh[scariv_conf_pkg::DISP_SIZE:0]),
 .i_data     (w_rvc_buf_idx),
 .o_selected (w_head_start_pos_next)
);


assign w_out_inst_q_pc = w_inst_buf_data[0].pc[1+:$clog2(ic_word_num)];

always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_head_start_pos   <= 'h0;
  end else begin
    if (w_flush_pipeline | w_head_predict_taken_issued) begin
      r_head_start_pos <= 'h0;
    end else if (w_head_all_inst_issued) begin
      // Move to next Line, carring lower bits for next
      r_head_start_pos <= w_head_start_pos_next + w_out_inst_q_pc;
    end else if (w_inst_buffer_fire_next) begin
      r_head_start_pos <= w_head_start_pos_next[$clog2(ic_word_num)-1:0];
    end
  end
end

// =================================
// RVC Expand from 16-bit to 32-bit
// =================================
assign w_rvc_buf_idx[0] = {1'b0, r_head_start_pos};
generate for (genvar w_idx = 0; w_idx < scariv_conf_pkg::DISP_SIZE; w_idx++) begin : rvc_expand_loop
  logic [15: 0]                    w_local_rvc_inst;
  logic [15: 0]                    w_rvc_next_inst;
  logic [ 1: 0]                    w_rvc_byte_en;
  logic [ 1: 0]                    w_rvc_next_byte_en;
  logic                            w_inst_buf_valid_b0;
  logic                            w_inst_buf_valid_b2;
  scariv_ibuf_pkg::inst_buf_t      w_inst_buf_entry_b0;
  scariv_ibuf_pkg::inst_buf_t      w_inst_buf_entry_b2;

  logic [$clog2(scariv_pkg::INST_BUF_SIZE)-1: 0] w_inst_buf_ptr_b0;
  logic [$clog2(scariv_pkg::INST_BUF_SIZE)-1: 0] w_inst_buf_ptr_b2;

  logic [31: 0]                                w_local_expand_inst;
  logic [$clog2(ic_word_num): 0]               w_rvc_buf_idx_with_offset_b2;

  /* verilator lint_off WIDTH */
  assign w_inst_buf_ptr_b0 = (w_rvc_buf_idx_with_offset[w_idx] < ic_word_num) ? r_inst_buffer_outptr :
                             w_inst_buffer_outptr_p1;
  assign w_inst_buf_ptr_b2 = (w_rvc_buf_idx_with_offset_b2 < ic_word_num) ? r_inst_buffer_outptr :
                             w_inst_buffer_outptr_p1;

  assign w_rvc_buf_idx_with_offset[w_idx] = w_rvc_buf_idx[w_idx] + w_out_inst_q_pc;
  assign w_rvc_buf_idx_with_offset_b2     = w_rvc_buf_idx_with_offset[w_idx] + 1;

  /* verilator lint_off WIDTH */
  assign w_inst_buf_valid_b0 = (w_rvc_buf_idx_with_offset[w_idx] < ic_word_num) ? w_inst_buf_valid[0] : w_inst_buf_valid[1];
  assign w_inst_buf_entry_b0 = (w_rvc_buf_idx_with_offset[w_idx] < ic_word_num) ? w_inst_buf_data [0] : w_inst_buf_data [1];
  assign w_inst_buf_valid_b2 = (w_rvc_buf_idx_with_offset_b2     < ic_word_num) ? w_inst_buf_valid[0] : w_inst_buf_valid[1];
  assign w_inst_buf_entry_b2 = (w_rvc_buf_idx_with_offset_b2     < ic_word_num) ? w_inst_buf_data [0] : w_inst_buf_data [1];

  assign w_local_rvc_inst   = w_inst_buf_entry_b0.data   [ w_rvc_buf_idx_with_offset[w_idx][$clog2(ic_word_num)-1:0]*16 +:16];
  assign w_rvc_next_inst    = w_inst_buf_entry_b2.data   [ w_rvc_buf_idx_with_offset_b2    [$clog2(ic_word_num)-1:0]*16 +:16];
  assign w_rvc_byte_en      = w_inst_buf_entry_b0.byte_en[ w_rvc_buf_idx_with_offset[w_idx][$clog2(ic_word_num)-1:0] *2 +: 2];
  assign w_rvc_next_byte_en = w_inst_buf_entry_b2.byte_en[ w_rvc_buf_idx_with_offset_b2    [$clog2(ic_word_num)-1:0] *2 +: 2];
  scariv_rvc_expander u_scariv_rvc_expander (.i_rvc_inst(w_local_rvc_inst), .out_32bit(w_local_expand_inst));

  always_comb begin
    if (w_local_rvc_inst[1:0] != 2'b11) begin
      // RVC instruction
      /* verilator lint_off ALWCOMBORDER */
      w_rvc_buf_idx[w_idx + 1] = w_rvc_buf_idx[w_idx] + 1;
      w_expand_inst[w_idx]     = w_local_expand_inst;
      w_rvc_inst[w_idx]    = w_local_rvc_inst;
      w_rvc_valid[w_idx]   = 1'b1;
      w_expanded_valid[w_idx]  = w_inst_buf_valid_b0 &
                                 !w_inst_buf_entry_b0.dead &
                                 & (&w_rvc_byte_en);

      w_fetch_except[w_idx]       = w_inst_buf_valid_b0 &
                                    !w_inst_buf_entry_b0.dead &
                                    w_inst_buf_entry_b0.tlb_except_valid;
      w_fetch_except_cause[w_idx] = w_inst_buf_entry_b0.tlb_except_cause;
      w_fetch_except_tval [w_idx] = {w_inst_buf_entry_b0.pc[riscv_pkg::VADDR_W-1:$clog2(scariv_lsu_pkg::DCACHE_DATA_B_W)],
                                     w_rvc_buf_idx_with_offset[w_idx][$clog2(ic_word_num)-1:0], 1'b0};

      w_expand_pred_info[w_idx] = w_inst_buf_entry_b0.pred_info[w_rvc_buf_idx_with_offset[w_idx][$clog2(ic_word_num)-1:0]];
      w_expand_pred_index[w_idx] = w_inst_buf_ptr_b0;

      w_expand_ras_info[w_idx] = w_inst_buf_entry_b0.ras_info[w_rvc_buf_idx_with_offset[w_idx][$clog2(ic_word_num)-1:0]];
    end else begin
      // Normal instruction
      /* verilator lint_off ALWCOMBORDER */
      w_rvc_buf_idx[w_idx + 1] = w_rvc_buf_idx[w_idx] + 2;
      w_expand_inst[w_idx]     = {w_rvc_next_inst, w_local_rvc_inst};
      w_expanded_valid[w_idx]  = w_inst_buf_valid_b0 & !w_inst_buf_entry_b0.dead &
                                 w_inst_buf_valid_b2 & !w_inst_buf_entry_b2.dead &
                                 &{w_rvc_next_byte_en, w_rvc_byte_en};
      w_rvc_inst[w_idx]    = 'h0;
      w_rvc_valid[w_idx]   = 1'b0;

      w_fetch_except[w_idx]       = w_inst_buf_valid_b0 & !w_inst_buf_entry_b0.dead & w_inst_buf_entry_b0.tlb_except_valid |
                                    w_inst_buf_valid_b2 & !w_inst_buf_entry_b2.dead & w_inst_buf_entry_b2.tlb_except_valid;
      w_fetch_except_cause[w_idx] = w_inst_buf_entry_b0.tlb_except_valid ? w_inst_buf_entry_b0.tlb_except_cause :
                                    w_inst_buf_entry_b2.tlb_except_cause;
      w_fetch_except_tval [w_idx] = w_inst_buf_entry_b0.tlb_except_valid ?
                                    {w_inst_buf_entry_b0.pc[riscv_pkg::VADDR_W-1:$clog2(scariv_lsu_pkg::DCACHE_DATA_B_W)], w_rvc_buf_idx_with_offset[w_idx][$clog2(ic_word_num)-1:0], 1'b0} :
                                    {w_inst_buf_entry_b2.pc[riscv_pkg::VADDR_W-1:$clog2(scariv_lsu_pkg::DCACHE_DATA_B_W)], w_rvc_buf_idx_with_offset_b2[$clog2(ic_word_num)-1:0], 1'b0};

      w_expand_pred_info [w_idx] = w_inst_buf_entry_b2.pred_info[w_rvc_buf_idx_with_offset_b2[$clog2(ic_word_num)-1:0]];
      w_expand_pred_index[w_idx] = w_inst_buf_ptr_b2;

      w_expand_ras_info  [w_idx] = w_inst_buf_entry_b2.ras_info [w_rvc_buf_idx_with_offset_b2[$clog2(ic_word_num)-1:0]];
    end // else: !if(w_rvc_inst[1:0] != 2'b11)
  end // always_comb

  assign w_predict_taken_valid_array[w_idx] = w_expanded_valid[w_idx] &
                                              (w_expand_pred_info[w_idx].btb_valid & w_expand_pred_info[w_idx].pred_taken); // | // BIM
                                               /* w_expand_ras_info[w_idx].is_call |  // RAS
                                                w_expand_ras_info[w_idx].is_ret);  // RAS */

end
endgenerate



generate for (genvar w_idx = 0; w_idx < scariv_conf_pkg::DISP_SIZE; w_idx++) begin : word_loop
  decoder_inst_cat
  u_decoder_inst_cat
    (
     .inst(w_expand_inst[w_idx]),
     .inst_cat   (w_inst_cat   [w_idx]),
     .inst_subcat(w_inst_subcat[w_idx])
     );

  decoder_reg
  u_decoder_reg
    (
     .inst(w_expand_inst[w_idx]),
     .rd(rd_field_type [w_idx]),
     .r1(rs1_field_type[w_idx]),
     .r2(rf2_field_type[w_idx]),
     .r3(rs3_field_type[w_idx])
     );

logic          w_inst_ld_fpu_illegal;
logic          w_inst_st_fpu_illegal;
logic          w_inst_arith_fpu_illegal;
logic          w_inst_fpu_illegal;

  assign w_inst_ld_fpu_illegal = (w_inst_cat[w_idx] == decoder_inst_cat_pkg::INST_CAT_LD) &
                                 (w_inst_subcat[w_idx] == decoder_inst_cat_pkg::INST_SUBCAT_FPU) &
                                 (csr_info.mstatus[`MSTATUS_FS] == 2'b00);
  assign w_inst_st_fpu_illegal = (w_inst_cat[w_idx] == decoder_inst_cat_pkg::INST_CAT_ST) &
                                 (w_inst_subcat[w_idx] == decoder_inst_cat_pkg::INST_SUBCAT_FPU) &
                                 (csr_info.mstatus[`MSTATUS_FS] == 2'b00);
  assign w_inst_arith_fpu_illegal = (w_inst_cat[w_idx] == decoder_inst_cat_pkg::INST_CAT_FPU) &
                                    (csr_info.mstatus[`MSTATUS_FS] == 2'b00);
  assign w_inst_fpu_illegal = w_inst_ld_fpu_illegal |
                              w_inst_st_fpu_illegal |
                              w_inst_arith_fpu_illegal;

  assign w_inst_is_arith     [w_idx] = w_expanded_valid[w_idx] & (w_inst_cat[w_idx] == decoder_inst_cat_pkg::INST_CAT_ARITH );
  assign w_inst_is_muldiv    [w_idx] = w_expanded_valid[w_idx] & (w_inst_cat[w_idx] == decoder_inst_cat_pkg::INST_CAT_MULDIV);
  assign w_inst_is_ld        [w_idx] = w_expanded_valid[w_idx] & !w_inst_ld_fpu_illegal & (w_inst_cat[w_idx] == decoder_inst_cat_pkg::INST_CAT_LD    );
  assign w_inst_is_st        [w_idx] = w_expanded_valid[w_idx] & !w_inst_st_fpu_illegal & (w_inst_cat[w_idx] == decoder_inst_cat_pkg::INST_CAT_ST    );
  assign w_inst_is_br        [w_idx] = w_expanded_valid[w_idx] & (w_inst_cat[w_idx] == decoder_inst_cat_pkg::INST_CAT_BR    );
  assign w_inst_is_br_branch [w_idx] = w_expanded_valid[w_idx] & !w_inst_ld_fpu_illegal & (w_inst_subcat[w_idx] == decoder_inst_cat_pkg::INST_SUBCAT_BRANCH);
  assign w_inst_is_csu       [w_idx] = w_expanded_valid[w_idx] & (w_inst_cat[w_idx] == decoder_inst_cat_pkg::INST_CAT_CSU   );
  assign w_inst_is_fpu       [w_idx] = w_expanded_valid[w_idx] & !w_inst_arith_fpu_illegal & (w_inst_cat[w_idx] == decoder_inst_cat_pkg::INST_CAT_FPU   );

  logic          w_is_std_call;
  logic          w_is_std_ret;
  assign w_is_std_call = (w_expand_inst[w_idx][ 6:0] == 7'b1101111) &
                         (w_expand_inst[w_idx][11:7] == 5'h1);
  assign w_is_std_ret = w_expand_inst[w_idx] == 32'h00008067;

  assign w_inst_is_call  [w_idx] = w_expanded_valid[w_idx] & w_is_std_call;
  assign w_inst_is_ret   [w_idx] = w_expanded_valid[w_idx] & w_is_std_ret;

  assign w_inst_illegal  [w_idx] = w_expanded_valid[w_idx] &
                                   ((w_inst_cat[w_idx] == decoder_inst_cat_pkg::INST_CAT__ ) | w_inst_fpu_illegal);
end // block: word_loop
endgenerate

assign w_inst_arith_pick_up  = w_inst_is_arith | w_inst_is_muldiv;
assign w_inst_muldiv_pick_up = w_inst_is_muldiv;
assign w_inst_mem_pick_up    = w_inst_is_ld | w_inst_is_st;
assign w_inst_bru_pick_up    = w_inst_is_br;
assign w_inst_csu_pick_up    = w_inst_is_csu;
assign w_inst_fpu_pick_up    = w_inst_is_fpu;
assign w_fetch_except_pick_up = w_fetch_except;
assign w_inst_illegal_pick_up = w_inst_illegal;

bit_pick_up #(.WIDTH(scariv_conf_pkg::DISP_SIZE), .NUM(scariv_conf_pkg::ARITH_DISP_SIZE))  u_arith_disp_pick_up  (.in(w_inst_arith_pick_up ),  .out(w_inst_arith_disp  ));
bit_pick_up #(.WIDTH(scariv_conf_pkg::DISP_SIZE), .NUM(scariv_conf_pkg::MULDIV_DISP_SIZE)) u_muldiv_disp_pick_up (.in(w_inst_muldiv_pick_up),  .out(w_inst_muldiv_disp ));
bit_pick_up #(.WIDTH(scariv_conf_pkg::DISP_SIZE), .NUM(scariv_conf_pkg::MEM_DISP_SIZE  ))  u_mem_disp_pick_up    (.in(w_inst_mem_pick_up   ),  .out(w_inst_mem_disp    ));
bit_pick_up #(.WIDTH(scariv_conf_pkg::DISP_SIZE), .NUM(scariv_conf_pkg::MEM_DISP_SIZE  ))  u_ld_disp_pick_up     (.in(w_inst_is_ld         ),  .out(w_inst_ld_disp     ));
bit_pick_up #(.WIDTH(scariv_conf_pkg::DISP_SIZE), .NUM(scariv_conf_pkg::MEM_DISP_SIZE  ))  u_st_disp_pick_up     (.in(w_inst_is_st         ),  .out(w_inst_st_disp     ));
bit_pick_up #(.WIDTH(scariv_conf_pkg::DISP_SIZE), .NUM(scariv_conf_pkg::BRU_DISP_SIZE  ))  u_bru_disp_pick_up    (.in(w_inst_bru_pick_up   ),  .out(w_inst_bru_disp    ));
bit_pick_up #(.WIDTH(scariv_conf_pkg::DISP_SIZE), .NUM(scariv_conf_pkg::CSU_DISP_SIZE  ))  u_csu_disp_pick_up    (.in(w_inst_csu_pick_up   ),  .out(w_inst_csu_disp    ));
bit_pick_up #(.WIDTH(scariv_conf_pkg::DISP_SIZE), .NUM(scariv_conf_pkg::FPU_DISP_SIZE  ))  u_fpu_disp_pick_up    (.in(w_inst_fpu_pick_up   ),  .out(w_inst_fpu_disp    ));
bit_pick_up #(.WIDTH(scariv_conf_pkg::DISP_SIZE), .NUM(1                             ))  u_illegal_disp_pick_up(.in(w_inst_illegal_pick_up), .out(w_inst_illegal_disp));
bit_pick_up #(.WIDTH(scariv_conf_pkg::DISP_SIZE), .NUM(1                             ))  u_except_disp_pick_up (.in(w_fetch_except_pick_up), .out(w_fetch_except_disp));

assign w_inst_disp_or = w_inst_arith_disp | w_inst_mem_disp | w_inst_bru_disp | w_inst_csu_disp | w_inst_fpu_disp | w_inst_illegal_disp | w_fetch_except_disp;

logic [scariv_conf_pkg::DISP_SIZE: 0] w_inst_disp_mask_tmp;
bit_extract_lsb #(.WIDTH(scariv_conf_pkg::DISP_SIZE + 1)) u_inst_msb (.in({1'b1, ~w_inst_disp_or}), .out(w_inst_disp_mask_tmp));
assign w_predict_taken_valid = |(w_inst_disp_mask & w_predict_taken_valid_array);

bit_extract_lsb #(.WIDTH(scariv_conf_pkg::DISP_SIZE)) u_predict_valid_lsb (.in(w_inst_disp_mask & w_predict_taken_valid_array), .out(w_predict_taken_valid_lsb));
bit_oh_or #(.T(logic[$clog2(scariv_pkg::INST_BUF_SIZE)-1:0]), .WORDS(scariv_conf_pkg::DISP_SIZE)) u_inst_buf_pred_index (.i_oh(w_predict_taken_valid_lsb), .i_data(w_expand_pred_index), .o_selected(w_pred_lsb_index));

always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_pred_entry_kill_valid <= 1'b0;
    r_pred_entry_kill_index <= 'h0;
  end else begin
    if (w_flush_pipeline) begin
      r_pred_entry_kill_valid <= 1'b0;
    end else begin
      if (~r_pred_entry_kill_valid &
          w_head_predict_taken_issued &
          (w_pred_lsb_index != r_inst_buffer_outptr)) begin
        r_pred_entry_kill_valid <= 1'b1;
        r_pred_entry_kill_index <= w_pred_lsb_index;
      end else if (r_pred_entry_kill_valid &
                   w_inst_buf_valid[0] &
                   (r_pred_entry_kill_index == r_inst_buffer_outptr)) begin
        r_pred_entry_kill_valid <= 1'b0;
      end
    end // else: !if(w_flush_pipeline)
  end // else: !if(!i_reset_n)
end // always_ff @ (posedge i_clk, negedge i_reset_n)


scariv_pkg::grp_id_t w_bru_predict_disp_valid;
scariv_pkg::grp_id_t w_disp_special_limit_valid;
scariv_pkg::grp_id_t w_disp_special_limit_valid_oh;

assign w_bru_predict_disp_valid = (w_inst_disp_mask_tmp - 1) & (w_inst_bru_disp & (w_predict_taken_valid_array | w_inst_is_call | w_inst_is_ret));

assign w_disp_special_limit_valid = w_bru_predict_disp_valid | (w_inst_csu_disp & (w_inst_disp_mask_tmp - 1));

bit_extract_lsb #(.WIDTH(scariv_conf_pkg::DISP_SIZE)) u_special_valid_lsb (.in(w_disp_special_limit_valid), .out(w_disp_special_limit_valid_oh));

scariv_pkg::grp_id_t w_disp_special_bru_valid;
scariv_pkg::grp_id_t w_disp_special_csu_valid;

assign w_disp_special_bru_valid = w_disp_special_limit_valid_oh & w_bru_predict_disp_valid;
assign w_disp_special_csu_valid = w_disp_special_limit_valid_oh & w_inst_csu_disp;

assign w_inst_disp_mask = |w_disp_special_bru_valid ? {w_disp_special_bru_valid, 1'b0} - 1 :
                          (w_disp_special_csu_valid == 'h1) ? 'h1 :
                          |w_disp_special_csu_valid ? w_inst_csu_disp - 1 :
                          w_inst_disp_mask_tmp - 1;


assign w_ibuf_front_valid_next = |w_inst_disp_mask & !r_pred_entry_kill_valid &
                                 !w_flush_pipeline &
                                 !o_decode_flush.valid;
assign w_inst_buffer_fire_next  = w_ibuf_front_valid_next & ibuf_front_if.ready;

logic ibuf_front_if_valid_raw;
assign ibuf_front_if.valid = ibuf_front_if_valid_raw & ~w_flush_pipeline;
always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    ibuf_front_if_valid_raw <= 1'b0;
  end else begin
    if (w_flush_pipeline) begin
      ibuf_front_if_valid_raw <= 1'b0;
    end else if (ibuf_front_if.ready) begin
      ibuf_front_if_valid_raw   <= w_ibuf_front_valid_next;
      ibuf_front_if.payload <= w_ibuf_front_payload_next;
    end
  end
end

assign w_ibuf_front_payload_next.pc_addr        = w_inst_buf_data[0].pc + r_head_start_pos;
assign w_ibuf_front_payload_next.basicblk_pc_vaddr = w_inst_buf_data[0].pc;
`ifdef SIMULATION
assign w_ibuf_front_payload_next.pc_addr_debug  = (w_inst_buf_data[0].pc + r_head_start_pos) << 1;
assign w_ibuf_front_payload_next.basicblk_pc_vaddr_debug = w_inst_buf_data[0].pc << 1;
`endif // SIMULATION
assign w_ibuf_front_payload_next.is_br_included = |w_inst_bru_disped;
assign w_ibuf_front_payload_next.tlb_except_valid = w_fetch_except;
assign w_ibuf_front_payload_next.tlb_except_cause = w_fetch_except_cause;
assign w_ibuf_front_payload_next.tlb_except_tval  = w_fetch_except_tval;
assign w_ibuf_front_payload_next.int_inserted  = w_inst_buf_data[0].int_inserted;

// -------------------------------
// Dispatch Inst, Resource Count
// -------------------------------

bit_pick_up #(.WIDTH(scariv_conf_pkg::DISP_SIZE), .NUM(scariv_conf_pkg::ARITH_DISP_SIZE )) u_arith_disped_pick_up   (.in(w_inst_arith_disp   & w_inst_disp_mask), .out(w_inst_arith_disped  ));
bit_pick_up #(.WIDTH(scariv_conf_pkg::DISP_SIZE), .NUM(scariv_conf_pkg::MULDIV_DISP_SIZE)) u_muldiv_disped_pick_up  (.in(w_inst_muldiv_disp  & w_inst_disp_mask), .out(w_inst_muldiv_disped ));
bit_pick_up #(.WIDTH(scariv_conf_pkg::DISP_SIZE), .NUM(scariv_conf_pkg::MEM_DISP_SIZE   )) u_mem_disped_pick_up     (.in(w_inst_mem_disp     & w_inst_disp_mask), .out(w_inst_mem_disped    ));
bit_pick_up #(.WIDTH(scariv_conf_pkg::DISP_SIZE), .NUM(scariv_conf_pkg::MEM_DISP_SIZE   )) u_ld_disped_pick_up      (.in(w_inst_ld_disp      & w_inst_disp_mask), .out(w_inst_ld_disped     ));
bit_pick_up #(.WIDTH(scariv_conf_pkg::DISP_SIZE), .NUM(scariv_conf_pkg::MEM_DISP_SIZE   )) u_st_disped_pick_up      (.in(w_inst_st_disp      & w_inst_disp_mask), .out(w_inst_st_disped     ));
bit_pick_up #(.WIDTH(scariv_conf_pkg::DISP_SIZE), .NUM(scariv_conf_pkg::BRU_DISP_SIZE   )) u_bru_disped_pick_up     (.in(w_inst_bru_disp     & w_inst_disp_mask), .out(w_inst_bru_disped    ));
bit_pick_up #(.WIDTH(scariv_conf_pkg::DISP_SIZE), .NUM(scariv_conf_pkg::CSU_DISP_SIZE   )) u_csu_disped_pick_up     (.in(w_inst_csu_disp     & w_inst_disp_mask), .out(w_inst_csu_disped    ));
bit_pick_up #(.WIDTH(scariv_conf_pkg::DISP_SIZE), .NUM(scariv_conf_pkg::FPU_DISP_SIZE   )) u_fpu_disped_pick_up     (.in(w_inst_fpu_disp     & w_inst_disp_mask), .out(w_inst_fpu_disped    ));

logic [$clog2(scariv_conf_pkg::DISP_SIZE): 0] w_inst_muldiv_cnt;
logic [$clog2(scariv_conf_pkg::DISP_SIZE): 0] w_inst_mem_cnt;
logic [$clog2(scariv_conf_pkg::DISP_SIZE): 0] w_inst_ld_cnt;
logic [$clog2(scariv_conf_pkg::DISP_SIZE): 0] w_inst_st_cnt;
logic [$clog2(scariv_conf_pkg::DISP_SIZE): 0] w_inst_bru_cnt;
logic [$clog2(scariv_conf_pkg::DISP_SIZE): 0] w_inst_csu_cnt;
logic [$clog2(scariv_conf_pkg::DISP_SIZE): 0] w_inst_fpu_cnt;

generate for (genvar a_idx = 0; a_idx < scariv_conf_pkg::ALU_INST_NUM; a_idx++) begin : alu_rsrc_loop
  localparam alu_lane_width = scariv_conf_pkg::ARITH_DISP_SIZE / scariv_conf_pkg::ALU_INST_NUM;
  logic [scariv_conf_pkg::DISP_SIZE-1: 0] w_lane_disped_valid[alu_lane_width];
  logic [scariv_conf_pkg::DISP_SIZE-1: 0] w_lane_disped_valid_or;
  logic [$clog2(alu_lane_width+1): 0] w_lane_disp_cnt;
  for (genvar i = 0; i < alu_lane_width; i++) begin: cnt_loop
    bit_pick_1_pos #(.NUM(i * scariv_conf_pkg::ALU_INST_NUM + a_idx), .SEL_WIDTH(scariv_conf_pkg::DISP_SIZE)) bit_pos (.i_valids(w_inst_arith_disped), .o_picked_pos(w_lane_disped_valid[i]));
  end
  bit_or #(.WIDTH(scariv_conf_pkg::DISP_SIZE), .WORDS(alu_lane_width)) alu_disped_or (.i_data(w_lane_disped_valid), .o_selected(w_lane_disped_valid_or));
  bit_cnt #(.WIDTH(scariv_conf_pkg::DISP_SIZE)) u_alu_inst_cnt (.in(w_lane_disped_valid_or), .out(w_lane_disp_cnt));
  assign w_ibuf_front_payload_next.resource_cnt.alu_inst_cnt  [a_idx] = w_lane_disp_cnt;
  assign w_ibuf_front_payload_next.resource_cnt.alu_inst_valid[a_idx] = w_lane_disped_valid_or;
end
endgenerate

bit_cnt #(.WIDTH(scariv_conf_pkg::DISP_SIZE)) u_muldiv_inst_cnt (.in(w_inst_muldiv_disped), .out(w_inst_muldiv_cnt));
assign w_ibuf_front_payload_next.resource_cnt.muldiv_inst_cnt = w_inst_muldiv_cnt;

bit_cnt #(.WIDTH(scariv_conf_pkg::DISP_SIZE)) u_mem_inst_cnt (.in(w_inst_mem_disped), .out(w_inst_mem_cnt));
bit_cnt #(.WIDTH(scariv_conf_pkg::DISP_SIZE)) u_ld_inst_cnt  (.in(w_inst_ld_disped), .out(w_inst_ld_cnt));
bit_cnt #(.WIDTH(scariv_conf_pkg::DISP_SIZE)) u_st_inst_cnt  (.in(w_inst_st_disped), .out(w_inst_st_cnt));
// assign w_ibuf_front_payload_next.resource_cnt.lsu_inst_valid = w_inst_mem_disped;

generate for (genvar l_idx = 0; l_idx < scariv_conf_pkg::LSU_INST_NUM; l_idx++) begin : lsu_rsrc_loop
  localparam lsu_lane_width = scariv_conf_pkg::MEM_DISP_SIZE / scariv_conf_pkg::LSU_INST_NUM;
  logic [scariv_conf_pkg::DISP_SIZE-1: 0] w_lane_disped_valid[lsu_lane_width];
  logic [scariv_conf_pkg::DISP_SIZE-1: 0] w_lane_disped_valid_or;
  logic [$clog2(lsu_lane_width+1): 0] w_lane_disp_cnt;
  for (genvar i = 0; i < lsu_lane_width; i++) begin: cnt_loop
    bit_pick_1_pos #(.NUM(i * scariv_conf_pkg::LSU_INST_NUM + l_idx), .SEL_WIDTH(scariv_conf_pkg::DISP_SIZE)) bit_pos (.i_valids(w_inst_mem_disped), .o_picked_pos(w_lane_disped_valid[i]));
  end
  bit_or #(.WIDTH(scariv_conf_pkg::DISP_SIZE), .WORDS(lsu_lane_width)) lsu_disped_or (.i_data(w_lane_disped_valid), .o_selected(w_lane_disped_valid_or));
  bit_cnt #(.WIDTH(scariv_conf_pkg::DISP_SIZE)) u_lsu_inst_cnt (.in(w_lane_disped_valid_or), .out(w_lane_disp_cnt));
  assign w_ibuf_front_payload_next.resource_cnt.lsu_inst_cnt  [l_idx] = w_lane_disp_cnt;
  assign w_ibuf_front_payload_next.resource_cnt.lsu_inst_valid[l_idx] = w_lane_disped_valid_or;
end endgenerate

assign w_ibuf_front_payload_next.resource_cnt.ld_inst_cnt = w_inst_ld_cnt;
assign w_ibuf_front_payload_next.resource_cnt.st_inst_cnt = w_inst_st_cnt;

bit_cnt #(.WIDTH(scariv_conf_pkg::DISP_SIZE)) u_bru_inst_cnt (.in(w_inst_bru_disped), .out(w_inst_bru_cnt));
assign w_ibuf_front_payload_next.resource_cnt.bru_inst_cnt     = w_inst_bru_cnt;
assign w_ibuf_front_payload_next.resource_cnt.bru_inst_valid   = w_inst_bru_disped;
assign w_ibuf_front_payload_next.resource_cnt.bru_branch_valid = w_inst_bru_disped & w_inst_is_br_branch;

bit_cnt #(.WIDTH(scariv_conf_pkg::DISP_SIZE)) u_csu_inst_cnt (.in(w_inst_csu_disped), .out(w_inst_csu_cnt));
assign w_ibuf_front_payload_next.resource_cnt.csu_inst_cnt   = w_inst_csu_cnt;
assign w_ibuf_front_payload_next.resource_cnt.csu_inst_valid = w_inst_csu_disped;

bit_cnt #(.WIDTH(scariv_conf_pkg::DISP_SIZE)) u_fpu_inst_cnt (.in(w_inst_fpu_disped), .out(w_inst_fpu_cnt));
generate for (genvar f_idx = 0; f_idx < scariv_conf_pkg::FPU_INST_NUM; f_idx++) begin : fpu_rsrc_loop
  localparam fpu_lane_width = scariv_conf_pkg::FPU_DISP_SIZE / scariv_conf_pkg::FPU_INST_NUM;
  logic [scariv_conf_pkg::DISP_SIZE-1: 0] w_lane_disped_valid[fpu_lane_width];
  logic [scariv_conf_pkg::DISP_SIZE-1: 0] w_lane_disped_valid_or;
  logic [$clog2(fpu_lane_width+1): 0] w_lane_disp_cnt;
  for (genvar i = 0; i < fpu_lane_width; i++) begin: cnt_loop
    bit_pick_1_pos #(.NUM(i*scariv_conf_pkg::FPU_INST_NUM + f_idx), .SEL_WIDTH(scariv_conf_pkg::DISP_SIZE)) bit_pos (.i_valids(w_inst_fpu_disped), .o_picked_pos(w_lane_disped_valid[i]));
  end
  bit_or #(.WIDTH(scariv_conf_pkg::DISP_SIZE), .WORDS(fpu_lane_width)) fpu_disped_or (.i_data(w_lane_disped_valid), .o_selected(w_lane_disped_valid_or));
  bit_cnt #(.WIDTH(scariv_conf_pkg::DISP_SIZE)) u_fpu_inst_cnt (.in(w_lane_disped_valid_or), .out(w_lane_disp_cnt));
  assign w_ibuf_front_payload_next.resource_cnt.fpu_inst_cnt[f_idx] = w_lane_disp_cnt;
  assign w_ibuf_front_payload_next.resource_cnt.fpu_inst_valid[f_idx] = w_lane_disped_valid_or;
end
endgenerate

`ifdef SIMULATION
logic [ 63: 0] r_kanata_cycle_count;
scariv_pkg::grp_id_t w_valid_grp_id;
generate for (genvar g_idx = 0; g_idx < scariv_conf_pkg::DISP_SIZE; g_idx++) begin : sim_grp_loop
  assign w_valid_grp_id[g_idx] = w_ibuf_front_payload_next.inst[g_idx].valid;
end
endgenerate

always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_kanata_cycle_count <= 'h0;
  end else begin
    if (w_ibuf_front_valid_next & ibuf_front_if.ready) begin
      r_kanata_cycle_count <= r_kanata_cycle_count + $countones(w_valid_grp_id);
    end
  end
end
`endif // SIMULATION

generate for (genvar d_idx = 0; d_idx < scariv_conf_pkg::DISP_SIZE; d_idx++) begin : disp_loop
  always_comb begin
    if (w_inst_disp_mask[d_idx]) begin
      w_ibuf_front_payload_next.inst[d_idx].valid = w_inst_disp_mask[d_idx];
      w_ibuf_front_payload_next.inst[d_idx].illegal_valid = w_inst_illegal_disp[d_idx];
      w_ibuf_front_payload_next.inst[d_idx].inst = w_expand_inst[d_idx];
      w_ibuf_front_payload_next.inst[d_idx].rvc_inst_valid = w_rvc_valid[d_idx];
      w_ibuf_front_payload_next.inst[d_idx].rvc_inst       = w_rvc_inst [d_idx];
      w_ibuf_front_payload_next.inst[d_idx].pc_addr = {w_inst_buf_data[0].pc[riscv_pkg::VADDR_W-1:$clog2(scariv_lsu_pkg::DCACHE_DATA_B_W)], {$clog2(scariv_lsu_pkg::DCACHE_DATA_B_W){1'b0}}} +
                                                      {w_rvc_buf_idx_with_offset[d_idx], 1'b0};

      w_ibuf_front_payload_next.inst[d_idx].wr_reg.valid   = rd_field_type[d_idx] != RD__;
      w_ibuf_front_payload_next.inst[d_idx].wr_reg.typ     = rd_field_type[d_idx] == RD_R3 ? scariv_pkg::GPR : scariv_pkg::FPR;
      w_ibuf_front_payload_next.inst[d_idx].wr_reg.regidx  = w_expand_inst[d_idx][11: 7];

      w_ibuf_front_payload_next.inst[d_idx].rd_regs[0].valid  = rs1_field_type[d_idx] != R1__;
      w_ibuf_front_payload_next.inst[d_idx].rd_regs[0].typ    = rs1_field_type[d_idx] == R1_R1 ? scariv_pkg::GPR : scariv_pkg::FPR;
      w_ibuf_front_payload_next.inst[d_idx].rd_regs[0].regidx = w_expand_inst[d_idx][19:15];

      w_ibuf_front_payload_next.inst[d_idx].rd_regs[1].valid  = rf2_field_type[d_idx] != R2__;
      w_ibuf_front_payload_next.inst[d_idx].rd_regs[1].typ    = rf2_field_type[d_idx] == R2_R2 ? scariv_pkg::GPR : scariv_pkg::FPR;
      w_ibuf_front_payload_next.inst[d_idx].rd_regs[1].regidx = w_expand_inst[d_idx][24:20];

      w_ibuf_front_payload_next.inst[d_idx].rd_regs[2].valid  = rs3_field_type[d_idx] != R3__;
      w_ibuf_front_payload_next.inst[d_idx].rd_regs[2].typ    = scariv_pkg::FPR;
      w_ibuf_front_payload_next.inst[d_idx].rd_regs[2].regidx = w_expand_inst[d_idx][31:27];

      w_ibuf_front_payload_next.inst[d_idx].cat        = w_inst_cat[d_idx];
      w_ibuf_front_payload_next.inst[d_idx].subcat     = w_inst_subcat[d_idx];

      w_ibuf_front_payload_next.inst[d_idx].pred_taken        = w_predict_taken_valid_lsb[d_idx] |
                                                                w_inst_is_call[d_idx] |
                                                                w_inst_is_ret [d_idx];
      w_ibuf_front_payload_next.inst[d_idx].bim_value         = w_expand_pred_info[d_idx].bim_value;
      w_ibuf_front_payload_next.inst[d_idx].btb_valid         = w_expand_pred_info[d_idx].btb_valid;
      // w_ibuf_front_payload_next.inst[d_idx].pred_target_vaddr = (w_inst_is_ret [d_idx] & w_expand_ras_info[d_idx].is_ret |
      //                                          w_inst_is_call[d_idx] & w_expand_ras_info[d_idx].is_call) ? w_expand_ras_info[d_idx].pred_target_vaddr :
      //                                         w_expand_pred_info[d_idx].pred_target_vaddr;
      w_ibuf_front_payload_next.inst[d_idx].pred_target_vaddr = w_inst_is_call[d_idx] ? iq_call_next_vaddr_oh :
                                                                w_inst_is_ret [d_idx] ? w_iq_ras_ret_vaddr :
                                                                w_expand_pred_info[d_idx].pred_target_vaddr;

      w_ibuf_front_payload_next.inst[d_idx].is_cond           = w_expand_pred_info[d_idx].is_cond;
      w_ibuf_front_payload_next.inst[d_idx].is_call           = w_inst_is_call[d_idx];
      w_ibuf_front_payload_next.inst[d_idx].is_ret            = w_inst_is_ret [d_idx];
      w_ibuf_front_payload_next.inst[d_idx].ras_index         = r_ras_index; // w_expand_ras_info[d_idx].ras_index;

      w_ibuf_front_payload_next.inst[d_idx].gshare_index      = w_expand_pred_info[d_idx].gshare_index     ;
      w_ibuf_front_payload_next.inst[d_idx].gshare_bhr        = w_expand_pred_info[d_idx].gshare_bhr       ;

`ifdef SIMULATION
      w_ibuf_front_payload_next.inst[d_idx].kanata_id = r_kanata_cycle_count + d_idx;
`endif // SIMULATION

    end else begin // if (w_inst_disp_mask[d_idx])
      w_ibuf_front_payload_next.inst[d_idx] = 'h0;
    end // else: !if(w_inst_disp_mask[d_idx])
  end // always_comb
end
endgenerate

generate for (genvar d_idx = 0; d_idx < scariv_conf_pkg::DISP_SIZE; d_idx++) begin : pc_vaddr_next_loop
  vaddr_t w_iq_call_offset;
  assign w_iq_call_offset = $signed({{(riscv_pkg::VADDR_W-11){w_ibuf_front_payload_next.inst[d_idx].inst[31]}},
                                     w_ibuf_front_payload_next.inst[d_idx].inst[31],
                                     w_ibuf_front_payload_next.inst[d_idx].inst[19:12],
                                     w_ibuf_front_payload_next.inst[d_idx].inst[20],
                                     w_ibuf_front_payload_next.inst[d_idx].inst[30:21], 1'b0});
  assign iq_call_next_vaddr_array [d_idx] = w_ibuf_front_payload_next.inst[d_idx].pc_addr + w_iq_call_offset;
  assign iq_call_stash_vaddr_array[d_idx] = w_ibuf_front_payload_next.inst[d_idx].pc_addr + (w_rvc_valid[d_idx] ? 'h2 : 'h4);
end
endgenerate
bit_oh_or #(.T(vaddr_t), .WORDS(scariv_conf_pkg::DISP_SIZE))
u_iq_call_pc_addr_oh (.i_oh(iq_is_call_valid_oh), .i_data(iq_call_next_vaddr_array), .o_selected(iq_call_next_vaddr_oh));

bit_oh_or #(.T(vaddr_t), .WORDS(scariv_conf_pkg::DISP_SIZE))
u_iq_call_stash_addr_oh (.i_oh(iq_is_call_valid_oh), .i_data(iq_call_stash_vaddr_array), .o_selected(iq_call_stash_vaddr_oh));

assign iq_is_call_valid_oh = {{scariv_conf_pkg::DISP_SIZE{1'b1}}{(w_ibuf_front_valid_next & ibuf_front_if.ready)}} & w_inst_disp_mask & w_inst_is_call;
assign iq_is_ret_valid_oh  = {{scariv_conf_pkg::DISP_SIZE{1'b1}}{(w_ibuf_front_valid_next & ibuf_front_if.ready)}} & w_inst_disp_mask & w_inst_is_ret;

always_comb begin
  if (w_br_flush) begin
    if (br_upd_if.is_ret) begin
      w_ras_index_next = br_upd_if.ras_index - 'h1;
    end else begin
      w_ras_index_next = br_upd_if.ras_index;
    end
  end else begin
    w_ras_index_next = r_ras_index;
  end

  if (|iq_is_ret_valid_oh) begin
    w_ras_index_next = w_ras_index_next - 'h1;
  end else if (|iq_is_call_valid_oh) begin
    w_ras_index_next = w_ras_index_next + 'h1;
  end
end

always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_ras_index <= 'h0;
  end else begin
    r_ras_index <= w_ras_index_next;
  end
end

// ===============================================================
// Generate Flush for CALL / RET
// If BTB prediction and RAS prediction are different, make flush
// ===============================================================
scariv_pkg::grp_id_t w_call_flush_valid;
scariv_pkg::grp_id_t w_ret_flush_valid;
generate for (genvar d_idx = 0; d_idx < scariv_conf_pkg::DISP_SIZE; d_idx++) begin : ras_flush_loop
  assign w_call_flush_valid[d_idx] = iq_is_call_valid_oh[d_idx] &
                                     (!w_expand_pred_info[d_idx].pred_taken |
                                      (iq_call_next_vaddr_array[d_idx] != w_expand_pred_info[d_idx].pred_target_vaddr));
  assign w_ret_flush_valid[d_idx] = iq_is_ret_valid_oh[d_idx] &
                                    (!w_expand_pred_info[d_idx].pred_taken |
                                     (w_iq_ras_ret_vaddr != w_expand_pred_info[d_idx].pred_target_vaddr));
end
endgenerate

always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    o_decode_flush.valid <= 1'b0;
  end else begin
    if (w_flush_pipeline) begin
      o_decode_flush.valid <= 1'b0;
    end else if (ibuf_front_if.ready) begin
      o_decode_flush.valid <= (|w_call_flush_valid) | (|w_ret_flush_valid);
      o_decode_flush.pred_vaddr <= (|w_call_flush_valid) ? iq_call_next_vaddr_oh :
                                   w_iq_ras_ret_vaddr;
    end
  end // else: !if(!i_reset_n)
end // always_ff @ (posedge i_clk, negedge i_reset_n)


scariv_pred_ras
u_ras
  (
   .i_clk     (i_clk),
   .i_reset_n (i_reset_n),

   .i_wr_valid (|iq_is_call_valid_oh   ),
   .i_wr_index (r_ras_index            ),
   .i_wr_pa    (iq_call_stash_vaddr_oh[riscv_pkg::VADDR_W-1: 1] ),

   .i_f2_rd_valid (|iq_is_ret_valid_oh),
   .i_f2_rd_index (r_ras_index-1      ),
   .o_f2_rd_pa    (w_iq_ras_ret_vaddr[riscv_pkg::VADDR_W-1: 1] ),

   .i_br_call_cmt_valid     ('h0),
   .i_br_call_cmt_ras_index ('h0),
   .i_br_call_cmt_wr_vpc    ('h0)
   );
assign w_iq_ras_ret_vaddr[0] = 1'b0;

`ifdef SIMULATION

import "DPI-C" function void rtl_push_ras (input longint rtl_time,
                                           input longint rtl_pc_vaddr,
                                           input longint rtl_index,
                                           input longint rtl_addr);

import "DPI-C" function void rtl_pop_ras (input longint rtl_time,
                                          input longint rtl_pc_vaddr,
                                          input longint rtl_index,
                                          input longint rtl_addr);

import "DPI-C" function void rtl_flush_ras (input longint rtl_time,
                                            input int     rtl_cmt_id,
                                            input int     rtl_grp_id,
                                            input longint rtl_pc_vaddr,
                                            input longint rtl_ras_index);

function logic [$clog2($bits(ic_block_t))-1: 0] encoder_func(logic [$bits(ic_block_t)-1: 0] in);
  for (int i = 0; i < $bits(ic_block_t); i++) begin
    if (in[i]) return i;
  end
  return 0;
endfunction // encoder_func

always_ff @ (negedge i_clk, negedge i_reset_n) begin
  if (i_reset_n) begin
    if (u_ras.i_wr_valid) begin
      rtl_push_ras ($time, w_ibuf_front_payload_next.pc_addr_debug + encoder_func(iq_is_call_valid_oh) << 1,
                    u_ras.i_wr_index, {u_ras.i_wr_pa, 1'b0});
    end
    if (u_ras.i_f2_rd_valid) begin
      rtl_pop_ras ($time, w_ibuf_front_payload_next.pc_addr_debug + encoder_func(iq_is_ret_valid_oh) << 1,
                   u_ras.i_f2_rd_index, {u_ras.o_f2_rd_pa, 1'b0});
    end

    if (w_br_flush) begin
      rtl_flush_ras ($time, br_upd_if.cmt_id, br_upd_if.grp_id,
                     br_upd_if.pc_vaddr, br_upd_if.ras_index);
    end
  end
end // always_ff @ (negedge i_clk, negedge i_reset_n)

`endif // SIMULATION


`ifdef SIMULATION
function void dump_json(int fp);
  $fwrite(fp, "  \"scariv_inst_buffer\" : {\n");

  // for(int idx=0; idx < scariv_pkg::INST_BUF_SIZE; idx++) begin
  //   if (r_inst_queue[idx].valid) begin
  //     $fwrite(fp, "    \"r_inst_queue[%d]\" : {\n", idx);
  //     $fwrite(fp, "      valid     : \"%d\",\n", r_inst_queue[idx].valid);
  //     $fwrite(fp, "      data    : \"0x%x\",\n", r_inst_queue[idx].data);
  //     $fwrite(fp, "      pc      : \"0x%x\",\n", r_inst_queue[idx].pc << 1);
  //     $fwrite(fp, "      byte_en : \"0x%x\",\n", r_inst_queue[idx].byte_en);
  //     $fwrite(fp, "    },\n");
  //   end
  // end

  for (int d_idx = 0; d_idx < scariv_conf_pkg::DISP_SIZE; d_idx++) begin : disp_loop
    if (ibuf_front_if.payload.inst[d_idx].valid) begin
      $fwrite(fp, "    \"ibuf_front_if.payload.inst[%d]\" : {", d_idx);
      $fwrite(fp, "      valid : %d,",      ibuf_front_if.payload.inst[d_idx].valid);
      $fwrite(fp, "      inst  : \"0x%08x\",",      ibuf_front_if.payload.inst[d_idx].inst);
      $fwrite(fp, "      pc_addr : \"0x%0x\",",    ibuf_front_if.payload.inst[d_idx].pc_addr);

      $fwrite(fp, "      rd_valid   : %d,", ibuf_front_if.payload.inst[d_idx].wr_reg.valid);
      $fwrite(fp, "      rd_type    : \"%d\",", ibuf_front_if.payload.inst[d_idx].wr_reg.typ);
      $fwrite(fp, "      rd_regidx  : %d,", ibuf_front_if.payload.inst[d_idx].wr_reg.regidx);

      $fwrite(fp, "      rs1_valid  : %d,", ibuf_front_if.payload.inst[d_idx].rd_regs[0].valid);
      $fwrite(fp, "      rs1_type   : \"%d\",", ibuf_front_if.payload.inst[d_idx].rd_regs[0].typ);
      $fwrite(fp, "      rs1_regidx : %d,", ibuf_front_if.payload.inst[d_idx].rd_regs[0].regidx);

      $fwrite(fp, "      rf2_valid  : %d,", ibuf_front_if.payload.inst[d_idx].rd_regs[1].valid);
      $fwrite(fp, "      rf2_type   : \"%d\",", ibuf_front_if.payload.inst[d_idx].rd_regs[1].typ);
      $fwrite(fp, "      rf2_regidx : %d,", ibuf_front_if.payload.inst[d_idx].rd_regs[1].regidx);

      $fwrite(fp, "      \"cat[d_idx]\" : \"%d\",", ibuf_front_if.payload.inst[d_idx].cat);
      $fwrite(fp, "    },\n");
    end
  end

  $fwrite(fp, "  },\n");
endfunction // dump

logic [63: 0] r_sim_cycle_count;
logic [63: 0] r_sim_ibuf_max_period;
logic [63: 0] r_sim_ibuf_entry_count;
logic [63: 0] r_sim_ibuf_issue_count;
logic [63: 0] r_sim_ibuf_issue_inst_count;

disp_t sim_disp_valid;

generate for (genvar d_idx = 0; d_idx < scariv_conf_pkg::DISP_SIZE; d_idx++) begin : sim_disp_loop
  assign sim_disp_valid[d_idx] = ibuf_front_if.payload.inst[d_idx].valid;
end
endgenerate

always_ff @ (negedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_sim_ibuf_max_period  <= 'h0;
    r_sim_ibuf_entry_count <= 'h0;
    r_sim_cycle_count  <= 'h0;
    r_sim_ibuf_issue_count <= 'h0;
    r_sim_ibuf_issue_inst_count <= 'h0;
  end else begin
    r_sim_cycle_count <= r_sim_cycle_count + 'h1;
    if (r_sim_cycle_count % sim_pkg::COUNT_UNIT == sim_pkg::COUNT_UNIT-1) begin
      r_sim_ibuf_max_period  <= 'h0;
      r_sim_ibuf_entry_count <= 'h0;
      r_sim_ibuf_issue_count <= 'h0;
      r_sim_ibuf_issue_inst_count <= 'h0;
    end else begin
      if (!w_inst_buf_empty) begin
        if (w_inst_buf_full) begin
          r_sim_ibuf_max_period  <= r_sim_ibuf_max_period + 'h1;
        end
        r_sim_ibuf_entry_count <= r_sim_ibuf_entry_count + $countones(u_inst_queue.r_valids);
      end
      if (ibuf_front_if.valid & ibuf_front_if.ready) begin
        r_sim_ibuf_issue_count <= r_sim_ibuf_issue_count + 'h1;
        r_sim_ibuf_issue_inst_count <= r_sim_ibuf_issue_inst_count + $countones(sim_disp_valid);
      end
    end // else: !if(r_sim_cycle_count % sim_pkg::COUNT_UNIT == sim_pkg::COUNT_UNIT-1)
  end // else: !if(!i_reset_n)
end // always_ff @ (negedge i_clk, negedge i_reset_n)

function void dump_perf (int fp);
  $fwrite(fp, "  \"inst_buffer\" : {");
  $fwrite(fp, "  \"issued_times\" : %5d, ", r_sim_ibuf_issue_count);
  $fwrite(fp, "  \"issued_insts\" : %5d, ", r_sim_ibuf_issue_inst_count);
  $fwrite(fp, "  \"max_period\" : %5d, ", r_sim_ibuf_max_period);
  $fwrite(fp, "  \"average count\" : %5f},\n", r_sim_ibuf_entry_count / 1000.0);
endfunction // dump_perf

import "DPI-C" function void log_dispatch
(
 input longint timeinfo,
 input longint id,
 input longint paddr,
 input int     inst
);

import "DPI-C" function void log_stage
(
 input longint id,
 input string stage
);

always_ff @ (negedge i_clk, negedge i_reset_n) begin
  if (i_reset_n) begin
    if (ibuf_front_if.valid & ibuf_front_if.ready) begin
      for (int i = 0; i < scariv_conf_pkg::DISP_SIZE; i++) begin
        if (ibuf_front_if.payload.inst[i].valid) begin
          log_dispatch ($time, ibuf_front_if.payload.inst[i].kanata_id,
                        ibuf_front_if.payload.inst[i].pc_addr, ibuf_front_if.payload.inst[i].inst);
          log_stage (ibuf_front_if.payload.inst[i].kanata_id, "Di");
        end
      end
    end
  end
end

`endif // SIMULATION


initial begin
  if (scariv_conf_pkg::DISP_SIZE * 32 > scariv_conf_pkg::ICACHE_DATA_W) begin
    $fatal(0, "32xDISP_SIZE larger than ICache Line size is not supported");
  end
end

endmodule // inst_buffer
