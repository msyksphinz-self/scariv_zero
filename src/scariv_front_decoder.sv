// ------------------------------------------------------------------------
// NAME : scariv_front_decoder
// TYPE : module
// ------------------------------------------------------------------------
// SCARIV Instruction Buffer with Register Decoder
// ------------------------------------------------------------------------
//
// ------------------------------------------------------------------------

module scariv_front_decoder
  import scariv_pkg::*;
  import scariv_ic_pkg::*;
  import decoder_reg_pkg::*;
  (
   input logic  i_clk,
   input logic  i_reset_n,
   input logic  i_flush_valid,

   /* CSR information */
   csr_info_if.slave csr_info,

   btb_search_if.monitor    btb_search_if,
   bim_search_if.monitor    bim_search_if,
   ras_search_if.slave      ras_search_if,
   gshare_search_if.monitor gshare_search_if,

   input logic                           i_f2_ubtb_predict_valid,
   input scariv_predict_pkg::ubtb_info_t i_f2_ubtb_info,

   output decode_flush_t o_decode_flush,

   output logic                       o_inst_ready,
   input scariv_pkg::inst_buffer_in_t i_f2_inst,
   scariv_front_if.master             ibuf_front_if,

   br_upd_if.slave br_upd_if
   );

// Queue variables
logic    w_inst_buf_empty;
logic    w_inst_buf_full;
logic    w_inst_queue_pop;


logic    w_br_flush;
logic    w_flush_pipeline;
assign w_br_flush       = br_upd_if.update & ~br_upd_if.dead & br_upd_if.mispredict;
assign w_flush_pipeline = i_flush_valid | w_br_flush;

logic    w_ptr_in_fire;
logic    w_ptr_out_fire;
assign w_ptr_in_fire  = i_f2_inst.valid & o_inst_ready;
assign w_ptr_out_fire = w_head_all_inst_issued | w_head_predict_taken_issued |
                        w_inst_buf_valid[0] & r_pred_entry_kill_valid ;

logic [ 1: 0]               w_inst_buf_valid;
scariv_ibuf_pkg::inst_buf_t w_inst_buf_data[2];

// ------------------------
// Queue Control Pointer
// ------------------------
scariv_ibuf_pkg::inst_buf_t w_inst_buf_load;
assign w_inst_buf_load = scariv_ibuf_pkg::assign_entry(inst_buf_in);

ring_fifo_2ptr
  #(.T(scariv_ibuf_pkg::inst_buf_t),
    .DEPTH (scariv_pkg::INST_BUF_SIZE)
    )
u_inst_queue
(
 .i_clk     (i_clk    ),
 .i_reset_n (i_reset_n),

 .i_clear   (w_flush_pipeline),

 .i_push (w_ptr_in_fire),
 .i_data (w_inst_buf_load),

 .o_empty (w_inst_buf_empty),
 .o_full  (w_inst_buf_full),

 .i_pop  (w_ptr_out_fire),

 .o_valid0 (w_inst_buf_valid[0]),
 .o_data0  (w_inst_buf_data [0]),

 .o_valid1 (w_inst_buf_valid[1]),
 .o_data1  (w_inst_buf_data [1])
 );

assign o_inst_ready = !w_inst_buf_full;


// =================================
// RVC Expand from 16-bit to 32-bit
// =================================
generate for (genvar w_idx = 0; w_idx < scariv_conf_pkg::DISP_SIZE; w_idx++) begin : gen_rvc_expand_loop
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
                                 & (&w_rvc_byte_en);

      w_fetch_except[w_idx]       = w_inst_buf_valid_b0 &
                                    w_inst_buf_entry_b0.tlb_except_valid;
      w_fetch_except_cause[w_idx] = w_inst_buf_entry_b0.tlb_except_cause;
      w_fetch_except_tval [w_idx] = {w_inst_buf_entry_b0.pc[riscv_pkg::VADDR_W-1:$clog2(scariv_lsu_pkg::ICACHE_DATA_B_W)],
                                     w_rvc_buf_idx_with_offset[w_idx][$clog2(ic_word_num)-1:0], 1'b0};

      w_expand_pred_info[w_idx] = w_inst_buf_entry_b0.pred_info[w_rvc_buf_idx_with_offset[w_idx][$clog2(ic_word_num)-1:0]];
      w_expand_pred_index[w_idx] = w_inst_buf_ptr_b0;

      w_expand_ras_info[w_idx] = w_inst_buf_entry_b0.ras_info[w_rvc_buf_idx_with_offset[w_idx][$clog2(ic_word_num)-1:0]];
    end else begin
      // Normal instruction
      /* verilator lint_off ALWCOMBORDER */
      w_rvc_buf_idx[w_idx + 1] = w_rvc_buf_idx[w_idx] + 2;
      w_expand_inst[w_idx]     = {w_rvc_next_inst, w_local_rvc_inst};
      w_expanded_valid[w_idx]  = w_inst_buf_valid_b0 &
                                 w_inst_buf_valid_b2 &
                                 &{w_rvc_next_byte_en, w_rvc_byte_en};
      w_rvc_inst[w_idx]    = 'h0;
      w_rvc_valid[w_idx]   = 1'b0;

      w_fetch_except[w_idx]       = w_inst_buf_valid_b0 & w_inst_buf_entry_b0.tlb_except_valid |
                                    w_inst_buf_valid_b2 & w_inst_buf_entry_b2.tlb_except_valid;
      w_fetch_except_cause[w_idx] = w_inst_buf_entry_b0.tlb_except_valid ? w_inst_buf_entry_b0.tlb_except_cause :
                                    w_inst_buf_entry_b2.tlb_except_cause;
      w_fetch_except_tval [w_idx] = w_inst_buf_entry_b0.tlb_except_valid ?
                                    {w_inst_buf_entry_b0.pc[riscv_pkg::VADDR_W-1:$clog2(scariv_lsu_pkg::ICACHE_DATA_B_W)], w_rvc_buf_idx_with_offset[w_idx][$clog2(ic_word_num)-1:0], 1'b0} :
                                    {w_inst_buf_entry_b2.pc[riscv_pkg::VADDR_W-1:$clog2(scariv_lsu_pkg::ICACHE_DATA_B_W)], w_rvc_buf_idx_with_offset_b2[$clog2(ic_word_num)-1:0], 1'b0};

      w_expand_pred_info [w_idx] = w_inst_buf_entry_b2.pred_info[w_rvc_buf_idx_with_offset_b2[$clog2(ic_word_num)-1:0]];
      w_expand_pred_index[w_idx] = w_inst_buf_ptr_b2;

      w_expand_ras_info  [w_idx] = w_inst_buf_entry_b2.ras_info [w_rvc_buf_idx_with_offset_b2[$clog2(ic_word_num)-1:0]];
    end // else: !if(w_rvc_inst[1:0] != 2'b11)
  end // always_comb

  assign w_predict_taken_valid_array[w_idx] = w_expanded_valid[w_idx] &
                                              (w_expand_pred_info[w_idx].btb_valid & w_expand_pred_info[w_idx].pred_taken); // | // BIM
                                               /* w_expand_ras_info[w_idx].is_call |  // RAS
                                                w_expand_ras_info[w_idx].is_ret);  // RAS */


end endgenerate

generate for (genvar w_idx = 0; w_idx < scariv_conf_pkg::DISP_SIZE; w_idx++) begin : gen_decoder_loop
end endgenerate

endmodule // scariv_front_decoder
