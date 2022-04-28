module msrh_inst_buffer
  import decoder_reg_pkg::*;
  (
 input logic i_clk,
 input logic i_reset_n,
 input logic i_flush_valid,

 /* CSR information */
 csr_info_if.slave                csr_info,

 btb_search_if.monitor btb_search_if,
 bim_search_if.monitor bim_search_if,
 ras_search_if.slave   ras_search_if,

 output logic                     o_inst_ready,
 input msrh_pkg::inst_buffer_in_t i_s2_inst,
 disp_if.master                   iq_disp
 );

logic                                       w_inst_buffer_fire;

msrh_pkg::grp_id_t w_inst_arith_pick_up;
msrh_pkg::grp_id_t w_inst_muldiv_pick_up;
msrh_pkg::grp_id_t w_inst_mem_pick_up;
msrh_pkg::grp_id_t w_inst_bru_pick_up;
msrh_pkg::grp_id_t w_inst_csu_pick_up;
msrh_pkg::grp_id_t w_inst_fpu_pick_up;
msrh_pkg::grp_id_t w_inst_except_pick_up;
msrh_pkg::grp_id_t w_fetch_except_pick_up;
msrh_pkg::grp_id_t w_inst_illegal_pick_up;

msrh_pkg::grp_id_t w_inst_arith_disp;
msrh_pkg::grp_id_t w_inst_muldiv_disp;
msrh_pkg::grp_id_t w_inst_mem_disp;
msrh_pkg::grp_id_t w_inst_ld_disp;
msrh_pkg::grp_id_t w_inst_st_disp;
msrh_pkg::grp_id_t w_inst_bru_disp;
msrh_pkg::grp_id_t w_inst_csu_disp;
msrh_pkg::grp_id_t w_inst_fpu_disp;
msrh_pkg::grp_id_t w_inst_illegal_disp;
msrh_pkg::grp_id_t w_fetch_except_disp;

msrh_pkg::grp_id_t w_inst_disp_or;
msrh_pkg::grp_id_t w_inst_disp_mask;

localparam ic_word_num = msrh_lsu_pkg::ICACHE_DATA_B_W / 2;
decoder_inst_cat_pkg::inst_cat_t    w_inst_cat   [msrh_conf_pkg::DISP_SIZE];
decoder_inst_cat_pkg::inst_subcat_t w_inst_subcat[msrh_conf_pkg::DISP_SIZE];
msrh_pkg::grp_id_t w_inst_gen_except;
msrh_pkg::grp_id_t w_fetch_except;
msrh_pkg::grp_id_t w_inst_is_arith;
msrh_pkg::grp_id_t w_inst_is_muldiv;
msrh_pkg::grp_id_t w_inst_is_ld;
msrh_pkg::grp_id_t w_inst_is_st;
msrh_pkg::grp_id_t w_inst_is_br;
msrh_pkg::grp_id_t w_inst_is_csu;
msrh_pkg::grp_id_t w_inst_is_fpu;
msrh_pkg::grp_id_t w_inst_illegal;

msrh_pkg::grp_id_t w_inst_is_call;
msrh_pkg::grp_id_t w_inst_is_ret;
msrh_pkg::grp_id_t w_inst_is_call_ret_lsb;

msrh_pkg::except_t w_fetch_except_cause[msrh_conf_pkg::DISP_SIZE];
riscv_pkg::xlen_t       w_fetch_except_tval[msrh_conf_pkg::DISP_SIZE];

msrh_pkg::grp_id_t w_inst_gen_except_lsb;

rd_t rd_field_type [msrh_conf_pkg::DISP_SIZE];
r1_t rs1_field_type[msrh_conf_pkg::DISP_SIZE];
r2_t rs2_field_type[msrh_conf_pkg::DISP_SIZE];
r3_t rs3_field_type[msrh_conf_pkg::DISP_SIZE];

logic [$clog2(ic_word_num)-1:0] r_head_start_pos;
logic [$clog2(ic_word_num):0]   w_head_start_pos_next;
logic                           w_head_all_inst_issued;
logic                           w_head_predict_taken_issued;
logic                           w_predict_taken_valid;
msrh_pkg::grp_id_t w_predict_taken_valid_array;
msrh_pkg::grp_id_t                     w_predict_taken_valid_lsb;
logic [$clog2(msrh_pkg::INST_BUF_SIZE)-1: 0] w_pred_lsb_index;

msrh_pkg::grp_id_t w_inst_arith_disped;
msrh_pkg::grp_id_t w_inst_muldiv_disped;
msrh_pkg::grp_id_t w_inst_mem_disped;
msrh_pkg::grp_id_t w_inst_ld_disped;
msrh_pkg::grp_id_t w_inst_st_disped;
msrh_pkg::grp_id_t w_inst_bru_disped;
msrh_pkg::grp_id_t w_inst_csu_disped;
msrh_pkg::grp_id_t w_inst_fpu_disped;

typedef struct packed {
  logic                           pred_taken;
  logic [1:0]                     bim_value;
  logic                           btb_valid;
  msrh_pkg::vaddr_t pred_target_vaddr;
} pred_info_t;

pred_info_t w_expand_pred_info[msrh_conf_pkg::DISP_SIZE];
logic [$clog2(msrh_pkg::INST_BUF_SIZE)-1:0] w_expand_pred_index[msrh_conf_pkg::DISP_SIZE];

typedef struct packed {
  logic                           is_call;
  logic                           is_ret;
  logic [$clog2(msrh_conf_pkg::RAS_ENTRY_SIZE)-1: 0] ras_index;
  msrh_pkg::vaddr_t                    pred_target_vaddr;
} ras_info_t;

ras_info_t w_expand_ras_info[msrh_conf_pkg::DISP_SIZE];

typedef struct packed {
  logic                                      valid;
  logic                                      dead;
  logic [riscv_pkg::VADDR_W-1: 1]            pc;
  logic [msrh_conf_pkg::ICACHE_DATA_W-1: 0]  data;
  logic [msrh_lsu_pkg::ICACHE_DATA_B_W-1: 0] byte_en;
  logic                                      tlb_except_valid;
  msrh_pkg::except_t                         tlb_except_cause;

  pred_info_t [msrh_lsu_pkg::ICACHE_DATA_B_W/2-1: 0] pred_info;
  ras_info_t  [msrh_lsu_pkg::ICACHE_DATA_B_W/2-1: 0] ras_info;
`ifdef SIMULATION
  msrh_pkg::vaddr_t            pc_dbg;
`endif // SIMULATION
} inst_buf_t;

inst_buf_t r_inst_queue[msrh_pkg::INST_BUF_SIZE];
logic [msrh_pkg::INST_BUF_SIZE-1:0]      w_inst_buffer_valid;

logic [$clog2(msrh_pkg::INST_BUF_SIZE)-1:0] r_inst_buffer_inptr;
logic [$clog2(msrh_pkg::INST_BUF_SIZE)-1:0] r_inst_buffer_outptr;
logic [$clog2(msrh_pkg::INST_BUF_SIZE)-1:0] w_inst_buffer_outptr_p1;
logic                                       w_ptr_in_fire;
logic                                       w_ptr_out_fire;

logic [$clog2(ic_word_num)+1-1:1]           w_out_inst_q_pc;

logic                                       w_flush_pipeline;

// =================================
// RVC Expand from 16-bit to 32-bit
// =================================
/* verilator lint_off UNOPTFLAT */
logic [$clog2(ic_word_num): 0]       w_rvc_buf_idx[msrh_conf_pkg::DISP_SIZE + 1];
logic [$clog2(ic_word_num): 0]       w_rvc_buf_idx_with_offset[msrh_conf_pkg::DISP_SIZE + 1];
logic [31: 0]                        w_expand_inst[msrh_conf_pkg::DISP_SIZE];
msrh_pkg::grp_id_t w_expanded_valid;
logic [15: 0]                        w_rvc_inst[msrh_conf_pkg::DISP_SIZE];
msrh_pkg::grp_id_t w_rvc_valid;

/* verilator lint_off WIDTH */
assign w_head_all_inst_issued = w_inst_buffer_fire & ((w_head_start_pos_next + w_out_inst_q_pc) >= ic_word_num);
assign w_head_predict_taken_issued = w_inst_buffer_fire & w_predict_taken_valid & iq_disp.is_br_included;
assign w_ptr_in_fire  = i_s2_inst.valid & o_inst_ready;
assign w_ptr_out_fire = w_head_all_inst_issued | w_head_predict_taken_issued |
                        r_inst_queue[r_inst_buffer_outptr].valid & r_inst_queue[r_inst_buffer_outptr].dead ;

assign w_flush_pipeline = i_flush_valid;

// Queue Control Pointer
inoutptr
  #(
    .SIZE(msrh_pkg::INST_BUF_SIZE)
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

assign w_inst_buffer_outptr_p1 = r_inst_buffer_outptr == msrh_pkg::INST_BUF_SIZE-1 ? 'h0 :
                                 r_inst_buffer_outptr + 'h1;

assign w_inst_buffer_fire = iq_disp.valid & iq_disp.ready;

generate for (genvar idx = 0; idx < msrh_pkg::INST_BUF_SIZE; idx++) begin : inst_buf_loop

  assign w_inst_buffer_valid[idx] = r_inst_queue[idx].valid;

  always_ff @ (posedge i_clk, negedge i_reset_n) begin
    if (!i_reset_n) begin
      r_inst_queue[idx] <= 'h0;
    end else begin
      if (w_flush_pipeline) begin
        r_inst_queue[idx] <= 'h0;
      end else if (w_ptr_in_fire & (r_inst_buffer_inptr == idx)) begin
        r_inst_queue[idx].valid   <= 1'b1;
        r_inst_queue[idx].data    <= i_s2_inst.inst;
        r_inst_queue[idx].pc      <= i_s2_inst.pc;
        r_inst_queue[idx].byte_en <= i_s2_inst.byte_en;
        r_inst_queue[idx].tlb_except_valid <= i_s2_inst.tlb_except_valid;
        r_inst_queue[idx].tlb_except_cause <= i_s2_inst.tlb_except_cause;

        for (int b_idx = 0; b_idx < msrh_lsu_pkg::ICACHE_DATA_B_W/2; b_idx++) begin : pred_loop
          r_inst_queue[idx].pred_info[b_idx].pred_taken       <= bim_search_if.s2_bim_value[b_idx][1] & btb_search_if.s2_hit[b_idx] |
                                                                 ras_search_if.s2_is_ret   [b_idx];
          r_inst_queue[idx].pred_info[b_idx].bim_value        <= bim_search_if.s2_bim_value[b_idx];
          r_inst_queue[idx].pred_info[b_idx].btb_valid        <= btb_search_if.s2_hit[b_idx];
          r_inst_queue[idx].pred_info[b_idx].pred_target_vaddr <= btb_search_if.s2_target_vaddr[b_idx];

          r_inst_queue[idx].ras_info[b_idx].is_call           <= ras_search_if.s2_is_call[b_idx];
          r_inst_queue[idx].ras_info[b_idx].is_ret            <= ras_search_if.s2_is_ret [b_idx];
          r_inst_queue[idx].ras_info[b_idx].ras_index         <= ras_search_if.s2_ras_be [b_idx/2] & ras_search_if.s2_is_ret [b_idx] ? ras_search_if.s2_ras_index - 1 :
                                                                 ras_search_if.s2_ras_index;
          r_inst_queue[idx].ras_info[b_idx].pred_target_vaddr <= ras_search_if.s2_is_call[b_idx] ? {ras_search_if.s2_call_target_vaddr, 1'b0} : {ras_search_if.s2_ras_vaddr, 1'b0};
        end // block: pred_loop

`ifdef SIMULATION
        r_inst_queue[idx].pc_dbg   <= {i_s2_inst.pc, 1'b0};
`endif // SIMULATION
      end else if ((w_head_all_inst_issued |
                    w_head_predict_taken_issued |
                    r_inst_queue[idx].valid & r_inst_queue[idx].dead) & (r_inst_buffer_outptr == idx)) begin
        r_inst_queue[idx].valid  <= 1'b0;
        r_inst_queue[idx].dead   <= 1'b0;
      end else if (w_head_predict_taken_issued & (w_pred_lsb_index == idx)) begin
        r_inst_queue[idx].dead <= 1'b1;
      end // if (i_s2_inst.valid & o_inst_ready)
    end // else: !if(!i_reset_n)
  end // always_ff @ (posedge i_clk, negedge i_reset_n)

end // block: inst_buf_loop
endgenerate


assign o_inst_ready = !(&w_inst_buffer_valid);

// Extract next start position of decoding
logic [ic_word_num-1: 0] w_bit_next_start_pos_oh;
bit_extract_lsb
  #(.WIDTH(ic_word_num))
u_start_pos_bit
  (
   .in({{(ic_word_num - msrh_conf_pkg::DISP_SIZE){1'b1}}, ~w_inst_disp_mask}),
   .out(w_bit_next_start_pos_oh)
   );
// Note: MSB (DISP_SIZE) bit is dummy.
bit_oh_or #(.T(logic[$clog2(ic_word_num): 0]), .WORDS(msrh_conf_pkg::DISP_SIZE+1))
u_select_next_pos (
 .i_oh       (w_bit_next_start_pos_oh[msrh_conf_pkg::DISP_SIZE:0]),
 .i_data     (w_rvc_buf_idx),
 .o_selected (w_head_start_pos_next)
);


assign w_out_inst_q_pc = r_inst_queue[r_inst_buffer_outptr].pc[1+:$clog2(ic_word_num)];

always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_head_start_pos   <= 'h0;
  end else begin
    if (w_flush_pipeline | w_head_predict_taken_issued) begin
      r_head_start_pos <= 'h0;
    end else if (w_head_all_inst_issued) begin
      // Move to next Line, carring lower bits for next
      r_head_start_pos <= w_head_start_pos_next + w_out_inst_q_pc;
    end else if (w_inst_buffer_fire) begin
      r_head_start_pos <= w_head_start_pos_next[$clog2(ic_word_num)-1:0];
    end
  end
end

// =================================
// RVC Expand from 16-bit to 32-bit
// =================================
assign w_rvc_buf_idx[0] = {1'b0, r_head_start_pos};
generate for (genvar w_idx = 0; w_idx < msrh_conf_pkg::DISP_SIZE; w_idx++) begin : rvc_expand_loop
  logic [15: 0]                    w_local_rvc_inst;
  logic [15: 0]                    w_rvc_next_inst;
  logic [ 1: 0]                    w_rvc_byte_en;
  logic [ 1: 0]                    w_rvc_next_byte_en;
  logic [$clog2(msrh_pkg::INST_BUF_SIZE)-1: 0] w_inst_buf_ptr_b0;
  logic [$clog2(msrh_pkg::INST_BUF_SIZE)-1: 0] w_inst_buf_ptr_b2;

  logic [31: 0]                                w_local_expand_inst;
  logic [$clog2(ic_word_num): 0]               w_rvc_buf_idx_with_offset_b2;


  assign w_rvc_buf_idx_with_offset[w_idx] = w_rvc_buf_idx[w_idx] + w_out_inst_q_pc;
  assign w_rvc_buf_idx_with_offset_b2     = w_rvc_buf_idx_with_offset[w_idx] + 1;

  /* verilator lint_off WIDTH */
  assign w_inst_buf_ptr_b0 = (w_rvc_buf_idx_with_offset[w_idx] < ic_word_num) ? r_inst_buffer_outptr :
                             w_inst_buffer_outptr_p1;
  assign w_inst_buf_ptr_b2 = (w_rvc_buf_idx_with_offset_b2 < ic_word_num) ? r_inst_buffer_outptr :
                             w_inst_buffer_outptr_p1;

  assign w_local_rvc_inst   = r_inst_queue[w_inst_buf_ptr_b0].data   [ w_rvc_buf_idx_with_offset[w_idx][$clog2(ic_word_num)-1:0]*16 +:16];
  assign w_rvc_next_inst    = r_inst_queue[w_inst_buf_ptr_b2].data   [ w_rvc_buf_idx_with_offset_b2    [$clog2(ic_word_num)-1:0]*16 +:16];
  assign w_rvc_byte_en      = r_inst_queue[w_inst_buf_ptr_b0].byte_en[ w_rvc_buf_idx_with_offset[w_idx][$clog2(ic_word_num)-1:0] *2 +: 2];
  assign w_rvc_next_byte_en = r_inst_queue[w_inst_buf_ptr_b2].byte_en[ w_rvc_buf_idx_with_offset_b2    [$clog2(ic_word_num)-1:0] *2 +: 2];
  msrh_rvc_expander u_msrh_rvc_expander (.i_rvc_inst(w_local_rvc_inst), .out_32bit(w_local_expand_inst));

  always_comb begin
    if (w_local_rvc_inst[1:0] != 2'b11) begin
      // RVC instruction
      /* verilator lint_off ALWCOMBORDER */
      w_rvc_buf_idx[w_idx + 1] = w_rvc_buf_idx[w_idx] + 1;
      w_expand_inst[w_idx]     = w_local_expand_inst;
      w_rvc_inst[w_idx]    = w_local_rvc_inst;
      w_rvc_valid[w_idx]   = 1'b1;
      w_expanded_valid[w_idx]  = r_inst_queue[w_inst_buf_ptr_b0].valid &
                                 !r_inst_queue[w_inst_buf_ptr_b0].dead &
                                 & (&w_rvc_byte_en);

      w_fetch_except[w_idx]       = r_inst_queue[w_inst_buf_ptr_b0].valid &
                                    r_inst_queue[w_inst_buf_ptr_b0].tlb_except_valid;
      w_fetch_except_cause[w_idx] = r_inst_queue[w_inst_buf_ptr_b0].tlb_except_cause;
      w_fetch_except_tval [w_idx] = iq_disp.inst[w_idx].pc_addr;

      w_expand_pred_info[w_idx] = r_inst_queue[w_inst_buf_ptr_b0].pred_info[w_rvc_buf_idx_with_offset[w_idx][$clog2(ic_word_num)-1:0]];
      w_expand_pred_index[w_idx] = w_inst_buf_ptr_b0;

      w_expand_ras_info[w_idx] = r_inst_queue[w_inst_buf_ptr_b0].ras_info[w_rvc_buf_idx_with_offset[w_idx][$clog2(ic_word_num)-1:0]];
    end else begin
      // Normal instruction
      /* verilator lint_off ALWCOMBORDER */
      w_rvc_buf_idx[w_idx + 1] = w_rvc_buf_idx[w_idx] + 2;
      w_expand_inst[w_idx]     = {w_rvc_next_inst, w_local_rvc_inst};
      w_expanded_valid[w_idx]  = r_inst_queue[w_inst_buf_ptr_b0].valid & !r_inst_queue[w_inst_buf_ptr_b0].dead &
                                 r_inst_queue[w_inst_buf_ptr_b2].valid & !r_inst_queue[w_inst_buf_ptr_b2].dead &
                                 &{w_rvc_next_byte_en, w_rvc_byte_en};
      w_rvc_inst[w_idx]    = 'h0;
      w_rvc_valid[w_idx]   = 1'b0;

      w_fetch_except[w_idx]       = r_inst_queue[w_inst_buf_ptr_b0].valid & r_inst_queue[w_inst_buf_ptr_b0].tlb_except_valid |
                                    r_inst_queue[w_inst_buf_ptr_b2].valid & r_inst_queue[w_inst_buf_ptr_b2].tlb_except_valid;
      w_fetch_except_cause[w_idx] = r_inst_queue[w_inst_buf_ptr_b0].tlb_except_valid ? r_inst_queue[w_inst_buf_ptr_b0].tlb_except_cause :
                                    r_inst_queue[w_inst_buf_ptr_b2].tlb_except_cause;
      w_fetch_except_tval [w_idx] = r_inst_queue[w_inst_buf_ptr_b0].tlb_except_valid ? iq_disp.inst[w_idx].pc_addr :
                                    iq_disp.inst[w_idx].pc_addr + 'h2;

      w_expand_pred_info [w_idx] = r_inst_queue[w_inst_buf_ptr_b2].pred_info[w_rvc_buf_idx_with_offset_b2[$clog2(ic_word_num)-1:0]];
      w_expand_pred_index[w_idx] = w_inst_buf_ptr_b2;

      w_expand_ras_info  [w_idx] = r_inst_queue[w_inst_buf_ptr_b2].ras_info [w_rvc_buf_idx_with_offset_b2[$clog2(ic_word_num)-1:0]];
    end // else: !if(w_rvc_inst[1:0] != 2'b11)
  end // always_comb

  assign w_predict_taken_valid_array[w_idx] = w_expand_pred_info[w_idx].btb_valid & w_expand_pred_info[w_idx].pred_taken | // BIM
                                              w_expand_ras_info[w_idx].is_call |  // RAS
                                              w_expand_ras_info[w_idx].is_ret;  // RAS

end
endgenerate



generate for (genvar w_idx = 0; w_idx < msrh_conf_pkg::DISP_SIZE; w_idx++) begin : word_loop
  logic[ 3: 0] w_raw_cat;
  logic [ 1: 0] w_raw_subcat;
  logic        w_raw_gen_except;
  decoder_inst_cat
  u_decoder_inst_cat
    (
     .inst(w_expand_inst[w_idx]),
     .inst_cat(w_raw_cat),
     .inst_subcat(w_raw_subcat),
     .gen_except(w_raw_gen_except)
     );
  assign w_inst_cat   [w_idx] = decoder_inst_cat_pkg::inst_cat_t'(w_raw_cat);
  assign w_inst_subcat[w_idx] = decoder_inst_cat_pkg::inst_subcat_t'(w_raw_subcat);

  decoder_reg
  u_decoder_reg
    (
     .inst(w_expand_inst[w_idx]),
     .rd(rd_field_type [w_idx]),
     .r1(rs1_field_type[w_idx]),
     .r2(rs2_field_type[w_idx]),
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

  assign w_inst_is_arith [w_idx] = w_expanded_valid[w_idx] & (w_inst_cat[w_idx] == decoder_inst_cat_pkg::INST_CAT_ARITH );
  assign w_inst_is_muldiv[w_idx] = w_expanded_valid[w_idx] & (w_inst_cat[w_idx] == decoder_inst_cat_pkg::INST_CAT_MULDIV);
  assign w_inst_is_ld    [w_idx] = w_expanded_valid[w_idx] & !w_inst_ld_fpu_illegal & (w_inst_cat[w_idx] == decoder_inst_cat_pkg::INST_CAT_LD    );
  assign w_inst_is_st    [w_idx] = w_expanded_valid[w_idx] & !w_inst_st_fpu_illegal & (w_inst_cat[w_idx] == decoder_inst_cat_pkg::INST_CAT_ST    );
  assign w_inst_is_br    [w_idx] = w_expanded_valid[w_idx] & (w_inst_cat[w_idx] == decoder_inst_cat_pkg::INST_CAT_BR    );
  assign w_inst_is_csu   [w_idx] = w_expanded_valid[w_idx] & (w_inst_cat[w_idx] == decoder_inst_cat_pkg::INST_CAT_CSU   );
  assign w_inst_is_fpu   [w_idx] = w_expanded_valid[w_idx] & !w_inst_arith_fpu_illegal & (w_inst_cat[w_idx] == decoder_inst_cat_pkg::INST_CAT_FPU   );

  logic          w_is_std_call;
  logic          w_is_std_ret;
  assign w_is_std_call = (w_expand_inst[w_idx][ 6:0] == 7'b1101111) &
                         (w_expand_inst[w_idx][11:7] == 5'h1);
  assign w_is_std_ret = w_expand_inst[w_idx] == 32'h00008067;

  assign w_inst_is_call  [w_idx] = w_expanded_valid[w_idx] & w_is_std_call;
  assign w_inst_is_ret   [w_idx] = w_expanded_valid[w_idx] & w_is_std_ret;

  assign w_inst_illegal  [w_idx] = w_expanded_valid[w_idx] &
                                   ((w_inst_cat[w_idx] == decoder_inst_cat_pkg::INST_CAT__ ) | w_inst_fpu_illegal);

  assign w_inst_gen_except[w_idx]  = w_expanded_valid[w_idx] & w_raw_gen_except;
end // block: word_loop
endgenerate

assign w_inst_arith_pick_up  = w_inst_is_arith | w_inst_is_muldiv;
assign w_inst_muldiv_pick_up = w_inst_is_muldiv;
assign w_inst_mem_pick_up    = w_inst_is_ld | w_inst_is_st;
assign w_inst_bru_pick_up    = w_inst_is_br;
assign w_inst_csu_pick_up    = w_inst_is_csu;
assign w_inst_fpu_pick_up    = w_inst_is_fpu;
assign w_inst_except_pick_up = w_inst_gen_except;
assign w_fetch_except_pick_up = w_fetch_except;
assign w_inst_illegal_pick_up = w_inst_illegal;

bit_pick_up #(.WIDTH(msrh_conf_pkg::DISP_SIZE), .NUM(msrh_conf_pkg::ARITH_DISP_SIZE))  u_arith_disp_pick_up  (.in(w_inst_arith_pick_up ),  .out(w_inst_arith_disp  ));
bit_pick_up #(.WIDTH(msrh_conf_pkg::DISP_SIZE), .NUM(msrh_conf_pkg::MULDIV_DISP_SIZE)) u_muldiv_disp_pick_up (.in(w_inst_muldiv_pick_up),  .out(w_inst_muldiv_disp ));
bit_pick_up #(.WIDTH(msrh_conf_pkg::DISP_SIZE), .NUM(msrh_conf_pkg::MEM_DISP_SIZE  ))  u_mem_disp_pick_up    (.in(w_inst_mem_pick_up   ),  .out(w_inst_mem_disp    ));
bit_pick_up #(.WIDTH(msrh_conf_pkg::DISP_SIZE), .NUM(msrh_conf_pkg::MEM_DISP_SIZE  ))  u_ld_disp_pick_up     (.in(w_inst_is_ld         ),  .out(w_inst_ld_disp     ));
bit_pick_up #(.WIDTH(msrh_conf_pkg::DISP_SIZE), .NUM(msrh_conf_pkg::MEM_DISP_SIZE  ))  u_st_disp_pick_up     (.in(w_inst_is_st         ),  .out(w_inst_st_disp     ));
bit_pick_up #(.WIDTH(msrh_conf_pkg::DISP_SIZE), .NUM(msrh_conf_pkg::BRU_DISP_SIZE  ))  u_bru_disp_pick_up    (.in(w_inst_bru_pick_up   ),  .out(w_inst_bru_disp    ));
bit_pick_up #(.WIDTH(msrh_conf_pkg::DISP_SIZE), .NUM(msrh_conf_pkg::CSU_DISP_SIZE  ))  u_csu_disp_pick_up    (.in(w_inst_csu_pick_up   ),  .out(w_inst_csu_disp    ));
bit_pick_up #(.WIDTH(msrh_conf_pkg::DISP_SIZE), .NUM(msrh_conf_pkg::FPU_DISP_SIZE  ))  u_fpu_disp_pick_up    (.in(w_inst_fpu_pick_up   ),  .out(w_inst_fpu_disp    ));
bit_pick_up #(.WIDTH(msrh_conf_pkg::DISP_SIZE), .NUM(1                             ))  u_illegal_disp_pick_up(.in(w_inst_illegal_pick_up), .out(w_inst_illegal_disp));
bit_pick_up #(.WIDTH(msrh_conf_pkg::DISP_SIZE), .NUM(1                             ))  u_except_disp_pick_up (.in(w_fetch_except_pick_up), .out(w_fetch_except_disp));

assign w_inst_disp_or = w_inst_arith_disp | w_inst_mem_disp | w_inst_bru_disp | w_inst_csu_disp | w_inst_fpu_disp | w_inst_illegal_disp | w_fetch_except_disp;

logic [msrh_conf_pkg::DISP_SIZE: 0] w_inst_disp_mask_tmp;
bit_extract_lsb #(.WIDTH(msrh_conf_pkg::DISP_SIZE + 1)) u_inst_msb (.in({1'b1, ~w_inst_disp_or}), .out(w_inst_disp_mask_tmp));
assign w_predict_taken_valid = |(w_inst_disp_mask & w_predict_taken_valid_array);

bit_extract_lsb #(.WIDTH(msrh_conf_pkg::DISP_SIZE)) u_predict_valid_lsb (.in(w_inst_disp_mask & w_predict_taken_valid_array), .out(w_predict_taken_valid_lsb));
bit_oh_or #(.T(logic[$clog2(msrh_pkg::INST_BUF_SIZE)-1:0] ), .WORDS(msrh_conf_pkg::DISP_SIZE)) u_inst_buf_pred_index (.i_oh(w_predict_taken_valid_lsb), .i_data(w_expand_pred_index), .o_selected(w_pred_lsb_index));

msrh_pkg::grp_id_t w_bru_predict_disp_valid;
msrh_pkg::grp_id_t w_disp_special_limit_valid;
msrh_pkg::grp_id_t w_disp_special_limit_valid_oh;

assign w_bru_predict_disp_valid = (w_inst_disp_mask_tmp - 1) & (w_inst_bru_disp | w_predict_taken_valid_array);

assign w_disp_special_limit_valid = w_bru_predict_disp_valid | (w_inst_csu_disp & (w_inst_disp_mask_tmp - 1));

bit_extract_lsb #(.WIDTH(msrh_conf_pkg::DISP_SIZE)) u_special_valid_lsb (.in(w_disp_special_limit_valid), .out(w_disp_special_limit_valid_oh));

msrh_pkg::grp_id_t w_disp_special_bru_valid;
msrh_pkg::grp_id_t w_disp_special_csu_valid;

assign w_disp_special_bru_valid = w_disp_special_limit_valid_oh & w_bru_predict_disp_valid;
assign w_disp_special_csu_valid = w_disp_special_limit_valid_oh & w_inst_csu_disp;

assign w_inst_disp_mask = |w_disp_special_bru_valid ? {w_disp_special_bru_valid, 1'b0} - 1 :
                          (w_disp_special_csu_valid == 'h1) ? 'h1 :
                          |w_disp_special_csu_valid ? w_inst_csu_disp - 1 :
                          w_inst_disp_mask_tmp - 1;

assign iq_disp.valid          = |w_inst_disp_mask & !w_flush_pipeline;
assign iq_disp.pc_addr        = r_inst_queue[r_inst_buffer_outptr].pc + r_head_start_pos;
assign iq_disp.is_br_included = |w_inst_bru_disped;
assign iq_disp.tlb_except_valid = w_fetch_except;
assign iq_disp.tlb_except_cause = w_fetch_except_cause;
assign iq_disp.tlb_except_tval  = w_fetch_except_tval;

// -------------------------------
// Dispatch Inst, Resource Count
// -------------------------------

bit_pick_up #(.WIDTH(msrh_conf_pkg::DISP_SIZE), .NUM(msrh_conf_pkg::ARITH_DISP_SIZE )) u_arith_disped_pick_up   (.in(w_inst_arith_disp   & w_inst_disp_mask), .out(w_inst_arith_disped  ));
bit_pick_up #(.WIDTH(msrh_conf_pkg::DISP_SIZE), .NUM(msrh_conf_pkg::MULDIV_DISP_SIZE)) u_muldiv_disped_pick_up  (.in(w_inst_muldiv_disp  & w_inst_disp_mask), .out(w_inst_muldiv_disped ));
bit_pick_up #(.WIDTH(msrh_conf_pkg::DISP_SIZE), .NUM(msrh_conf_pkg::MEM_DISP_SIZE   )) u_mem_disped_pick_up     (.in(w_inst_mem_disp     & w_inst_disp_mask), .out(w_inst_mem_disped    ));
bit_pick_up #(.WIDTH(msrh_conf_pkg::DISP_SIZE), .NUM(msrh_conf_pkg::MEM_DISP_SIZE   )) u_ld_disped_pick_up      (.in(w_inst_ld_disp      & w_inst_disp_mask), .out(w_inst_ld_disped     ));
bit_pick_up #(.WIDTH(msrh_conf_pkg::DISP_SIZE), .NUM(msrh_conf_pkg::MEM_DISP_SIZE   )) u_st_disped_pick_up      (.in(w_inst_st_disp      & w_inst_disp_mask), .out(w_inst_st_disped     ));
bit_pick_up #(.WIDTH(msrh_conf_pkg::DISP_SIZE), .NUM(msrh_conf_pkg::BRU_DISP_SIZE   )) u_bru_disped_pick_up     (.in(w_inst_bru_disp     & w_inst_disp_mask), .out(w_inst_bru_disped    ));
bit_pick_up #(.WIDTH(msrh_conf_pkg::DISP_SIZE), .NUM(msrh_conf_pkg::CSU_DISP_SIZE   )) u_csu_disped_pick_up     (.in(w_inst_csu_disp     & w_inst_disp_mask), .out(w_inst_csu_disped    ));
bit_pick_up #(.WIDTH(msrh_conf_pkg::DISP_SIZE), .NUM(msrh_conf_pkg::FPU_DISP_SIZE   )) u_fpu_disped_pick_up     (.in(w_inst_fpu_disp     & w_inst_disp_mask), .out(w_inst_fpu_disped    ));

logic [$clog2(msrh_conf_pkg::DISP_SIZE): 0] w_inst_muldiv_cnt;
logic [$clog2(msrh_conf_pkg::DISP_SIZE): 0] w_inst_mem_cnt;
logic [$clog2(msrh_conf_pkg::DISP_SIZE): 0] w_inst_ld_cnt;
logic [$clog2(msrh_conf_pkg::DISP_SIZE): 0] w_inst_st_cnt;
logic [$clog2(msrh_conf_pkg::DISP_SIZE): 0] w_inst_bru_cnt;
logic [$clog2(msrh_conf_pkg::DISP_SIZE): 0] w_inst_csu_cnt;
logic [$clog2(msrh_conf_pkg::DISP_SIZE): 0] w_inst_fpu_cnt;

generate for (genvar a_idx = 0; a_idx < msrh_conf_pkg::ALU_INST_NUM; a_idx++) begin : alu_rsrc_loop
  localparam alu_lane_width = msrh_conf_pkg::ARITH_DISP_SIZE / msrh_conf_pkg::ALU_INST_NUM;
  logic [msrh_conf_pkg::DISP_SIZE-1: 0] w_lane_disped_valid[alu_lane_width];
  logic [msrh_conf_pkg::DISP_SIZE-1: 0] w_lane_disped_valid_or;
  logic [$clog2(alu_lane_width+1): 0] w_lane_disp_cnt;
  for (genvar i = 0; i < alu_lane_width; i++) begin: cnt_loop
    bit_pick_1_pos #(.NUM(i * msrh_conf_pkg::ALU_INST_NUM + a_idx), .SEL_WIDTH(msrh_conf_pkg::DISP_SIZE)) bit_pos (.i_valids(w_inst_arith_disped), .o_picked_pos(w_lane_disped_valid[i]));
  end
  bit_or #(.WIDTH(msrh_conf_pkg::DISP_SIZE), .WORDS(alu_lane_width)) alu_disped_or (.i_data(w_lane_disped_valid), .o_selected(w_lane_disped_valid_or));
  bit_cnt #(.WIDTH(msrh_conf_pkg::DISP_SIZE)) u_alu_inst_cnt (.in(w_lane_disped_valid_or), .out(w_lane_disp_cnt));
  assign iq_disp.resource_cnt.alu_inst_cnt  [a_idx] = w_lane_disp_cnt;
  assign iq_disp.resource_cnt.alu_inst_valid[a_idx] = w_lane_disped_valid_or;
end
endgenerate

bit_cnt #(.WIDTH(msrh_conf_pkg::DISP_SIZE)) u_muldiv_inst_cnt (.in(w_inst_muldiv_disped), .out(w_inst_muldiv_cnt));
assign iq_disp.resource_cnt.muldiv_inst_cnt = w_inst_muldiv_cnt;

bit_cnt #(.WIDTH(msrh_conf_pkg::DISP_SIZE)) u_mem_inst_cnt (.in(w_inst_mem_disped), .out(w_inst_mem_cnt));
bit_cnt #(.WIDTH(msrh_conf_pkg::DISP_SIZE)) u_ld_inst_cnt  (.in(w_inst_ld_disped), .out(w_inst_ld_cnt));
bit_cnt #(.WIDTH(msrh_conf_pkg::DISP_SIZE)) u_st_inst_cnt  (.in(w_inst_st_disped), .out(w_inst_st_cnt));
assign iq_disp.resource_cnt.lsu_inst_valid = w_inst_mem_disped;

generate for (genvar l_idx = 0; l_idx < msrh_conf_pkg::LSU_INST_NUM; l_idx++) begin : lsu_rsrc_loop
  logic [$clog2(msrh_conf_pkg::MEM_DISP_SIZE): 0]  lsu_lane_width;
  assign lsu_lane_width = msrh_conf_pkg::MEM_DISP_SIZE / msrh_conf_pkg::LSU_INST_NUM;
  assign iq_disp.resource_cnt.lsu_inst_cnt[l_idx] = (w_inst_mem_cnt >= lsu_lane_width * (l_idx+1)) ? lsu_lane_width :
                                                    /* verilator lint_off UNSIGNED */
                                                    (w_inst_mem_cnt <  lsu_lane_width * l_idx) ? 'h0 :
                                                    w_inst_mem_cnt - lsu_lane_width * l_idx;
end
endgenerate

assign iq_disp.resource_cnt.ld_inst_cnt = w_inst_ld_cnt;
assign iq_disp.resource_cnt.st_inst_cnt = w_inst_st_cnt;

bit_cnt #(.WIDTH(msrh_conf_pkg::DISP_SIZE)) u_bru_inst_cnt (.in(w_inst_bru_disped), .out(w_inst_bru_cnt));
assign iq_disp.resource_cnt.bru_inst_cnt   = w_inst_bru_cnt;
assign iq_disp.resource_cnt.bru_inst_valid = w_inst_bru_disped;

bit_cnt #(.WIDTH(msrh_conf_pkg::DISP_SIZE)) u_csu_inst_cnt (.in(w_inst_csu_disped), .out(w_inst_csu_cnt));
assign iq_disp.resource_cnt.csu_inst_cnt   = w_inst_csu_cnt;
assign iq_disp.resource_cnt.csu_inst_valid = w_inst_csu_disped;

bit_cnt #(.WIDTH(msrh_conf_pkg::DISP_SIZE)) u_fpu_inst_cnt (.in(w_inst_fpu_disped), .out(w_inst_fpu_cnt));
generate for (genvar f_idx = 0; f_idx < msrh_conf_pkg::FPU_INST_NUM; f_idx++) begin : fpu_rsrc_loop
  localparam fpu_lane_width = msrh_conf_pkg::FPU_DISP_SIZE / msrh_conf_pkg::FPU_INST_NUM;
  logic [msrh_conf_pkg::DISP_SIZE-1: 0] w_lane_disped_valid[fpu_lane_width];
  logic [msrh_conf_pkg::DISP_SIZE-1: 0] w_lane_disped_valid_or;
  logic [$clog2(fpu_lane_width+1): 0] w_lane_disp_cnt;
  for (genvar i = 0; i < fpu_lane_width; i++) begin: cnt_loop
    bit_pick_1_pos #(.NUM(i*msrh_conf_pkg::FPU_INST_NUM + f_idx), .SEL_WIDTH(msrh_conf_pkg::DISP_SIZE)) bit_pos (.i_valids(w_inst_fpu_disped), .o_picked_pos(w_lane_disped_valid[i]));
  end
  bit_or #(.WIDTH(msrh_conf_pkg::DISP_SIZE), .WORDS(fpu_lane_width)) fpu_disped_or (.i_data(w_lane_disped_valid), .o_selected(w_lane_disped_valid_or));
  bit_cnt #(.WIDTH(msrh_conf_pkg::DISP_SIZE)) u_fpu_inst_cnt (.in(w_lane_disped_valid_or), .out(w_lane_disp_cnt));
  assign iq_disp.resource_cnt.fpu_inst_cnt[f_idx] = w_lane_disp_cnt;
  assign iq_disp.resource_cnt.fpu_inst_valid[f_idx] = w_lane_disped_valid_or;
end
endgenerate

generate for (genvar d_idx = 0; d_idx < msrh_conf_pkg::DISP_SIZE; d_idx++) begin : disp_loop
  always_comb begin
    if (w_inst_disp_mask[d_idx]) begin
      iq_disp.inst[d_idx].valid = w_inst_disp_mask[d_idx];
      iq_disp.inst[d_idx].illegal_valid = w_inst_illegal_disp[d_idx];
      iq_disp.inst[d_idx].inst = w_expand_inst[d_idx];
      iq_disp.inst[d_idx].rvc_inst_valid = w_rvc_valid[d_idx];
      iq_disp.inst[d_idx].rvc_inst       = w_rvc_inst [d_idx];
      iq_disp.inst[d_idx].pc_addr = {r_inst_queue[r_inst_buffer_outptr].pc[riscv_pkg::VADDR_W-1:$clog2(msrh_lsu_pkg::DCACHE_DATA_B_W)], {$clog2(msrh_lsu_pkg::DCACHE_DATA_B_W){1'b0}}} +
                                    {w_rvc_buf_idx_with_offset[d_idx], 1'b0};

      iq_disp.inst[d_idx].wr_reg.valid   = rd_field_type[d_idx] != RD__;
      iq_disp.inst[d_idx].wr_reg.typ     = rd_field_type[d_idx] == RD_R3 ? msrh_pkg::GPR : msrh_pkg::FPR;
      iq_disp.inst[d_idx].wr_reg.regidx  = w_expand_inst[d_idx][11: 7];

      iq_disp.inst[d_idx].rd_regs[0].valid  = rs1_field_type[d_idx] != R1__;
      iq_disp.inst[d_idx].rd_regs[0].typ    = rs1_field_type[d_idx] == R1_R1 ? msrh_pkg::GPR : msrh_pkg::FPR;
      iq_disp.inst[d_idx].rd_regs[0].regidx = w_expand_inst[d_idx][19:15];

      iq_disp.inst[d_idx].rd_regs[1].valid  = rs2_field_type[d_idx] != R2__;
      iq_disp.inst[d_idx].rd_regs[1].typ    = rs2_field_type[d_idx] == R2_R2 ? msrh_pkg::GPR : msrh_pkg::FPR;
      iq_disp.inst[d_idx].rd_regs[1].regidx = w_expand_inst[d_idx][24:20];

      iq_disp.inst[d_idx].rd_regs[2].valid  = rs3_field_type[d_idx] != R3__;
      iq_disp.inst[d_idx].rd_regs[2].typ    = msrh_pkg::FPR;
      iq_disp.inst[d_idx].rd_regs[2].regidx = w_expand_inst[d_idx][31:27];

      iq_disp.inst[d_idx].cat        = w_inst_cat[d_idx];

      iq_disp.inst[d_idx].pred_taken        = w_predict_taken_valid_lsb[d_idx];
      iq_disp.inst[d_idx].bim_value         = w_expand_pred_info[d_idx].bim_value;
      iq_disp.inst[d_idx].btb_valid         = w_expand_pred_info[d_idx].btb_valid;
      iq_disp.inst[d_idx].pred_target_vaddr = (w_inst_is_ret [d_idx] & w_expand_ras_info[d_idx].is_ret |
                                               w_inst_is_call[d_idx] & w_expand_ras_info[d_idx].is_call) ? w_expand_ras_info[d_idx].pred_target_vaddr :
                                              w_expand_pred_info[d_idx].pred_target_vaddr;

      iq_disp.inst[d_idx].is_call           = w_inst_is_call[d_idx];
      iq_disp.inst[d_idx].is_ret            = w_inst_is_ret [d_idx];
      iq_disp.inst[d_idx].ras_index         = w_expand_ras_info[d_idx].ras_index;
    end else begin // if (w_inst_disp_mask[d_idx])
      iq_disp.inst[d_idx] = 'h0;
    end // else: !if(w_inst_disp_mask[d_idx])
  end // always_comb
end
endgenerate

`ifdef SIMULATION
function void dump_json(int fp);
  $fwrite(fp, "  \"msrh_inst_buffer\" : {\n");

  for(int idx=0; idx < msrh_pkg::INST_BUF_SIZE; idx++) begin
    if (r_inst_queue[idx].valid) begin
      $fwrite(fp, "    \"r_inst_queue[%d]\" : {\n", idx);
      $fwrite(fp, "      valid     : \"%d\",\n", r_inst_queue[idx].valid);
      $fwrite(fp, "      data    : \"0x%x\",\n", r_inst_queue[idx].data);
      $fwrite(fp, "      pc      : \"0x%x\",\n", r_inst_queue[idx].pc << 1);
      $fwrite(fp, "      byte_en : \"0x%x\",\n", r_inst_queue[idx].byte_en);
      $fwrite(fp, "    },\n");
    end
  end

  for (int d_idx = 0; d_idx < msrh_conf_pkg::DISP_SIZE; d_idx++) begin : disp_loop
    if (iq_disp.inst[d_idx].valid) begin
      $fwrite(fp, "    \"iq_disp.inst[%d]\" : {", d_idx);
      $fwrite(fp, "      valid : %d,",      iq_disp.inst[d_idx].valid);
      $fwrite(fp, "      inst  : \"0x%08x\",",      iq_disp.inst[d_idx].inst);
      $fwrite(fp, "      pc_addr : \"0x%0x\",",    iq_disp.inst[d_idx].pc_addr);

      $fwrite(fp, "      rd_valid   : %d,", iq_disp.inst[d_idx].wr_reg.valid);
      $fwrite(fp, "      rd_type    : \"%d\",", iq_disp.inst[d_idx].wr_reg.typ);
      $fwrite(fp, "      rd_regidx  : %d,", iq_disp.inst[d_idx].wr_reg.regidx);

      $fwrite(fp, "      rs1_valid  : %d,", iq_disp.inst[d_idx].rd_regs[0].valid);
      $fwrite(fp, "      rs1_type   : \"%d\",", iq_disp.inst[d_idx].rd_regs[0].typ);
      $fwrite(fp, "      rs1_regidx : %d,", iq_disp.inst[d_idx].rd_regs[0].regidx);

      $fwrite(fp, "      rs2_valid  : %d,", iq_disp.inst[d_idx].rd_regs[1].valid);
      $fwrite(fp, "      rs2_type   : \"%d\",", iq_disp.inst[d_idx].rd_regs[1].typ);
      $fwrite(fp, "      rs2_regidx : %d,", iq_disp.inst[d_idx].rd_regs[1].regidx);

      $fwrite(fp, "      \"cat[d_idx]\" : \"%d\",", iq_disp.inst[d_idx].cat);
      $fwrite(fp, "    },\n");
    end
  end

  $fwrite(fp, "  },\n");
endfunction // dump

logic [63: 0] r_cycle_count;
logic [63: 0] r_ibuf_max_period;
logic [63: 0] r_ibuf_entry_count;

always_ff @ (negedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_ibuf_max_period  <= 'h0;
    r_ibuf_entry_count <= 'h0;
    r_cycle_count  <= 'h0;
  end else begin
    r_cycle_count <= r_cycle_count + 'h1;
    if (r_cycle_count % sim_pkg::COUNT_UNIT == sim_pkg::COUNT_UNIT-1) begin
      r_ibuf_max_period  <= 'h0;
      r_ibuf_entry_count <= 'h0;
    end else begin
      if (|w_inst_buffer_valid) begin
        if (&w_inst_buffer_valid) begin
          r_ibuf_max_period  <= r_ibuf_max_period + 'h1;
        end
        r_ibuf_entry_count <= r_ibuf_entry_count + $countones(w_inst_buffer_valid);
      end
    end // else: !if(r_cycle_count % sim_pkg::COUNT_UNIT == sim_pkg::COUNT_UNIT-1)
  end // else: !if(!i_reset_n)
end // always_ff @ (negedge i_clk, negedge i_reset_n)

function void dump_perf (int fp);
  $fwrite(fp, "  \"inst_buffer\" : {");
  $fwrite(fp, "  \"max_period\" : %5d, ", r_ibuf_max_period);
  $fwrite(fp, "  \"average count\" : %5f},\n", r_ibuf_entry_count / 1000.0);
endfunction // dump_perf

`endif // SIMULATION


endmodule // inst_buffer
