module msrh_inst_buffer
  import decoder_reg_pkg::*;
  (
 input logic                                     i_clk,
 input logic                                     i_reset_n,
 input logic                                     i_flush_valid,

 input logic                                     i_inst_valid,

 // PC Update from Committer
 input msrh_pkg::commit_blk_t                    i_commit,

 output logic                                    o_inst_ready,
 input logic [riscv_pkg::VADDR_W-1: 1]           i_inst_pc,
 input logic [msrh_conf_pkg::ICACHE_DATA_W-1: 0] i_inst_in,
 input logic [msrh_lsu_pkg::ICACHE_DATA_B_W-1:0] i_inst_byte_en,
 input logic                                     i_inst_tlb_except_valid,
 input msrh_pkg::except_t                        i_inst_tlb_except_cause,

 disp_if.master                                  iq_disp
 );

logic                                       w_inst_buffer_fire;

logic [msrh_conf_pkg::DISP_SIZE-1:0] w_inst_arith_pick_up;
logic [msrh_conf_pkg::DISP_SIZE-1:0] w_inst_mem_pick_up;
logic [msrh_conf_pkg::DISP_SIZE-1:0] w_inst_bru_pick_up;
logic [msrh_conf_pkg::DISP_SIZE-1:0] w_inst_csu_pick_up;
logic [msrh_conf_pkg::DISP_SIZE-1:0] w_inst_except_pick_up;
logic [msrh_conf_pkg::DISP_SIZE-1:0] w_inst_illegal_pick_up;

logic [msrh_conf_pkg::DISP_SIZE-1:0] w_inst_arith_disp;
logic [msrh_conf_pkg::DISP_SIZE-1:0] w_inst_mem_disp;
logic [msrh_conf_pkg::DISP_SIZE-1:0] w_inst_ld_disp;
logic [msrh_conf_pkg::DISP_SIZE-1:0] w_inst_st_disp;
logic [msrh_conf_pkg::DISP_SIZE-1:0] w_inst_bru_disp;
logic [msrh_conf_pkg::DISP_SIZE-1:0] w_inst_csu_disp;
logic [msrh_conf_pkg::DISP_SIZE-1:0] w_inst_except_disp;
logic [msrh_conf_pkg::DISP_SIZE-1:0] w_inst_illegal_disp;

logic [msrh_conf_pkg::DISP_SIZE-1:0] w_inst_disp_or;
logic [msrh_conf_pkg::DISP_SIZE-1:0] w_inst_disp_mask;

localparam ic_word_num = msrh_lsu_pkg::ICACHE_DATA_B_W / 4;
decoder_inst_cat_pkg::inst_cat_t w_inst_cat[msrh_conf_pkg::DISP_SIZE];
logic [msrh_conf_pkg::DISP_SIZE-1:0] w_inst_gen_except;
logic [msrh_conf_pkg::DISP_SIZE-1:0] w_inst_illegal;
logic [msrh_conf_pkg::DISP_SIZE-1:0] w_inst_is_arith;
logic [msrh_conf_pkg::DISP_SIZE-1:0] w_inst_is_ld;
logic [msrh_conf_pkg::DISP_SIZE-1:0] w_inst_is_st;
logic [msrh_conf_pkg::DISP_SIZE-1:0] w_inst_is_br;
logic [msrh_conf_pkg::DISP_SIZE-1:0] w_inst_is_csu;

logic [msrh_conf_pkg::DISP_SIZE-1:0] w_inst_gen_except_lsb;

rd_t rd_field_type [msrh_conf_pkg::DISP_SIZE];
r1_t rs1_field_type[msrh_conf_pkg::DISP_SIZE];
r2_t rs2_field_type[msrh_conf_pkg::DISP_SIZE];

logic [ic_word_num-1:0] r_head_inst_issued;
logic [ic_word_num*2-1:0] w_head_inst_issued_next;
logic [$clog2(ic_word_num)-1:0] r_head_start_pos;
logic [$clog2(ic_word_num):0]   w_head_start_pos_next;
logic                           w_head_all_inst_issued;

typedef struct packed {
  logic                                      valid;
  logic [riscv_pkg::VADDR_W-1: 1]            pc;
  logic [msrh_conf_pkg::ICACHE_DATA_W-1: 0]  data;
  logic [msrh_lsu_pkg::ICACHE_DATA_B_W-1: 0] byte_en;
  logic                                      tlb_except_valid;
  msrh_pkg::except_t                         tlb_except_cause;
`ifdef SIMULATION
  logic [riscv_pkg::VADDR_W-1: 0]            pc_dbg;
`endif // SIMULATION
} inst_buf_t;

inst_buf_t r_inst_queue[msrh_pkg::INST_BUF_SIZE];
logic [msrh_pkg::INST_BUF_SIZE-1:0]      w_inst_buffer_valid;

logic [$clog2(msrh_pkg::INST_BUF_SIZE)-1:0] r_inst_buffer_inptr;
logic [$clog2(msrh_pkg::INST_BUF_SIZE)-1:0] r_inst_buffer_outptr;
logic [$clog2(msrh_pkg::INST_BUF_SIZE)-1:0] w_inst_buffer_outptr_p1;
logic                                       w_ptr_in_fire;
logic                                       w_ptr_out_fire;

logic [$clog2(ic_word_num)+2-1:2]           w_out_inst_q_pc;

logic                                       w_flush_pipeline;

assign w_head_all_inst_issued = w_inst_buffer_fire & (&w_head_inst_issued_next[ic_word_num-1:0]);

assign w_ptr_in_fire  = i_inst_valid & o_inst_ready;
assign w_ptr_out_fire = w_head_all_inst_issued;

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
   .o_in_ptr  (r_inst_buffer_inptr),
   .i_out_valid (w_ptr_out_fire),
   .o_out_ptr (r_inst_buffer_outptr)
   );

assign w_inst_buffer_outptr_p1 = r_inst_buffer_outptr + 'h1;

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
        r_inst_queue[idx].data    <= i_inst_in;
        r_inst_queue[idx].pc      <= i_inst_pc;
        r_inst_queue[idx].byte_en <= i_inst_byte_en;
        r_inst_queue[idx].tlb_except_valid <= i_inst_tlb_except_valid;
        r_inst_queue[idx].tlb_except_cause <= i_inst_tlb_except_cause;
`ifdef SIMULATION
        r_inst_queue[idx].pc_dbg   <= {i_inst_pc, 1'b0};
`endif // SIMULATION
      end else if (w_head_all_inst_issued & (r_inst_buffer_outptr == idx)) begin
        r_inst_queue[idx].valid  <= 1'b0;
      end // if (i_inst_valid & o_inst_ready)
    end // else: !if(!i_reset_n)
  end // always_ff @ (posedge i_clk, negedge i_reset_n)

end // block: inst_buf_loop
endgenerate


assign o_inst_ready = !(&w_inst_buffer_valid);

encoder
  #(.SIZE(ic_word_num + 1))
u_start_pos_enc
  (
   .i_in({{(ic_word_num - msrh_conf_pkg::DISP_SIZE){1'b0}}, {w_inst_disp_mask, w_inst_disp_mask[0]} ^ {1'b0, w_inst_disp_mask}}),
   .o_out(w_head_start_pos_next)
   );

logic [ic_word_num-1: 0] w_head_start_pos_upper_next;
logic [$clog2(ic_word_num):0]   w_head_start_upper_next;

assign w_head_start_pos_upper_next = w_head_inst_issued_next[ic_word_num +: ic_word_num];

encoder
  #(.SIZE(ic_word_num + 1))
u_start_pos_next_uppper_enc
  (
   .i_in({w_head_start_pos_upper_next, w_head_start_pos_upper_next[0]} ^ {1'b0, w_head_start_pos_upper_next}),
   .o_out(w_head_start_upper_next)
   );

assign w_out_inst_q_pc = r_inst_queue[r_inst_buffer_outptr].pc[2+:$clog2(ic_word_num)];

/* verilator lint_off WIDTH */
assign w_head_inst_issued_next = r_head_inst_issued |
                                 w_inst_disp_mask << (r_head_start_pos + w_out_inst_q_pc) |
                                 (1 << w_out_inst_q_pc)-1;

always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_head_inst_issued <= {ic_word_num{1'b0}};
    r_head_start_pos   <= 'h0;
  end else begin
    if (w_flush_pipeline) begin
      r_head_inst_issued <= 'h0;
      r_head_start_pos   <= 'h0;
    end else if (w_inst_buffer_fire) begin
      if (&w_head_inst_issued_next[ic_word_num-1:0]) begin
        r_head_inst_issued <= w_head_inst_issued_next[ic_word_num +: ic_word_num];
        r_head_start_pos   <= w_head_start_upper_next;
      end else begin
        r_head_inst_issued <= w_head_inst_issued_next;
        r_head_start_pos   <= r_head_start_pos + w_head_start_pos_next[$clog2(ic_word_num)-1:0];
      end
    end
  end
end

logic [31: 0] w_inst[msrh_conf_pkg::DISP_SIZE];
logic [msrh_conf_pkg::DISP_SIZE-1:0] w_inst_be_valid;

generate for (genvar w_idx = 0; w_idx < msrh_conf_pkg::DISP_SIZE; w_idx++) begin : word_loop
  logic [$clog2(ic_word_num): 0] w_buf_id;
  logic [$clog2(msrh_pkg::INST_BUF_SIZE)-1: 0] w_inst_buf_ptr;

  assign w_buf_id = r_head_start_pos + w_idx +
                    w_out_inst_q_pc;
  assign w_inst_buf_ptr = (w_buf_id < ic_word_num) ? r_inst_buffer_outptr :
                          w_inst_buffer_outptr_p1;
  assign w_inst         [w_idx] =   r_inst_queue[w_inst_buf_ptr].data[w_buf_id[$clog2(ic_word_num)-1:0]*32+:32];
  assign w_inst_be_valid[w_idx] = |(r_inst_queue[w_inst_buf_ptr].byte_en[w_buf_id[$clog2(ic_word_num)-1:0]*4+:4]);

  logic[ 2: 0] w_raw_cat;
  logic        w_raw_gen_except;
  decoder_inst_cat
  u_decoder_inst_cat
    (
     .inst(w_inst[w_idx]),
     .inst_cat(w_raw_cat),
     .gen_except(w_raw_gen_except)
     );
  assign w_inst_cat[w_idx] = decoder_inst_cat_pkg::inst_cat_t'(w_raw_cat);

  decoder_reg
  u_decoder_reg
    (
     .inst(w_inst[w_idx]),
     .rd(rd_field_type [w_idx]),
     .r1(rs1_field_type[w_idx]),
     .r2(rs2_field_type[w_idx])
     );


  assign w_inst_is_arith[w_idx] = r_inst_queue[w_inst_buf_ptr].valid & w_inst_be_valid[w_idx] & (w_inst_cat[w_idx] == decoder_inst_cat_pkg::INST_CAT_ARITH);
  assign w_inst_is_ld   [w_idx] = r_inst_queue[w_inst_buf_ptr].valid & w_inst_be_valid[w_idx] & (w_inst_cat[w_idx] == decoder_inst_cat_pkg::INST_CAT_LD  );
  assign w_inst_is_st   [w_idx] = r_inst_queue[w_inst_buf_ptr].valid & w_inst_be_valid[w_idx] & (w_inst_cat[w_idx] == decoder_inst_cat_pkg::INST_CAT_ST  );
  assign w_inst_is_br   [w_idx] = r_inst_queue[w_inst_buf_ptr].valid & w_inst_be_valid[w_idx] & (w_inst_cat[w_idx] == decoder_inst_cat_pkg::INST_CAT_BR  );
  assign w_inst_is_csu  [w_idx] = r_inst_queue[w_inst_buf_ptr].valid & w_inst_be_valid[w_idx] & (w_inst_cat[w_idx] == decoder_inst_cat_pkg::INST_CAT_CSU );

  assign w_inst_illegal[w_idx]    = r_inst_queue[w_inst_buf_ptr].valid & w_inst_be_valid[w_idx] & r_inst_queue[w_inst_buf_ptr].tlb_except_valid;
  assign w_inst_gen_except[w_idx] = r_inst_queue[w_inst_buf_ptr].valid & w_inst_be_valid[w_idx] & w_raw_gen_except;
end
endgenerate

assign w_inst_arith_pick_up  = w_inst_is_arith;
assign w_inst_mem_pick_up    = w_inst_is_ld | w_inst_is_st;
assign w_inst_bru_pick_up    = w_inst_is_br;
assign w_inst_csu_pick_up    = w_inst_is_csu;
assign w_inst_except_pick_up = w_inst_gen_except;
assign w_inst_illegal_pick_up = w_inst_illegal;

bit_pick_up #(.WIDTH(msrh_conf_pkg::DISP_SIZE), .NUM(msrh_conf_pkg::ARITH_DISP_SIZE)) u_arith_disp_pick_up  (.in(w_inst_arith_pick_up ),  .out(w_inst_arith_disp  ));
bit_pick_up #(.WIDTH(msrh_conf_pkg::DISP_SIZE), .NUM(msrh_conf_pkg::MEM_DISP_SIZE  )) u_mem_disp_pick_up    (.in(w_inst_mem_pick_up   ),  .out(w_inst_mem_disp    ));
bit_pick_up #(.WIDTH(msrh_conf_pkg::DISP_SIZE), .NUM(msrh_conf_pkg::MEM_DISP_SIZE  )) u_ld_disp_pick_up     (.in(w_inst_is_ld         ),  .out(w_inst_ld_disp     ));
bit_pick_up #(.WIDTH(msrh_conf_pkg::DISP_SIZE), .NUM(msrh_conf_pkg::MEM_DISP_SIZE  )) u_st_disp_pick_up     (.in(w_inst_is_st         ),  .out(w_inst_st_disp     ));
bit_pick_up #(.WIDTH(msrh_conf_pkg::DISP_SIZE), .NUM(msrh_conf_pkg::BRU_DISP_SIZE  )) u_bru_disp_pick_up    (.in(w_inst_bru_pick_up   ),  .out(w_inst_bru_disp    ));
bit_pick_up #(.WIDTH(msrh_conf_pkg::DISP_SIZE), .NUM(msrh_conf_pkg::CSU_DISP_SIZE  )) u_csu_disp_pick_up    (.in(w_inst_csu_pick_up   ),  .out(w_inst_csu_disp    ));
// bit_pick_up #(.WIDTH(msrh_conf_pkg::DISP_SIZE), .NUM(msrh_conf_pkg::CSU_DISP_SIZE  )) u_except_disp_pick_up (.in(w_inst_except_pick_up),  .out(w_inst_except_disp ));
bit_pick_up #(.WIDTH(msrh_conf_pkg::DISP_SIZE), .NUM(1                             )) u_illegal_disp_pick_up(.in(w_inst_illegal_pick_up), .out(w_inst_illegal_disp));

assign w_inst_disp_or = w_inst_arith_disp | w_inst_mem_disp | w_inst_bru_disp | w_inst_csu_disp | /* w_inst_except_disp | */w_inst_illegal_disp;

logic [msrh_conf_pkg::DISP_SIZE: 0] w_inst_disp_mask_tmp;
bit_extract_lsb #(.WIDTH(msrh_conf_pkg::DISP_SIZE + 1)) u_inst_msb (.in({1'b0, ~w_inst_disp_or}), .out(w_inst_disp_mask_tmp));
assign w_inst_disp_mask = w_inst_disp_mask_tmp - 1;

assign iq_disp.valid          = |w_inst_disp_mask & !w_flush_pipeline;
assign iq_disp.pc_addr        = r_inst_queue[r_inst_buffer_outptr].pc + {r_head_start_pos, 1'b0};
assign iq_disp.is_br_included = (|w_inst_is_br) | (|w_inst_gen_except);
assign iq_disp.tlb_except_valid = r_inst_queue[r_inst_buffer_outptr].tlb_except_valid;
assign iq_disp.tlb_except_cause = r_inst_queue[r_inst_buffer_outptr].tlb_except_cause;


// -------------------------------
// Dispatch Inst, Resource Count
// -------------------------------
logic [msrh_conf_pkg::DISP_SIZE-1:0] w_inst_arith_disped;
logic [msrh_conf_pkg::DISP_SIZE-1:0] w_inst_mem_disped;
logic [msrh_conf_pkg::DISP_SIZE-1:0] w_inst_ld_disped;
logic [msrh_conf_pkg::DISP_SIZE-1:0] w_inst_st_disped;
logic [msrh_conf_pkg::DISP_SIZE-1:0] w_inst_bru_disped;
logic [msrh_conf_pkg::DISP_SIZE-1:0] w_inst_csu_disped;
bit_pick_up #(.WIDTH(msrh_conf_pkg::DISP_SIZE), .NUM(msrh_conf_pkg::ARITH_DISP_SIZE)) u_arith_disped_pick_up (.in(w_inst_arith_disp & w_inst_disp_mask), .out(w_inst_arith_disped));
bit_pick_up #(.WIDTH(msrh_conf_pkg::DISP_SIZE), .NUM(msrh_conf_pkg::MEM_DISP_SIZE  )) u_mem_disped_pick_up   (.in(w_inst_mem_disp   & w_inst_disp_mask), .out(w_inst_mem_disped  ));
bit_pick_up #(.WIDTH(msrh_conf_pkg::DISP_SIZE), .NUM(msrh_conf_pkg::MEM_DISP_SIZE  )) u_ld_disped_pick_up    (.in(w_inst_ld_disp    & w_inst_disp_mask), .out(w_inst_ld_disped   ));
bit_pick_up #(.WIDTH(msrh_conf_pkg::DISP_SIZE), .NUM(msrh_conf_pkg::MEM_DISP_SIZE  )) u_st_disped_pick_up    (.in(w_inst_st_disp    & w_inst_disp_mask), .out(w_inst_st_disped   ));
bit_pick_up #(.WIDTH(msrh_conf_pkg::DISP_SIZE), .NUM(msrh_conf_pkg::BRU_DISP_SIZE  )) u_bru_disped_pick_up   (.in(w_inst_bru_disp   & w_inst_disp_mask), .out(w_inst_bru_disped  ));
bit_pick_up #(.WIDTH(msrh_conf_pkg::DISP_SIZE), .NUM(msrh_conf_pkg::CSU_DISP_SIZE  )) u_csu_disped_pick_up   (.in(w_inst_csu_disp   & w_inst_disp_mask), .out(w_inst_csu_disped  ));

logic [$clog2(msrh_conf_pkg::ARITH_DISP_SIZE): 0] w_inst_arith_cnt;
logic [$clog2(msrh_conf_pkg::MEM_DISP_SIZE): 0]   w_inst_mem_cnt;
logic [$clog2(msrh_conf_pkg::MEM_DISP_SIZE): 0]   w_inst_ld_cnt;
logic [$clog2(msrh_conf_pkg::MEM_DISP_SIZE): 0]   w_inst_st_cnt;
logic [$clog2(msrh_conf_pkg::BRU_DISP_SIZE): 0]   w_inst_bru_cnt;
logic [$clog2(msrh_conf_pkg::CSU_DISP_SIZE): 0]   w_inst_csu_cnt;

bit_cnt #(.WIDTH(msrh_conf_pkg::DISP_SIZE)) u_alu_inst_cnt (.in(w_inst_arith_disped), .out(w_inst_arith_cnt));
generate for (genvar a_idx = 0; a_idx < msrh_conf_pkg::ALU_INST_NUM; a_idx++) begin : alu_rsrc_loop
  logic [$clog2(msrh_conf_pkg::ARITH_DISP_SIZE): 0]  alu_lane_width;
  assign alu_lane_width = msrh_conf_pkg::ARITH_DISP_SIZE / msrh_conf_pkg::ALU_INST_NUM;
  assign iq_disp.resource_cnt.alu_inst_cnt[a_idx] = (w_inst_arith_cnt >= alu_lane_width * (a_idx+1)) ? alu_lane_width :
                                                    /* verilator lint_off UNSIGNED */
                                                    (w_inst_arith_cnt <  alu_lane_width * a_idx) ? 'h0 :
                                                    w_inst_arith_cnt - alu_lane_width * a_idx;
end
endgenerate

bit_cnt #(.WIDTH(msrh_conf_pkg::DISP_SIZE)) u_mem_inst_cnt (.in(w_inst_mem_disped), .out(w_inst_mem_cnt));
bit_cnt #(.WIDTH(msrh_conf_pkg::DISP_SIZE)) u_ld_inst_cnt  (.in(w_inst_ld_disped), .out(w_inst_ld_cnt));
bit_cnt #(.WIDTH(msrh_conf_pkg::DISP_SIZE)) u_st_inst_cnt  (.in(w_inst_st_disped), .out(w_inst_st_cnt));

generate for (genvar l_idx = 0; l_idx < msrh_conf_pkg::LSU_INST_NUM; l_idx++) begin : lsu_rsrc_loop
  logic [$clog2(msrh_conf_pkg::ARITH_DISP_SIZE): 0]  lsu_lane_width;
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
assign iq_disp.resource_cnt.bru_inst_cnt = w_inst_bru_cnt;
bit_cnt #(.WIDTH(msrh_conf_pkg::DISP_SIZE)) u_csu_inst_cnt (.in(w_inst_csu_disped), .out(w_inst_csu_cnt));
assign iq_disp.resource_cnt.csu_inst_cnt = w_inst_csu_cnt;

generate for (genvar d_idx = 0; d_idx < msrh_conf_pkg::DISP_SIZE; d_idx++) begin : disp_loop
  always_comb begin
    if (w_inst_disp_mask[d_idx]) begin
      iq_disp.inst[d_idx].valid = w_inst_disp_mask[d_idx];
      iq_disp.inst[d_idx].inst  = w_inst[d_idx];
      iq_disp.inst[d_idx].pc_addr = {r_inst_queue[r_inst_buffer_outptr].pc, 1'b0} + ((r_head_start_pos + d_idx) << 2);

      iq_disp.inst[d_idx].rd_valid   = rd_field_type[d_idx] != RD__;
      iq_disp.inst[d_idx].rd_type    = msrh_pkg::GPR;
      iq_disp.inst[d_idx].rd_regidx  = w_inst[d_idx][11: 7];

      iq_disp.inst[d_idx].rs1_valid  = rs1_field_type[d_idx] != R1__;
      iq_disp.inst[d_idx].rs1_type   = msrh_pkg::GPR;
      iq_disp.inst[d_idx].rs1_regidx = w_inst[d_idx][19:15];

      iq_disp.inst[d_idx].rs2_valid  = rs2_field_type[d_idx] != R2__;
      iq_disp.inst[d_idx].rs2_type   = msrh_pkg::GPR;
      iq_disp.inst[d_idx].rs2_regidx = w_inst[d_idx][24:20];

      iq_disp.inst[d_idx].cat        = w_inst_cat[d_idx];
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

      $fwrite(fp, "      rd_valid   : %d,", iq_disp.inst[d_idx].rd_valid);
      $fwrite(fp, "      rd_type    : \"%d\",", iq_disp.inst[d_idx].rd_type);
      $fwrite(fp, "      rd_regidx  : %d,", iq_disp.inst[d_idx].rd_regidx);

      $fwrite(fp, "      rs1_valid  : %d,", iq_disp.inst[d_idx].rs1_valid);
      $fwrite(fp, "      rs1_type   : \"%d\",", iq_disp.inst[d_idx].rs1_type);
      $fwrite(fp, "      rs1_regidx : %d,", iq_disp.inst[d_idx].rs1_regidx);

      $fwrite(fp, "      rs2_valid  : %d,", iq_disp.inst[d_idx].rs2_valid);
      $fwrite(fp, "      rs2_type   : \"%d\",", iq_disp.inst[d_idx].rs2_type);
      $fwrite(fp, "      rs2_regidx : %d,", iq_disp.inst[d_idx].rs2_regidx);

      $fwrite(fp, "      \"cat[d_idx]\" : \"%d\",", iq_disp.inst[d_idx].cat);
      $fwrite(fp, "    },\n");
    end
  end

  $fwrite(fp, "  },\n");
endfunction // dump
`endif // SIMULATION


endmodule // inst_buffer
