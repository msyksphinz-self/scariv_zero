module inst_buffer
  (
 input logic                                i_clk,
 input logic                                i_reset_n,

 input logic                                i_inst_vld,

 output logic                                o_inst_rdy,
 input logic [riscv_pkg::VADDR_W-1: 1]       i_inst_pc,
 input logic [msrh_pkg::ICACHE_DATA_W-1: 0]  i_inst_in,
 input logic [msrh_pkg::ICACHE_DATA_B_W-1:0] i_inst_byte_en,

 output logic                                o_inst_buf_valid,
 output logic [riscv_pkg::VADDR_W-1: 1]       o_inst_pc,
 output msrh_pkg::disp_t [msrh_pkg::DISP_SIZE-1:0] o_inst_buf,
 input logic                                i_inst_buf_ready
 );

logic                                       w_inst_buffer_fire;

logic [msrh_pkg::DISP_SIZE-1:0] w_inst_arith_pick_up;
logic [msrh_pkg::DISP_SIZE-1:0] w_inst_mem_pick_up;

logic [msrh_pkg::DISP_SIZE-1:0] w_inst_arith_disp;
logic [msrh_pkg::DISP_SIZE-1:0] w_inst_mem_disp;
logic [msrh_pkg::DISP_SIZE-1:0] w_inst_disp_or;
logic [msrh_pkg::DISP_SIZE-1:0] w_inst_disp_mask;

localparam ic_word_num = msrh_pkg::ICACHE_DATA_B_W / 4;
msrh_pkg::inst_cat_t w_inst_cat[ic_word_num];
logic [ic_word_num-1:0] w_inst_is_arith;
logic [ic_word_num-1:0] w_inst_is_mem;

logic [ic_word_num-1:0] w_inst_arith_msb;
logic [ic_word_num-1:0] w_inst_mem_msb;

logic [ic_word_num-1:0] rd_valid;
logic [ 1: 0]           rs1_type[ic_word_num-1:0];
logic [ic_word_num-1:0] rs2_type;

logic [ic_word_num-1:0] r_head_inst_issued;
logic [ic_word_num-1:0] w_head_inst_issued_next;
logic [$clog2(ic_word_num)-1:0] r_head_start_pos;
logic [$clog2(ic_word_num)-1:0] w_head_start_pos_next;
logic                           w_head_all_inst_issued;

typedef struct packed {
  logic                                  vld;
  logic [riscv_pkg::VADDR_W-1: 1]        pc;
  logic [msrh_pkg::ICACHE_DATA_W-1: 0]   data;
  logic [msrh_pkg::ICACHE_DATA_B_W-1: 0] byte_en;
} inst_buf_t;

inst_buf_t r_inst_queue[msrh_pkg::INST_BUF_SIZE];
logic [msrh_pkg::INST_BUF_SIZE-1:0]      w_inst_buffer_vld;

logic [$clog2(msrh_pkg::INST_BUF_SIZE)-1:0] r_inst_buffer_inptr;
logic [$clog2(msrh_pkg::INST_BUF_SIZE)-1:0] r_inst_buffer_outptr;
logic                                       w_ptr_in_fire;
logic                                       w_ptr_out_fire;

assign w_head_all_inst_issued = w_inst_buffer_fire & (&w_head_inst_issued_next);

assign w_ptr_in_fire  = i_inst_vld & o_inst_rdy;
assign w_ptr_out_fire = w_head_all_inst_issued;

// Queue Control Pointer
inoutptr
  #(
    .SIZE(msrh_pkg::INST_BUF_SIZE)
    )
inst_buf_ptr
  (
   .i_clk     (i_clk),
   .i_reset_n (i_reset_n),

   .i_in_vld  (w_ptr_in_fire),
   .o_in_ptr  (r_inst_buffer_inptr),
   .i_out_vld (w_ptr_out_fire),
   .o_out_ptr (r_inst_buffer_outptr)
   );

assign w_inst_buffer_fire = o_inst_buf_valid & i_inst_buf_ready;

generate for (genvar idx = 0; idx < msrh_pkg::INST_BUF_SIZE; idx++) begin : inst_buf_loop

  assign w_inst_buffer_vld[idx] = r_inst_queue[idx].vld;

  always_ff @ (posedge i_clk, negedge i_reset_n) begin
    if (!i_reset_n) begin
      r_inst_queue[idx].vld <= 1'b0;
    end else begin
      if (w_ptr_in_fire & (r_inst_buffer_inptr == idx)) begin
        r_inst_queue[idx].vld  <= 1'b1;
        r_inst_queue[idx].data <= i_inst_in;
        r_inst_queue[idx].pc   <= i_inst_pc;
        r_inst_queue[idx].byte_en <= i_inst_byte_en;
      end else if (w_head_all_inst_issued & (r_inst_buffer_outptr == idx)) begin
        r_inst_queue[idx].vld  <= 1'b0;
      end // if (i_inst_vld & o_inst_rdy)
    end // else: !if(!i_reset_n)
  end // always_ff @ (posedge i_clk, negedge i_reset_n)

end // block: inst_buf_loop
endgenerate


assign o_inst_rdy = !(&w_inst_buffer_vld);

encoder
  #(.SIZE(ic_word_num))
u_start_pos_enc
  (
   .i_in({{(ic_word_num - msrh_pkg::DISP_SIZE - 1){1'b0}}, {w_inst_disp_mask, w_inst_disp_mask[0]} ^ {1'b0, w_inst_disp_mask}}),
   .o_out(w_head_start_pos_next)
   );


/* verilator lint_off WIDTH */
assign w_head_inst_issued_next = r_head_inst_issued | w_inst_disp_mask << r_head_start_pos;

always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_head_inst_issued <= {ic_word_num{1'b0}};
    r_head_start_pos   <= 'h0;
  end else begin
    if (w_inst_buffer_fire) begin
      if (&w_head_inst_issued_next) begin
        r_head_inst_issued <= 'h0;
        r_head_start_pos   <= 'h0;
      end else begin
        r_head_inst_issued <= w_head_inst_issued_next;
        r_head_start_pos   <= w_head_start_pos_next;
      end
    end
  end
end


generate for (genvar w_idx = 0; w_idx < ic_word_num; w_idx++) begin : word_loop
  logic [ 1: 0] raw_cat;
  decoder_cat
  u_decoder_cat
    (
     .inst(r_inst_queue[r_inst_buffer_outptr].data[w_idx*32+:32]),
     .cat(raw_cat)
     );
  assign w_inst_cat[w_idx] = msrh_pkg::inst_cat_t'(raw_cat);

  decoder_reg
  u_decoder_reg
    (
     .inst(r_inst_queue[r_inst_buffer_outptr].data[w_idx*32+:32]),
     .rd(rd_valid[w_idx]),
     .r1(rs1_type[w_idx]),
     .r2(rs2_type[w_idx])
     );


  assign w_inst_is_arith[w_idx] = r_inst_queue[r_inst_buffer_outptr].vld & (w_inst_cat[w_idx] == msrh_pkg::CAT_ARITH);
  assign w_inst_is_mem  [w_idx] = r_inst_queue[r_inst_buffer_outptr].vld & (w_inst_cat[w_idx] == msrh_pkg::CAT_MEM  );

end
endgenerate

assign w_inst_arith_pick_up = w_inst_is_arith[r_head_start_pos +: msrh_pkg::DISP_SIZE];
assign w_inst_mem_pick_up   = w_inst_is_mem  [r_head_start_pos +: msrh_pkg::DISP_SIZE];

bit_pick_up #(.WIDTH(msrh_pkg::DISP_SIZE), .NUM(msrh_pkg::ARITH_DISP_SIZE)) u_arith_disp_pick_up (.in(w_inst_arith_pick_up), .out(w_inst_arith_disp));
bit_pick_up #(.WIDTH(msrh_pkg::DISP_SIZE), .NUM(msrh_pkg::MEM_DISP_SIZE  )) u_mem_disp_pick_up   (.in(w_inst_mem_pick_up),   .out(w_inst_mem_disp  ));

assign w_inst_disp_or = w_inst_arith_disp | w_inst_mem_disp;

bit_tree_msb #(.WIDTH(msrh_pkg::DISP_SIZE)) u_inst_msb (.in(w_inst_disp_or), .out(w_inst_disp_mask));


assign o_inst_buf_valid = |w_inst_disp_mask;
assign o_inst_pc = r_inst_queue[r_inst_buffer_outptr].pc;
generate for (genvar d_idx = 0; d_idx < msrh_pkg::DISP_SIZE; d_idx++) begin : disp_loop
  logic [31: 0] w_inst;
  assign w_inst = r_inst_queue[r_inst_buffer_outptr].data[(d_idx+r_head_start_pos)*32+:32];

  assign o_inst_buf[d_idx].valid = w_inst_disp_mask[d_idx];
  assign o_inst_buf[d_idx].inst  = w_inst;

  assign o_inst_buf[d_idx].rd_valid   = rd_valid[d_idx+r_head_start_pos];
  assign o_inst_buf[d_idx].rd_type    = msrh_pkg::GPR;
  assign o_inst_buf[d_idx].rd_regidx  = w_inst[11: 7];

  assign o_inst_buf[d_idx].rs1_valid  = rs1_type[d_idx+r_head_start_pos] != 'h0;
  assign o_inst_buf[d_idx].rs1_type   = msrh_pkg::GPR;
  assign o_inst_buf[d_idx].rs1_regidx = w_inst[19:15];

  assign o_inst_buf[d_idx].rs2_valid  = rs2_type[d_idx+r_head_start_pos] != 'h0;
  assign o_inst_buf[d_idx].rs2_type   = msrh_pkg::GPR;
  assign o_inst_buf[d_idx].rs2_regidx = w_inst[24:20];

end
endgenerate


endmodule // inst_buffer
