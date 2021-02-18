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

logic [$clog2(msrh_pkg::INST_BUF_SIZE)-1:0] inst_buffer_inptr_q;
logic [$clog2(msrh_pkg::INST_BUF_SIZE)-1:0] inst_buffer_outptr_q;

typedef struct packed {
  logic                                  vld;
  logic [riscv_pkg::VADDR_W-1: 1]        pc;
  logic [msrh_pkg::ICACHE_DATA_W-1: 0]   data;
  logic [msrh_pkg::ICACHE_DATA_B_W-1: 0] byte_en;
} inst_buf_t;

inst_buf_t inst_queue[msrh_pkg::INST_BUF_SIZE];
logic [msrh_pkg::INST_BUF_SIZE-1:0]      w_inst_buffer_vld;


assign w_inst_buffer_fire = o_inst_buf_valid & i_inst_buf_ready;

generate for (genvar idx = 0; idx < msrh_pkg::INST_BUF_SIZE; idx++) begin : inst_buf_loop

  assign w_inst_buffer_vld[idx] = inst_queue[idx].vld;

  always_ff @ (posedge i_clk, negedge i_reset_n) begin
    if (!i_reset_n) begin
      inst_queue[idx].vld <= 1'b0;
    end else begin
      if (i_inst_vld & o_inst_rdy & (inst_buffer_inptr_q == idx)) begin
        inst_queue[idx].vld  <= 1'b1;
        inst_queue[idx].data <= i_inst_in;
        inst_queue[idx].pc   <= i_inst_pc;
        inst_queue[idx].byte_en <= i_inst_byte_en;
      end else if (w_inst_buffer_fire & (inst_buffer_outptr_q == idx)) begin
        inst_queue[idx].vld  <= 1'b0;
      end // if (i_inst_vld & o_inst_rdy)
    end // else: !if(!i_reset_n)
  end // always_ff @ (posedge i_clk, negedge i_reset_n)

end // block: inst_buf_loop
endgenerate

always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    inst_buffer_inptr_q <= 'h0;
    inst_buffer_outptr_q <= 'h0;
  end else begin
    inst_buffer_inptr_q  <= i_inst_vld & o_inst_rdy ? inst_buffer_inptr_q + 'h1 : inst_buffer_inptr_q;
    inst_buffer_outptr_q <= w_inst_buffer_fire ? inst_buffer_outptr_q + 'h1 : inst_buffer_outptr_q;
  end
end


assign o_inst_rdy = !(&w_inst_buffer_vld);

localparam ic_word_num = msrh_pkg::ICACHE_DATA_B_W / 4;
msrh_pkg::inst_cat_t w_inst_cat[ic_word_num];
logic [ic_word_num-1:0] w_inst_is_arith;
logic [ic_word_num-1:0] w_inst_is_mem;

logic [ic_word_num-1:0] w_inst_arith_msb;
logic [ic_word_num-1:0] w_inst_mem_msb;

logic [ic_word_num-1:0] rd_valid;
logic [ 1: 0]           rs1_type[ic_word_num-1:0];
logic [ic_word_num-1:0] rs2_type;

generate for (genvar w_idx = 0; w_idx < ic_word_num; w_idx++) begin : word_loop
  logic [ 1: 0] raw_cat;
  decoder_cat
  u_decoder_cat
    (
     .inst(inst_queue[inst_buffer_outptr_q].data[w_idx*32+:32]),
     .cat(raw_cat)
     );
  assign w_inst_cat[w_idx] = msrh_pkg::inst_cat_t'(raw_cat);

  decoder_reg
  u_decoder_reg
    (
     .inst(inst_queue[inst_buffer_outptr_q].data[w_idx*32+:32]),
     .rd(rd_valid[w_idx]),
     .r1(rs1_type[w_idx]),
     .r2(rs2_type[w_idx])
     );

  assign w_inst_is_arith[w_idx] = inst_queue[inst_buffer_outptr_q].vld & (w_inst_cat[w_idx] == msrh_pkg::CAT_ARITH);
  assign w_inst_is_mem  [w_idx] = inst_queue[inst_buffer_outptr_q].vld & (w_inst_cat[w_idx] == msrh_pkg::CAT_MEM  );

end
endgenerate

logic [msrh_pkg::DISP_SIZE-1:0] w_inst_arith_pick_up;
logic [msrh_pkg::DISP_SIZE-1:0] w_inst_mem_pick_up;

logic [msrh_pkg::DISP_SIZE-1:0] w_inst_arith_disp;
logic [msrh_pkg::DISP_SIZE-1:0] w_inst_mem_disp;
logic [msrh_pkg::DISP_SIZE-1:0] w_inst_disp_or;
logic [msrh_pkg::DISP_SIZE-1:0] w_inst_disp_mask;

assign w_inst_arith_pick_up = w_inst_is_arith[msrh_pkg::DISP_SIZE-1:0];
assign w_inst_mem_pick_up   = w_inst_is_mem  [msrh_pkg::DISP_SIZE-1:0];

bit_pick_up #(.WIDTH(msrh_pkg::DISP_SIZE), .NUM(msrh_pkg::ARITH_DISP_SIZE)) u_arith_disp_pick_up (.in(w_inst_arith_pick_up), .out(w_inst_arith_disp));
bit_pick_up #(.WIDTH(msrh_pkg::DISP_SIZE), .NUM(msrh_pkg::MEM_DISP_SIZE  )) u_mem_disp_pick_up   (.in(w_inst_mem_pick_up),   .out(w_inst_mem_disp  ));

assign w_inst_disp_or = w_inst_arith_disp | w_inst_mem_disp;

bit_tree_msb #(.WIDTH(msrh_pkg::DISP_SIZE)) u_inst_msb (.in(w_inst_disp_or), .out(w_inst_disp_mask));

assign o_inst_buf_valid = |w_inst_disp_mask;
assign o_inst_pc = inst_queue[inst_buffer_outptr_q].pc;
generate for (genvar d_idx = 0; d_idx < msrh_pkg::DISP_SIZE; d_idx++) begin : disp_loop
  logic [31: 0] w_inst;
  assign w_inst = inst_queue[inst_buffer_outptr_q].data[d_idx*32+:32];

  assign o_inst_buf[d_idx].valid = w_inst_disp_mask[d_idx];
  assign o_inst_buf[d_idx].inst  = w_inst;

  assign o_inst_buf[d_idx].rd_valid   = rd_valid[d_idx];
  assign o_inst_buf[d_idx].rd_type    = msrh_pkg::GPR;
  assign o_inst_buf[d_idx].rd_regidx  = w_inst[11: 7];

  assign o_inst_buf[d_idx].rs1_valid  = rs1_type[d_idx] != 'h0;
  assign o_inst_buf[d_idx].rs1_type   = msrh_pkg::GPR;
  assign o_inst_buf[d_idx].rs1_regidx = w_inst[19:15];

  assign o_inst_buf[d_idx].rs2_valid  = rs2_type[d_idx] != 'h0;
  assign o_inst_buf[d_idx].rs2_type   = msrh_pkg::GPR;
  assign o_inst_buf[d_idx].rs2_regidx = w_inst[24:20];

end
endgenerate


endmodule // inst_buffer
