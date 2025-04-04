// ------------------------------------------------------------------------
// NAME : MRSH Predictor
// TYPE : module
// ------------------------------------------------------------------------
// It includes all variations of predictors for SCARIV
// ------------------------------------------------------------------------
//
// ------------------------------------------------------------------------

// `default_nettype none

module scariv_predictor
  import scariv_pkg::*;
  import scariv_ic_pkg::*;
  import scariv_predict_pkg::*;
  import scariv_lsu_pkg::*;
(
 input logic  i_clk,
 input logic  i_reset_n,

 commit_if.monitor commit_if,

 input logic i_f1_valid,
 input logic i_f2_valid,
 input scariv_ic_pkg::ic_resp_t i_f2_ic_resp,

 btb_update_if.slave update_btb_if,
 btb_search_if.slave search_btb_if,
 btb_search_if.monitor search_btb_mon_if,
 output vaddr_t o_f1_btb_target_vaddr,

 ras_search_if.master ras_search_if,

 gshare_search_if.slave gshare_search_if,

 // Feedback into Frontend
 output logic   o_f2_predict_valid,
 output vaddr_t o_f2_predict_target_vaddr,

 br_upd_if.slave    br_upd_if
 );

ic_block_t w_f1_btb_hit_oh;

scariv_btb u_btb
  (
   .i_clk(i_clk),
   .i_reset_n(i_reset_n),

   .update_btb_if (update_btb_if),
   .search_btb_if (search_btb_if)
   );

bit_extract_lsb #(.WIDTH($bits(ic_block_t))) u_f1_btb_extract_lsb_oh (.in(search_btb_if.f1_hit), .out(w_f1_btb_hit_oh));

bit_oh_or_packed
  #(.T(vaddr_t),
    .WORDS($bits(ic_block_t))
    )
u_f1_target_vaddr_hit_oh (
 .i_oh      (w_f1_btb_hit_oh),
 .i_data    (search_btb_if.f1_target_vaddr),
 .o_selected(o_f1_btb_target_vaddr)
 );

typedef enum logic {
  RVC_CALL = 1'b0,
  STD_CALL = 1'b1
} call_size_t;

ic_block_t   w_rvc_call_be;
ic_block_t   w_std_call_be;
call_size_t  w_call_size_array[ICACHE_DATA_B_W/2];

ic_block_t   w_rvc_noncond_be;
ic_block_t   w_std_noncond_be;

ic_block_t   w_f1_call_be;
ic_block_t   w_f1_call_be_lsb;

ic_block_t   w_f1_call_valid;
ic_block_t   w_f1_ret_valid;

ic_block_t   w_f1_ret_be;
ic_block_t   w_f1_ret_be_lsb;

ic_block_t   w_f2_call_be;
ic_block_t   w_f2_noncond_be;
vaddr_t      w_f2_call_vaddr;
ic_vaddr_h_t w_f2_ras_next_pc;
ic_block_t   w_f2_ret_be;
ic_vaddr_h_t w_f2_ras_ret_vaddr;

// ic_vaddr_h_t w_sc_ras_next_pc;
// ic_vaddr_h_t w_sc_ras_ret_vaddr;

ic_block_t  w_f2_call_valid;
ic_block_t  w_f2_call_valid_oh;
ic_block_t  w_f2_ret_valid;
ic_block_t  w_f2_ret_valid_oh;

logic [31: 0]                    w_f2_inst_array_32bit[ICACHE_DATA_B_W/2];
logic [31: 0]                    w_f2_inst_array_oh;
logic [$clog2(ICACHE_DATA_B_W/2)-1: 0] w_f2_call_enc;
ic_vaddr_h_t        w_f2_call_target_vaddr;
ic_vaddr_h_t        w_f2_call_offset;
ic_vaddr_h_t        w_f2_call_pc;

// grp_id_t w_sc_grp_valid;
// grp_id_t w_sc_call_be;
// grp_id_t w_sc_ret_be;
// grp_id_t w_sc_call_valid;
// grp_id_t w_sc_ret_valid;

/* verilator lint_off UNOPTFLAT */
logic [ICACHE_DATA_B_W / 2 -1: 0] w_is_32bit_inst;

logic [scariv_conf_pkg::ICACHE_DATA_W-1: 0] w_f2_inst;
// logic [ICACHE_DATA_B_W-1: 0]              w_f2_inst_be;
assign w_f2_inst    = i_f2_ic_resp.data;
// assign w_f2_inst_be = i_f2_ic_resp.be;

logic [riscv_pkg::VADDR_W-1: $clog2(ICACHE_DATA_B_W/2)+1] r_f2_prev_upper_vaddr_p1;
logic                                                   r_is_32bit_inst_msb;
logic                                                   w_f2_call_be_msb;
logic [15: 0]                                           r_last_prev_inst_uppper_16bit;
always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_f2_prev_upper_vaddr_p1 <= 'h0;
    r_is_32bit_inst_msb <= 1'b0;
    w_f2_call_be_msb <= 1'b0;
    r_last_prev_inst_uppper_16bit <= 'h0;
  end else begin
    if (i_f2_valid & i_f2_ic_resp.valid) begin
      r_f2_prev_upper_vaddr_p1       <= i_f2_ic_resp.vaddr[riscv_pkg::VADDR_W-1: $clog2(ICACHE_DATA_B_W/2)+1] + 'h1;
      r_is_32bit_inst_msb            <= w_is_32bit_inst[ICACHE_DATA_B_W / 2 -1];
      w_f2_call_be_msb               <= w_f2_call_be   [ICACHE_DATA_B_W / 2 -1];
      r_last_prev_inst_uppper_16bit  <= i_f2_ic_resp.data[scariv_conf_pkg::ICACHE_DATA_W-1 -: 16];
    end
  end
end



generate for (genvar c_idx = 0; c_idx < ICACHE_DATA_B_W / 2; c_idx++) begin : call_loop
  // assign w_f2_inst_be[c_idx] = &(i_f2_ic_resp.be[c_idx*2 +: 2]);

  logic [15: 0] w_rvc_inst;
  logic [31: 0] w_std_inst;
  logic         is_rvc_j;
  logic         is_rvc_jal;
  logic         is_rvc_jalr;
  logic         is_rvc_jr;
  logic         rvc_call_be;
  logic         is_rvc_ret_raw;
  logic         is_std_ret_raw;
  assign w_rvc_inst = i_f2_ic_resp.data[c_idx*16 +: 16];
  if (riscv_pkg::XLEN_W == 32) begin
    assign is_rvc_jal = (w_rvc_inst[1:0] == 2'b01) &
                        (w_rvc_inst[15:13] == 3'b001);
  end else begin
    assign is_rvc_jal = 'b0;
  end // else: !if(riscv_pkg::XLEN_W == 32)
  assign is_rvc_j = (w_rvc_inst[1:0] == 2'b01) &
                    (w_rvc_inst[15:13] == 3'b101);
  assign is_rvc_jr = (w_rvc_inst[ 1: 0] == 2'b01) &
                     (w_rvc_inst[ 6: 2] == 5'h0) &
                     (w_rvc_inst[11: 7] != 5'h0) &
                     (w_rvc_inst[15:12] == 4'b1000);
  assign is_rvc_jalr = (w_rvc_inst[ 1: 0] == 2'b10) &
                       (w_rvc_inst[15:12] == 4'b1001) &
                       (w_rvc_inst[11: 7] != 5'h0) &
                       (w_rvc_inst[ 6: 2] == 5'h0);

  logic           w_same_prev_vaddr;
  assign w_same_prev_vaddr = r_f2_prev_upper_vaddr_p1 ==
                             i_f2_ic_resp.vaddr[riscv_pkg::VADDR_W-1: $clog2(ICACHE_DATA_B_W/2)+1];
  if (c_idx == 0) begin
    assign w_is_32bit_inst [c_idx] = (w_rvc_inst[1:0] == 2'b11) & (w_same_prev_vaddr & ~r_is_32bit_inst_msb | ~w_same_prev_vaddr);
  end else begin
    assign w_is_32bit_inst [c_idx] = (w_rvc_inst[1:0] == 2'b11) & !w_is_32bit_inst[c_idx-1];
  end
  assign w_rvc_call_be   [c_idx] = is_rvc_jal & !w_is_32bit_inst[c_idx-1];
  assign w_rvc_noncond_be[c_idx] = (is_rvc_j | is_rvc_jr | is_rvc_jalr) & !w_is_32bit_inst[c_idx-1];

  logic           is_std_call;
  logic           is_std_callr;
  logic           is_std_jal;
  logic           is_std_jalr;
  /* verilator lint_off SELRANGE */
  if (c_idx == 0) begin
    assign w_std_inst = {w_f2_inst[15: 0], r_last_prev_inst_uppper_16bit};
    assign is_std_call = w_same_prev_vaddr & r_is_32bit_inst_msb &
                         (w_std_inst[11: 7] == 5'h1) &
                         (w_std_inst[ 6: 0] == 7'b1101111);
    assign is_std_jal = w_same_prev_vaddr & r_is_32bit_inst_msb &
                        (w_std_inst[11: 7] != 5'h1) &
                        (w_std_inst[ 6: 0] == 7'b1101111);
    assign is_std_callr = w_same_prev_vaddr & r_is_32bit_inst_msb &
                          (w_std_inst[14:12] == 3'b000) &
                          (w_std_inst[11: 7] == 5'h1) &
                          (w_std_inst[ 6: 0] == 7'b1100111);
    assign is_std_jalr = w_same_prev_vaddr & r_is_32bit_inst_msb &
                         (w_std_inst[14:12] == 3'b000) &
                         (w_std_inst[11: 7] != 5'h1) &
                         (w_std_inst[ 6: 0] == 7'b1100111);
  end else begin
    assign w_std_inst = w_f2_inst[(c_idx+1)*16-1 -: 32];
    assign is_std_call = ~w_is_32bit_inst[c_idx] &
                         (w_std_inst[11: 7] == 5'h1) &
                         (w_std_inst[ 6: 0] == 7'b1101111);
    assign is_std_jal = ~w_is_32bit_inst[c_idx] &
                        (w_std_inst[11: 7] != 5'h1) &
                        (w_std_inst[ 6: 0] == 7'b1101111);
    assign is_std_callr = ~w_is_32bit_inst[c_idx] &
                          (w_std_inst[14:12] == 3'b000) &
                          (w_std_inst[11: 7] == 5'h1) &
                          (w_std_inst[ 6: 0] == 7'b1100111);
    assign is_std_jalr = ~w_is_32bit_inst[c_idx] &
                         (w_std_inst[14:12] == 3'b000) &
                         (w_std_inst[11: 7] != 5'h1) &
                         (w_std_inst[ 6: 0] == 7'b1100111);
  end
  assign w_f2_inst_array_32bit[c_idx] = w_std_inst;
  assign w_std_call_be   [c_idx] = is_std_call | is_std_callr;
  assign w_std_noncond_be[c_idx] = is_std_jal  | is_std_jalr ;

  assign w_call_size_array[c_idx] = w_std_call_be[c_idx] ? STD_CALL : RVC_CALL;
  assign w_f2_call_be[c_idx] = (w_rvc_call_be[c_idx] | w_std_call_be[c_idx]) & i_f2_ic_resp.valid &
                               i_f2_ic_resp.be[c_idx * 2];

  assign w_f2_noncond_be[c_idx] = (w_rvc_noncond_be[c_idx] | w_std_noncond_be[c_idx]) & i_f2_ic_resp.valid &
                                  i_f2_ic_resp.be[c_idx * 2];
  // --------------------------o
  // Decode RET (JALR X0,X1,0)
  // --------------------------
  logic w_is_rvc_ret;
  logic w_is_std_ret;
  assign is_rvc_ret_raw = (w_rvc_inst[ 1: 0] == 2'b10) &
                          (w_rvc_inst[ 6: 2] == 5'h0) &
                          (w_rvc_inst[11: 7] == 5'h1) &
                          (w_rvc_inst[15:12] == 4'b1000);
  assign is_std_ret_raw = (w_std_inst[ 6: 0] == 7'b1100111) &
                          (w_std_inst[14:12] == 3'b000) &
                          (w_std_inst[11: 7] == 5'h0) &
                          (w_std_inst[19:15] == 5'h1);
  if (c_idx != 0) begin
    assign w_is_rvc_ret = !w_is_32bit_inst[c_idx-1] & is_rvc_ret_raw;
    assign w_is_std_ret = !w_is_32bit_inst[c_idx-1] & is_std_ret_raw;
  end else begin
    assign w_is_rvc_ret = w_same_prev_vaddr & !r_is_32bit_inst_msb & is_rvc_ret_raw;
    assign w_is_std_ret = w_same_prev_vaddr &  r_is_32bit_inst_msb & is_std_ret_raw;
  end
  assign w_f2_ret_be[c_idx] = (w_is_rvc_ret | w_is_std_ret) & i_f2_ic_resp.valid &
                              i_f2_ic_resp.be[c_idx * 2];
end // block: rvc_jal_loop
endgenerate

/* verilator lint_off WIDTH */
assign w_f1_call_be = search_btb_if.f1_is_call;
assign w_f1_ret_be  = search_btb_if.f1_is_ret;

bit_extract_lsb #(.WIDTH(ICACHE_DATA_B_W/2)) call_f1_be_lsb (.in(w_f1_call_be), .out(w_f1_call_be_lsb));
bit_extract_lsb #(.WIDTH(ICACHE_DATA_B_W/2)) ret_f1_be_lsb  (.in(w_f1_ret_be),  .out(w_f1_ret_be_lsb));

logic [$clog2(scariv_conf_pkg::RAS_ENTRY_SIZE)-1: 0] w_ras_index_next;
logic [$clog2(scariv_conf_pkg::RAS_ENTRY_SIZE)-1: 0] r_ras_input_index;
logic [$clog2(scariv_conf_pkg::RAS_ENTRY_SIZE)-1: 0] w_ras_output_index;
/* verilator lint_off UNOPTFLAT */
logic [$clog2(scariv_conf_pkg::RAS_ENTRY_SIZE)-1: 0] w_f2_ras_index_next;
logic [$clog2(scariv_conf_pkg::RAS_ENTRY_SIZE)-1: 0] w_ras_wr_index;
logic                                              w_cmt_update_ras_idx;
logic                                              w_cmt_dead_valid;

logic [$clog2(scariv_conf_pkg::RAS_ENTRY_SIZE)-1: 0] r_f2_ras_index_next;

logic                                              w_br_call_dead;
logic                                              w_br_ret_dead;
logic                                              r_during_recover;

assign w_br_call_dead = br_upd_if.update & br_upd_if.dead & br_upd_if.is_call;
assign w_br_ret_dead  = br_upd_if.update & br_upd_if.dead & br_upd_if.is_ret ;

always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_during_recover <= 1'b0;
  end else begin
    if (w_br_call_dead | w_br_ret_dead) begin
      r_during_recover <= 1'b1; // Enter recovering mode
    end else if (br_upd_if.update & ~br_upd_if.dead) begin
      r_during_recover <= 1'b0; // Leave recovering mode
    end

  end // else: !if(!i_reset_n)
end // always_ff @ (posedge i_clk, negedge i_reset_n)

logic w_ras_commit_flush;
logic w_ras_br_flush;
logic w_ras_flush_valid;
logic [scariv_conf_pkg::DISP_SIZE-1: 0] w_ras_commit_flush_valid_oh;
logic [RAS_W-1: 0]          w_ras_commit_flush_ras_index_oh;
assign w_ras_commit_flush = scariv_pkg::is_flushed_commit(commit_if.commit_valid, commit_if.payload) /* & |(commit_if.payload.flush_valid & commit_if.ras_update) */;
assign w_ras_br_flush = br_upd_if.update & ~br_upd_if.dead & br_upd_if.mispredict /* &
                        (br_upd_if.is_call | br_upd_if.is_ret) */;
bit_extract_lsb #(.WIDTH(scariv_conf_pkg::DISP_SIZE)) commit_flush_valid_oh (.in(commit_if.payload.flush_valid), .out(w_ras_commit_if.payload.flush_valid_oh));
bit_oh_or_packed #(.T(logic [RAS_W-1: 0]), .WORDS(scariv_conf_pkg::DISP_SIZE))
bit_oh_call_target(.i_oh(w_ras_commit_if.payload.flush_valid_oh), .i_data(commit_if.ras_index), .o_selected(w_ras_commit_flush_ras_index_oh));
assign w_ras_flush_valid   = w_ras_commit_flush | w_ras_br_flush;

logic [RAS_W-1: 0]          w_flush_ras_index;
assign w_flush_ras_index = w_ras_commit_flush ? w_ras_commit_flush_ras_index_oh : br_upd_if.ras_index;

always_comb begin
  w_f2_ras_index_next = r_ras_input_index;

  if (w_ras_flush_valid) begin
    w_f2_ras_index_next = w_flush_ras_index;
  // end else if (w_br_call_dead & ~r_during_recover) begin
  //   w_f2_ras_index_next = br_upd_if.ras_index;
  // end else if (w_br_ret_dead & ~r_during_recover) begin
  //   w_f2_ras_index_next = br_upd_if.ras_index + 'h1;
  end

  w_ras_index_next = w_f2_ras_index_next;
  if (|w_f2_ret_valid) begin
    w_ras_index_next = w_f2_ras_index_next - 'h1;
  end else if (|w_f2_call_valid) begin
    w_ras_index_next = w_f2_ras_index_next + 'h1;
  end
  w_ras_wr_index = w_ras_index_next;
end

assign w_ras_output_index = w_ras_index_next - 1;

always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_ras_input_index   <= 'h0;
    r_f2_ras_index_next <= 'h0;
  end else begin
    r_ras_input_index   <= w_ras_index_next;
    r_f2_ras_index_next <= w_f2_ras_index_next;
  end
end

// ----------------------------------------
// Extracting Call/Ret for 1st instruction
// ----------------------------------------
bit_extract_lsb #(.WIDTH(ICACHE_DATA_B_W/2)) f1_btb_hit_select (.in(search_btb_if.f1_hit &
                                                                    (ras_search_if.f1_is_call | ras_search_if.f1_is_ret) &
                                                                    search_btb_if.f1_pc_vaddr_mask), .out(w_f1_btb_hit_oh));
assign w_f1_call_valid = {(ICACHE_DATA_B_W/2){i_f1_valid}} & w_f1_btb_hit_oh & ras_search_if.f1_is_call;
assign w_f1_ret_valid  = {(ICACHE_DATA_B_W/2){i_f1_valid}} & w_f1_btb_hit_oh & ras_search_if.f1_is_ret;

ic_block_t w_f2_ras_be;
assign w_f2_ras_be = ({w_f2_call_valid_oh, 2'b00} - 'h1) & ({w_f2_ret_valid_oh, 2'b00} - 'h1);

assign ras_search_if.f1_is_call   = search_btb_if.f1_is_call;
assign ras_search_if.f1_is_ret    = search_btb_if.f1_is_ret;
assign ras_search_if.f1_ras_vaddr = 'h0;
assign ras_search_if.f1_ras_index = 'h0;

always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    ras_search_if.f2_is_call <= 'h0;
    ras_search_if.f2_is_ret  <= 'h0;
  end else begin
    ras_search_if.f2_is_call <= w_f1_call_valid;
    ras_search_if.f2_is_ret  <= w_f1_ret_valid;
  end // else: !if(!i_reset_n)
end // always_ff @ (posedge i_clk, negedge i_reset_n)
assign ras_search_if.f2_call_target_vaddr = w_f2_call_target_vaddr;
generate for (genvar be_idx = 0; be_idx < ICACHE_DATA_B_W / 2; be_idx++) begin : f2_be_loop
  assign ras_search_if.f2_ras_be[be_idx*2+0] = w_f2_ras_be[be_idx];
  assign ras_search_if.f2_ras_be[be_idx*2+1] = w_f2_ras_be[be_idx];
end
endgenerate

assign ras_search_if.f2_ras_vaddr         = w_f2_ras_ret_vaddr;
assign ras_search_if.f2_ras_index         = /* |w_f2_ret_valid ? w_ras_index_next : */w_f2_ras_index_next;

// assign o_sc_ras_index = w_f2_ras_index_next;
// assign o_sc_ras_vaddr = {w_sc_ras_ret_vaddr, 1'b0};

// grp_id_t w_sc_call_be_array_vld;
// disp_t w_sc_call_entry;
//
// assign w_sc_call_be_array_vld = w_sc_call_be & w_sc_grp_valid;

/* verilator lint_off WIDTH */
assign w_f2_ras_next_pc = {i_f2_ic_resp.vaddr[riscv_pkg::VADDR_W-1: $clog2(ICACHE_DATA_B_W)], {$clog2(ICACHE_DATA_B_W/2){1'b0}}} +
                          w_f2_call_enc + 'h1;

// assign w_sc_ras_next_pc = w_sc_call_entry.pc_addr[riscv_pkg::VADDR_W-1: 1] + (w_sc_call_entry.rvc_inst_valid ? 1 : 2);
//
// bit_oh_or_packed #(.T(disp_t), .WORDS(scariv_conf_pkg::DISP_SIZE))
// bit_oh_call_target(.i_oh(w_sc_call_be_array_vld), .i_data(sc_disp.inst), .o_selected(w_sc_call_entry));

scariv_pred_ras
u_ras
  (
   .i_clk (i_clk),
   .i_reset_n (i_reset_n),

   .i_wr_valid (|w_f2_call_valid),
   .i_wr_index (w_f2_ras_index_next),
   .i_wr_pa    (w_f2_ras_next_pc),

   .i_f2_rd_valid ((|w_f2_ret_valid)),
   .i_f2_rd_index (r_ras_input_index-1),
   .o_f2_rd_pa    (w_f2_ras_ret_vaddr),

   .i_br_call_cmt_valid     (w_br_call_dead & ~r_during_recover),
   .i_br_call_cmt_ras_index (br_upd_if.ras_index),
   .i_br_call_cmt_wr_vpc    (br_upd_if.ras_prev_vaddr[riscv_pkg::VADDR_W-1: 1])
   );


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

always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (i_reset_n) begin
    if (u_ras.i_wr_valid) begin
      rtl_push_ras ($time, i_f2_ic_resp.vaddr + encoder_func(w_f2_call_valid_oh) << 1,
                    u_ras.i_wr_index, {u_ras.i_wr_pa, 1'b0});
    end
    if (u_ras.i_f2_rd_valid) begin
      rtl_pop_ras ($time, i_f2_ic_resp.vaddr + encoder_func(w_f2_ret_valid_oh) << 1,
                   u_ras.i_f2_rd_index, {u_ras.o_f2_rd_pa, 1'b0});
    end

    if (w_ras_br_flush) begin
      rtl_flush_ras ($time, br_upd_if.cmt_id, br_upd_if.grp_id,
                     br_upd_if.pc_vaddr, br_upd_if.ras_index);
    end
    if (w_ras_commit_flush) begin
      rtl_flush_ras ($time, commit_if.payload.cmt_id, w_ras_commit_if.payload.flush_valid_oh,
                     'h0, w_ras_commit_flush_ras_index_oh);
    end
  end
end // always_ff @ (posedge i_clk, negedge i_reset_n)

`endif // SIMULATION


bit_extract_lsb #(.WIDTH(ICACHE_DATA_B_W/2)) f1_pred_hit_select (.in((w_f1_call_be | w_f1_ret_be) & search_btb_if.f1_pc_vaddr_mask), .out(w_f1_btb_hit_oh));

ic_block_t w_f2_noncond_call_ret_be_oh;

bit_extract_lsb #(.WIDTH(ICACHE_DATA_B_W/2)) f2_pred_hit_select (.in(w_f2_noncond_be | w_f2_call_be | w_f2_ret_be), .out(w_f2_noncond_call_ret_be_oh));

assign w_f2_call_valid = ras_search_if.f2_is_call;
assign w_f2_ret_valid  = ras_search_if.f2_is_ret;

bit_extract_lsb #(.WIDTH(ICACHE_DATA_B_W/2)) f2_call_valid_oh (.in(w_f2_call_valid), .out(w_f2_call_valid_oh));
bit_extract_lsb #(.WIDTH(ICACHE_DATA_B_W/2)) f2_ret_valid_oh  (.in(w_f2_ret_valid ), .out(w_f2_ret_valid_oh ));
bit_oh_or #(.T(logic[31: 0]), .WORDS(ICACHE_DATA_B_W/2))
f2_inst_arary_32bit_sel(.i_oh(w_f2_call_valid_oh), .i_data(w_f2_inst_array_32bit), .o_selected(w_f2_inst_array_oh));
encoder #(.SIZE(ICACHE_DATA_B_W/2)) f2_call_loc_encoder (.i_in(w_f2_call_valid_oh), .o_out(w_f2_call_enc));
assign w_f2_call_offset = $signed({{(riscv_pkg::VADDR_W-11){w_f2_inst_array_oh[31]}}, w_f2_inst_array_oh[31], w_f2_inst_array_oh[19:12], w_f2_inst_array_oh[20], w_f2_inst_array_oh[30:21]});
assign w_f2_call_pc     = {i_f2_ic_resp.vaddr[riscv_pkg::VADDR_W-1: $clog2(ICACHE_DATA_B_W/2)+1], {$clog2(ICACHE_DATA_B_W/2){1'b0}}};
assign w_f2_call_target_vaddr = w_f2_call_offset + w_f2_call_pc + w_f2_call_enc - 1;


// -----------------
// GShare Predictor
// -----------------

scariv_gshare
u_gshare
  (
   .i_clk     (i_clk),
   .i_reset_n (i_reset_n),

   .i_f1_valid (i_f1_valid),
   .i_f2_valid (i_f2_valid),

   .search_btb_if    (search_btb_mon_if),
   .gshare_search_if (gshare_search_if ),
   .br_upd_if        (br_upd_if        ),

   .o_f2_predict_valid        (o_f2_predict_valid       ),
   .o_f2_predict_target_vaddr (o_f2_predict_target_vaddr)
   );



endmodule // scariv_predictor

// `default_nettype wire
