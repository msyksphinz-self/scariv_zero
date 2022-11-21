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
  import scariv_predict_pkg::*;
  import scariv_lsu_pkg::*;
(
 input logic  i_clk,
 input logic  i_reset_n,

 input commit_blk_t i_commit,

 input logic i_s1_valid,
 input logic i_s2_valid,
 input scariv_ic_pkg::ic_resp_t i_s2_ic_resp,

 btb_update_if.slave update_btb_if,
 btb_search_if.slave search_btb_if,
 output vaddr_t o_s1_btb_target_vaddr,

 ras_search_if.master ras_search_if,

 gshare_search_if.slave gshare_search_if,

 br_upd_if.slave  br_upd_fe_if
 );

logic [ICACHE_DATA_B_W/2-1: 0] w_s1_btb_hit_oh;

scariv_btb u_btb
  (
   .i_clk(i_clk),
   .i_reset_n(i_reset_n),

   .update_btb_if (update_btb_if),
   .search_btb_if (search_btb_if)
   );

bit_oh_or_packed
  #(.T(vaddr_t),
    .WORDS(ICACHE_DATA_B_W/2)
    )
u_s1_target_vaddr_hit_oh (
 .i_oh      (search_btb_if.s1_hit),
 .i_data    (search_btb_if.s1_target_vaddr),
 .o_selected(o_s1_btb_target_vaddr)
 );

typedef enum logic {
  RVC_CALL = 1'b0,
  STD_CALL = 1'b1
} call_size_t;

logic [ICACHE_DATA_B_W/2-1: 0]    w_rvc_call_be;
logic [ICACHE_DATA_B_W/2-1: 0]    w_std_call_be;
call_size_t w_call_size_array[ICACHE_DATA_B_W/2];

logic [ICACHE_DATA_B_W/2-1: 0]    w_rvc_noncond_be;
logic [ICACHE_DATA_B_W/2-1: 0]    w_std_noncond_be;

logic [ICACHE_DATA_B_W/2-1: 0]    w_s1_call_be;
logic [ICACHE_DATA_B_W/2-1:0]     w_s1_call_be_lsb;

logic [ICACHE_DATA_B_W / 2-1: 0]  w_s1_call_valid;
logic [ICACHE_DATA_B_W / 2-1: 0]  w_s1_ret_valid;

logic [ICACHE_DATA_B_W/2-1: 0]    w_s1_ret_be;
logic [ICACHE_DATA_B_W/2-1: 0]    w_s1_ret_be_lsb;

logic [ICACHE_DATA_B_W/2-1: 0]    w_s2_call_be;
logic [ICACHE_DATA_B_W/2-1: 0]    w_s2_noncond_be;
vaddr_t                 w_s2_call_vaddr;
logic [riscv_pkg::VADDR_W-1: 1]   w_s2_ras_next_pc;
logic [ICACHE_DATA_B_W/2-1: 0]    w_s2_ret_be;
logic [riscv_pkg::VADDR_W-1: 1]   w_s2_ras_ret_vaddr;

// logic [riscv_pkg::VADDR_W-1: 1] w_sc_ras_next_pc;
// logic [riscv_pkg::VADDR_W-1: 1] w_sc_ras_ret_vaddr;

logic [ICACHE_DATA_B_W / 2-1: 0] w_s2_call_valid;
logic [ICACHE_DATA_B_W / 2-1: 0] w_s2_call_valid_oh;
logic [ICACHE_DATA_B_W / 2-1: 0] w_s2_ret_valid;
logic [ICACHE_DATA_B_W / 2-1: 0] w_s2_ret_valid_oh;

logic [31: 0]                    w_s2_inst_array_32bit[ICACHE_DATA_B_W/2];
logic [31: 0]                    w_s2_inst_array_oh;
logic [$clog2(ICACHE_DATA_B_W/2)-1: 0] w_s2_call_enc;
logic [riscv_pkg::VADDR_W-1: 1]        w_s2_call_target_vaddr;
logic [riscv_pkg::VADDR_W-1: 1]        w_s2_call_offset;
logic [riscv_pkg::VADDR_W-1: 1]        w_s2_call_pc;

// grp_id_t w_sc_grp_valid;
// grp_id_t w_sc_call_be;
// grp_id_t w_sc_ret_be;
// grp_id_t w_sc_call_valid;
// grp_id_t w_sc_ret_valid;

/* verilator lint_off UNOPTFLAT */
logic [ICACHE_DATA_B_W / 2 -1: 0] w_is_32bit_inst;

logic [scariv_conf_pkg::ICACHE_DATA_W-1: 0] w_s2_inst;
// logic [ICACHE_DATA_B_W-1: 0]              w_s2_inst_be;
assign w_s2_inst    = i_s2_ic_resp.data;
// assign w_s2_inst_be = i_s2_ic_resp.be;

logic [riscv_pkg::VADDR_W-1: $clog2(ICACHE_DATA_B_W/2)+1] r_s2_prev_upper_vaddr_p1;
logic                                                   r_is_32bit_inst_msb;
logic                                                   w_s2_call_be_msb;
logic [15: 0]                                           r_last_prev_inst_uppper_16bit;
always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_s2_prev_upper_vaddr_p1 <= 'h0;
    r_is_32bit_inst_msb <= 1'b0;
    w_s2_call_be_msb <= 1'b0;
    r_last_prev_inst_uppper_16bit <= 'h0;
  end else begin
    if (i_s2_valid & i_s2_ic_resp.valid) begin
      r_s2_prev_upper_vaddr_p1       <= i_s2_ic_resp.vaddr[riscv_pkg::VADDR_W-1: $clog2(ICACHE_DATA_B_W/2)+1] + 'h1;
      r_is_32bit_inst_msb            <= w_is_32bit_inst[ICACHE_DATA_B_W / 2 -1];
      w_s2_call_be_msb               <= w_s2_call_be   [ICACHE_DATA_B_W / 2 -1];
      r_last_prev_inst_uppper_16bit  <= i_s2_ic_resp.data[scariv_conf_pkg::ICACHE_DATA_W-1 -: 16];
    end
  end
end



generate for (genvar c_idx = 0; c_idx < ICACHE_DATA_B_W / 2; c_idx++) begin : call_loop
  // assign w_s2_inst_be[c_idx] = &(i_s2_ic_resp.be[c_idx*2 +: 2]);

  logic [15: 0] w_rvc_inst;
  logic [31: 0] w_std_inst;
  logic         is_rvc_j;
  logic         is_rvc_jal;
  logic         is_rvc_jalr;
  logic         is_rvc_jr;
  logic         rvc_call_be;
  logic         is_rvc_ret_raw;
  logic         is_std_ret_raw;
  assign w_rvc_inst = i_s2_ic_resp.data[c_idx*16 +: 16];
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
  assign w_same_prev_vaddr = r_s2_prev_upper_vaddr_p1 ==
                             i_s2_ic_resp.vaddr[riscv_pkg::VADDR_W-1: $clog2(ICACHE_DATA_B_W/2)+1];
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
    assign w_std_inst = {w_s2_inst[15: 0], r_last_prev_inst_uppper_16bit};
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
    assign w_std_inst = w_s2_inst[(c_idx+1)*16-1 -: 32];
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
  assign w_s2_inst_array_32bit[c_idx] = w_std_inst;
  assign w_std_call_be   [c_idx] = is_std_call | is_std_callr;
  assign w_std_noncond_be[c_idx] = is_std_jal  | is_std_jalr ;

  assign w_call_size_array[c_idx] = w_std_call_be[c_idx] ? STD_CALL : RVC_CALL;
  assign w_s2_call_be[c_idx] = (w_rvc_call_be[c_idx] | w_std_call_be[c_idx]) & i_s2_ic_resp.valid &
                               i_s2_ic_resp.be[c_idx * 2];

  assign w_s2_noncond_be[c_idx] = (w_rvc_noncond_be[c_idx] | w_std_noncond_be[c_idx]) & i_s2_ic_resp.valid &
                                  i_s2_ic_resp.be[c_idx * 2];
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
  assign w_s2_ret_be[c_idx] = (w_is_rvc_ret | w_is_std_ret) & i_s2_ic_resp.valid &
                              i_s2_ic_resp.be[c_idx * 2];
end // block: rvc_jal_loop
endgenerate

/* verilator lint_off WIDTH */
assign w_s1_call_be = search_btb_if.s1_is_call;
assign w_s1_ret_be  = search_btb_if.s1_is_ret;

bit_extract_lsb #(.WIDTH(ICACHE_DATA_B_W/2)) call_s1_be_lsb (.in(w_s1_call_be), .out(w_s1_call_be_lsb));
bit_extract_lsb #(.WIDTH(ICACHE_DATA_B_W/2)) ret_s1_be_lsb  (.in(w_s1_ret_be),  .out(w_s1_ret_be_lsb));

logic [$clog2(scariv_conf_pkg::RAS_ENTRY_SIZE)-1: 0] w_ras_index_next;
logic [$clog2(scariv_conf_pkg::RAS_ENTRY_SIZE)-1: 0] r_ras_input_index;
logic [$clog2(scariv_conf_pkg::RAS_ENTRY_SIZE)-1: 0] w_ras_output_index;
/* verilator lint_off UNOPTFLAT */
logic [$clog2(scariv_conf_pkg::RAS_ENTRY_SIZE)-1: 0] w_s2_ras_index_next;
logic [$clog2(scariv_conf_pkg::RAS_ENTRY_SIZE)-1: 0] w_ras_wr_index;
logic                                              w_cmt_update_ras_idx;
logic                                              w_cmt_dead_valid;

logic [ICACHE_DATA_B_W/2-1: 0]       w_s1_pred_hit_oh;

logic [$clog2(scariv_conf_pkg::RAS_ENTRY_SIZE)-1: 0] r_s2_ras_index_next;

logic                                              w_br_call_dead;
logic                                              w_br_ret_dead;
logic                                              r_during_recover;

assign w_br_call_dead = br_upd_fe_if.update & br_upd_fe_if.dead & br_upd_fe_if.is_call;
assign w_br_ret_dead  = br_upd_fe_if.update & br_upd_fe_if.dead & br_upd_fe_if.is_ret ;

always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_during_recover <= 1'b0;
  end else begin
    if (w_br_call_dead | w_br_ret_dead) begin
      r_during_recover <= 1'b1; // Enter recovering mode
    end else if (br_upd_fe_if.update & ~br_upd_fe_if.dead) begin
      r_during_recover <= 1'b0; // Leave recovering mode
    end

  end // else: !if(!i_reset_n)
end // always_ff @ (posedge i_clk, negedge i_reset_n)

logic w_ras_commit_flush;
logic w_ras_br_flush;
logic w_ras_flush_valid;
logic [scariv_conf_pkg::DISP_SIZE-1: 0] w_ras_commit_flush_valid_oh;
logic [RAS_W-1: 0]          w_ras_commit_flush_ras_index_oh;
assign w_ras_commit_flush = is_flushed_commit(i_commit) /* & |(i_commit.flush_valid & i_commit.ras_update) */;
assign w_ras_br_flush = br_upd_fe_if.update & ~br_upd_fe_if.dead & br_upd_fe_if.mispredict /* &
                        (br_upd_fe_if.is_call | br_upd_fe_if.is_ret) */;
bit_extract_lsb #(.WIDTH(scariv_conf_pkg::DISP_SIZE)) commit_flush_valid_oh (.in(i_commit.flush_valid), .out(w_ras_commit_flush_valid_oh));
bit_oh_or_packed #(.T(logic [RAS_W-1: 0]), .WORDS(scariv_conf_pkg::DISP_SIZE))
bit_oh_call_target(.i_oh(w_ras_commit_flush_valid_oh), .i_data(i_commit.ras_index), .o_selected(w_ras_commit_flush_ras_index_oh));
assign w_ras_flush_valid   = w_ras_commit_flush | w_ras_br_flush;

logic [RAS_W-1: 0]          w_flush_ras_index;
assign w_flush_ras_index = w_ras_commit_flush ? w_ras_commit_flush_ras_index_oh : br_upd_fe_if.ras_index;

always_comb begin
  w_s2_ras_index_next = r_ras_input_index;

  if (w_ras_flush_valid) begin
    w_s2_ras_index_next = w_flush_ras_index;
  // end else if (w_br_call_dead & ~r_during_recover) begin
  //   w_s2_ras_index_next = br_upd_fe_if.ras_index;
  // end else if (w_br_ret_dead & ~r_during_recover) begin
  //   w_s2_ras_index_next = br_upd_fe_if.ras_index + 'h1;
  end

  w_ras_index_next = w_s2_ras_index_next;
  if (|w_s2_ret_valid) begin
    w_ras_index_next = w_s2_ras_index_next - 'h1;
  end else if (|w_s2_call_valid) begin
    w_ras_index_next = w_s2_ras_index_next + 'h1;
  end
  w_ras_wr_index = w_ras_index_next;
end

assign w_ras_output_index = w_ras_index_next - 1;

always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_ras_input_index   <= 'h0;
    r_s2_ras_index_next <= 'h0;
  end else begin
    r_ras_input_index   <= w_ras_index_next;
    r_s2_ras_index_next <= w_s2_ras_index_next;
  end
end

// RATの各ステージにおける役割
// S0: 現在のPCからBTBを引く -> S1で結果を得る
// S1: BTBのどこかにCALL(/RETは行わない)命令が含まれていると、まずBTBで予測して予測ジャンプを行う
// S2: RETの場合はRASからPOPして予測アドレスとして使用する. 次のRETに備えてras_indexをdecrementする
// 注意: Instruction Bufferに入っている命令のフラッシュはCommit Reportによっては行われない(消える可能性がある)
//       Commit Reportか、BR Reportによってしかるべき場所までras_indexを元に戻す必要がある

assign w_s1_call_valid = {(ICACHE_DATA_B_W/2){i_s1_valid}} & (|(w_s1_call_be & w_s1_pred_hit_oh) ? w_s1_call_be : 'h0);
assign w_s1_ret_valid  = {(ICACHE_DATA_B_W/2){i_s1_valid}} & (|(w_s1_ret_be  & w_s1_pred_hit_oh) ? w_s1_ret_be  : 'h0);

logic [ICACHE_DATA_B_W/2-1: 0] w_s2_ras_be;
assign w_s2_ras_be = ({w_s2_call_valid_oh, 2'b00} - 'h1) & ({w_s2_ret_valid_oh, 2'b00} - 'h1);

assign ras_search_if.s1_is_call   = w_s1_call_be_lsb;
assign ras_search_if.s1_is_ret    = 1'b0;
assign ras_search_if.s1_ras_vaddr = 'h0;
assign ras_search_if.s1_ras_index = 'h0;

assign ras_search_if.s2_is_call           = w_s2_call_valid;
assign ras_search_if.s2_call_target_vaddr = w_s2_call_target_vaddr;
assign ras_search_if.s2_is_ret            = w_s2_ret_valid;
generate for (genvar be_idx = 0; be_idx < ICACHE_DATA_B_W / 2; be_idx++) begin : s2_be_loop
  assign ras_search_if.s2_ras_be[be_idx*2+0] = w_s2_ras_be[be_idx];
  assign ras_search_if.s2_ras_be[be_idx*2+1] = w_s2_ras_be[be_idx];
end
endgenerate
assign ras_search_if.s2_ras_vaddr         = w_s2_ras_ret_vaddr;
assign ras_search_if.s2_ras_index         = /* |w_s2_ret_valid ? w_ras_index_next : */w_s2_ras_index_next;

// assign o_sc_ras_index = w_s2_ras_index_next;
// assign o_sc_ras_vaddr = {w_sc_ras_ret_vaddr, 1'b0};

// grp_id_t w_sc_call_be_array_vld;
// disp_t w_sc_call_entry;
//
// assign w_sc_call_be_array_vld = w_sc_call_be & w_sc_grp_valid;

/* verilator lint_off WIDTH */
assign w_s2_ras_next_pc = {i_s2_ic_resp.vaddr[riscv_pkg::VADDR_W-1: $clog2(ICACHE_DATA_B_W)], {$clog2(ICACHE_DATA_B_W/2){1'b0}}} +
                          w_s2_call_enc + 'h1;

// assign w_sc_ras_next_pc = w_sc_call_entry.pc_addr[riscv_pkg::VADDR_W-1: 1] + (w_sc_call_entry.rvc_inst_valid ? 1 : 2);
//
// bit_oh_or_packed #(.T(disp_t), .WORDS(scariv_conf_pkg::DISP_SIZE))
// bit_oh_call_target(.i_oh(w_sc_call_be_array_vld), .i_data(sc_disp.inst), .o_selected(w_sc_call_entry));

scariv_pred_ras
u_ras
  (
   .i_clk (i_clk),
   .i_reset_n (i_reset_n),

   .i_wr_valid (|w_s2_call_valid),
   .i_wr_index (w_s2_ras_index_next),
   .i_wr_pa    (w_s2_ras_next_pc),

   .i_s2_rd_valid ((|w_s2_ret_valid)),
   .i_s2_rd_index (r_ras_input_index-1),
   .o_s2_rd_pa    (w_s2_ras_ret_vaddr),

   .i_br_call_cmt_valid     (w_br_call_dead & ~r_during_recover),
   .i_br_call_cmt_ras_index (br_upd_fe_if.ras_index),
   .i_br_call_cmt_wr_vpc    (br_upd_fe_if.ras_prev_vaddr[riscv_pkg::VADDR_W-1: 1])
   );


// ----------------------------------------
// Extracting Call/Ret for 1st instruction
// ----------------------------------------
bit_extract_lsb #(.WIDTH(ICACHE_DATA_B_W/2)) s1_pred_hit_select (.in(w_s1_call_be | w_s1_ret_be), .out(w_s1_pred_hit_oh));

logic [ICACHE_DATA_B_W/2-1: 0] w_s2_noncond_call_ret_be_oh;

bit_extract_lsb #(.WIDTH(ICACHE_DATA_B_W/2)) s2_pred_hit_select (.in(w_s2_noncond_be | w_s2_call_be | w_s2_ret_be), .out(w_s2_noncond_call_ret_be_oh));

assign w_s2_call_valid = {(ICACHE_DATA_B_W/2){i_s2_valid}} & w_s2_call_be & w_s2_noncond_call_ret_be_oh;
assign w_s2_ret_valid  = {(ICACHE_DATA_B_W/2){i_s2_valid}} & w_s2_ret_be  & w_s2_noncond_call_ret_be_oh;

bit_extract_lsb #(.WIDTH(ICACHE_DATA_B_W/2)) s2_call_valid_oh (.in(w_s2_call_valid), .out(w_s2_call_valid_oh));
bit_extract_lsb #(.WIDTH(ICACHE_DATA_B_W/2)) s2_ret_valid_oh  (.in(w_s2_ret_valid ), .out(w_s2_ret_valid_oh ));
bit_oh_or #(.T(logic[31: 0]), .WORDS(ICACHE_DATA_B_W/2))
s2_inst_arary_32bit_sel(.i_oh(w_s2_call_valid_oh), .i_data(w_s2_inst_array_32bit), .o_selected(w_s2_inst_array_oh));
encoder #(.SIZE(ICACHE_DATA_B_W/2)) s2_call_loc_encoder (.i_in(w_s2_call_valid_oh), .o_out(w_s2_call_enc));
assign w_s2_call_offset = $signed({{(riscv_pkg::VADDR_W-11){w_s2_inst_array_oh[31]}}, w_s2_inst_array_oh[31], w_s2_inst_array_oh[19:12], w_s2_inst_array_oh[20], w_s2_inst_array_oh[30:21]});
assign w_s2_call_pc     = {i_s2_ic_resp.vaddr[riscv_pkg::VADDR_W-1: $clog2(ICACHE_DATA_B_W/2)+1], {$clog2(ICACHE_DATA_B_W/2){1'b0}}};
assign w_s2_call_target_vaddr = w_s2_call_offset + w_s2_call_pc + w_s2_call_enc - 1;


// -----------------
// GShare Predictor
// -----------------

scariv_gshare
u_gshare
  (
   .i_clk     (i_clk),
   .i_reset_n (i_reset_n),

   .search_btb_if    (search_btb_if   ),
   .gshare_search_if (gshare_search_if),
   .br_upd_fe_if     (br_upd_fe_if    ),

   .o_s2_predict_valid        (o_s2_predict_valid       ),
   .o_s2_predict_target_vaddr (o_s2_predict_target_vaddr)
   );




`ifdef SIMULATION
logic [$clog2(scariv_conf_pkg::RAS_ENTRY_SIZE)-1: 0] r_committed_ras_index;
logic [$clog2(scariv_conf_pkg::RAS_ENTRY_SIZE)-1: 0] w_committed_ras_index_m1;
assign w_committed_ras_index_m1 = r_committed_ras_index - 1;
always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_committed_ras_index <= 'h0;
  end else begin
    if (w_ras_flush_valid) begin
      r_committed_ras_index <= w_flush_ras_index;
    end else if (br_upd_fe_if.update & !br_upd_fe_if.dead & br_upd_fe_if.is_call) begin
      if (r_committed_ras_index != br_upd_fe_if.ras_index) begin
        $display ("CALL : expected ras_index different. Expectd=%0d, RTL=%0d",
                  r_committed_ras_index, br_upd_fe_if.ras_index);
        $fatal;
      end else begin
        r_committed_ras_index <= r_committed_ras_index + 'h1;
      end
    end else if (br_upd_fe_if.update & !br_upd_fe_if.dead & br_upd_fe_if.is_ret) begin
      if (w_committed_ras_index_m1 != br_upd_fe_if.ras_index) begin
        $display("RET : expected ras_index different. Expectd=%0d, RTL=%0d",
                 w_committed_ras_index_m1, br_upd_fe_if.ras_index);
        $fatal;
      end else begin
        r_committed_ras_index <= w_committed_ras_index_m1;
      end
    end
  end // else: !if(!i_reset_n)
end // always_ff @ (posedge i_clk, negedge i_reset_n)
`endif // SIMULATION

endmodule // scariv_predictor

// `default_nettype wire
