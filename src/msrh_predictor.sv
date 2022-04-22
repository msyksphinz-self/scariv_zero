// ------------------------------------------------------------------------
// NAME : MRSH Predictor
// TYPE : module
// ------------------------------------------------------------------------
// It includes all variations of predictors for MSRH
// ------------------------------------------------------------------------
//
// ------------------------------------------------------------------------

// `default_nettype none

module msrh_predictor
  import msrh_predict_pkg::*;
  import msrh_lsu_pkg::*;
(
 input logic  i_clk,
 input logic  i_reset_n,

 // disp_if.watch     sc_disp,
 // output logic [$clog2(msrh_conf_pkg::RAS_ENTRY_SIZE)-1: 0] o_sc_ras_index,
 // output msrh_pkg::vaddr_t                    o_sc_ras_vaddr,

 input logic i_s1_valid,
 input logic i_s2_valid,
 input msrh_lsu_pkg::ic_resp_t i_s2_ic_resp,

 btb_update_if.slave update_btb_if,
 btb_search_if.slave search_btb_if,
 output msrh_pkg::vaddr_t o_s1_btb_target_vaddr,

 bim_update_if.slave update_bim_if,
 bim_search_if.slave search_bim_if,

 ras_search_if.master ras_search_if,

 br_upd_if.slave  br_upd_fe_if
 );

logic [ICACHE_DATA_B_W/2-1: 0] w_s1_btb_hit_oh;

msrh_btb u_btb
  (
   .i_clk(i_clk),
   .i_reset_n(i_reset_n),

   .update_btb_if (update_btb_if),
   .search_btb_if (search_btb_if),

   .o_s1_btb_hit_oh (w_s1_btb_hit_oh)
   );

msrh_bim u_bim
  (
   .i_clk    (i_clk),
   .i_reset_n(i_reset_n),

   .update_bim_if (update_bim_if),
   .search_bim_if (search_bim_if),

   .i_s1_btb_hit_oh (w_s1_btb_hit_oh)
   );

typedef enum logic {
  RVC_CALL = 1'b0,
  STD_CALL = 1'b1
} call_size_t;

logic [ICACHE_DATA_B_W/2-1: 0]    w_rvc_call_be;
logic [ICACHE_DATA_B_W/2-1: 0]    w_std_call_be;
call_size_t w_call_size_array[ICACHE_DATA_B_W/2];

logic [ICACHE_DATA_B_W/2-1: 0]    w_s1_call_be;
logic [ICACHE_DATA_B_W/2-1:0]     w_s1_call_be_lsb;

logic [ICACHE_DATA_B_W / 2-1: 0]  w_s1_call_valid;
logic [ICACHE_DATA_B_W / 2-1: 0]  w_s1_ret_valid;

logic [ICACHE_DATA_B_W/2-1: 0]    w_s1_ret_be;
logic [ICACHE_DATA_B_W/2-1: 0]    w_s1_ret_be_lsb;

logic [ICACHE_DATA_B_W/2-1: 0]    w_s2_call_be;
msrh_pkg::vaddr_t                 w_s2_call_vaddr;
logic [riscv_pkg::VADDR_W-1: 1]   w_s2_ras_next_pc;
logic [ICACHE_DATA_B_W/2-1: 0]    w_s2_ret_be;
logic [riscv_pkg::VADDR_W-1: 1]   w_s2_ras_ret_vaddr;

// logic [riscv_pkg::VADDR_W-1: 1] w_sc_ras_next_pc;
// logic [riscv_pkg::VADDR_W-1: 1] w_sc_ras_ret_vaddr;

logic [ICACHE_DATA_B_W / 2-1: 0] w_s2_call_valid;
logic [ICACHE_DATA_B_W / 2-1: 0] w_s2_call_valid_oh;
logic [ICACHE_DATA_B_W / 2-1: 0] w_s2_ret_valid;

logic [31: 0]                    w_s2_inst_array_32bit[ICACHE_DATA_B_W/2];
logic [31: 0]                    w_s2_inst_array_oh;
logic [$clog2(ICACHE_DATA_B_W/2)-1: 0] w_s2_call_enc;
logic [riscv_pkg::VADDR_W-1: 1]        w_s2_call_target_vaddr;
logic [riscv_pkg::VADDR_W-1: 1]        w_s2_call_offset;

// msrh_pkg::grp_id_t w_sc_grp_valid;
// msrh_pkg::grp_id_t w_sc_call_be;
// msrh_pkg::grp_id_t w_sc_ret_be;
// msrh_pkg::grp_id_t w_sc_call_valid;
// msrh_pkg::grp_id_t w_sc_ret_valid;

logic [ICACHE_DATA_B_W / 2 -1: 0] w_is_32bit_inst;

logic [msrh_conf_pkg::ICACHE_DATA_W-1: 0] w_s2_inst;
// logic [ICACHE_DATA_B_W-1: 0]              w_s2_inst_be;
assign w_s2_inst    = i_s2_ic_resp.data;
// assign w_s2_inst_be = i_s2_ic_resp.be;

logic [riscv_pkg::VADDR_W-1: $clog2(ICACHE_DATA_B_W/2)] r_s2_prev_upper_vaddr_p1;
logic                                                   r_is_32bit_inst_msb;
logic                                                   w_s2_call_be_msb;
always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_s2_prev_upper_vaddr_p1 <= 'h0;
    r_is_32bit_inst_msb <= 1'b0;
    w_s2_call_be_msb <= 1'b0;
  end else begin
    if (i_s2_valid & i_s2_ic_resp.valid) begin
      r_s2_prev_upper_vaddr_p1 <= i_s2_ic_resp.vaddr[riscv_pkg::VADDR_W-1: $clog2(ICACHE_DATA_B_W/2)] + 'h1;
      r_is_32bit_inst_msb <= w_is_32bit_inst[ICACHE_DATA_B_W / 2 -1];
      w_s2_call_be_msb <= w_s2_call_be[ICACHE_DATA_B_W / 2 -1];
    end
  end
end



generate for (genvar c_idx = 0; c_idx < ICACHE_DATA_B_W / 2; c_idx++) begin : call_loop
  // assign w_s2_inst_be[c_idx] = &(i_s2_ic_resp.be[c_idx*2 +: 2]);

  logic [15: 0] w_rvc_inst;
  logic         is_rvc_jal;
  // logic         is_rvc_jalr;
  logic         rvc_call_be;
  assign w_rvc_inst = i_s2_ic_resp.data[c_idx*16 +: 16];
`ifdef RV32
  assign is_rvc_jal = (w_rvc_inst[1:0] == 2'b01) &
                      (w_rvc_inst[15:13] == 3'b001);
`else // RV32
  assign is_rvc_jal = 'b0;
`endif // RV32
  logic           w_same_prev_vaddr;
  assign w_same_prev_vaddr = r_s2_prev_upper_vaddr_p1 ==
                             i_s2_ic_resp.vaddr[riscv_pkg::VADDR_W-1: $clog2(ICACHE_DATA_B_W/2)];
  if (c_idx == 0) begin
    assign w_is_32bit_inst [c_idx] = (w_rvc_inst[1:0] == 2'b11) & w_same_prev_vaddr & !r_is_32bit_inst_msb;
  end else begin
    assign w_is_32bit_inst [c_idx] = (w_rvc_inst[1:0] == 2'b11);
  end
  // assign is_rvc_jalr = (w_rvc_inst[1:0] == 2'b10) &
  //                      (w_rvc_inst[15:12] == 4'b1001) &
  //                      (w_rvc_inst[11: 7] != 5'h0) &
  //                      (w_rvc_inst[ 6: 2] == 5'h0);
  assign w_rvc_call_be[c_idx] = is_rvc_jal & !w_is_32bit_inst[c_idx-1];

  logic [31: 0]   w_std_inst;
  logic           is_std_jal;
  logic           is_std_jalr;
  /* verilator lint_off SELRANGE */
  if (c_idx == (ICACHE_DATA_B_W / 2)-1) begin
    assign w_std_inst = {16'h0000, w_s2_inst[c_idx*16 +: 16]};
    assign is_std_jal = (w_std_inst[11:7] == 5'h1) & (w_std_inst[ 6:0] == 7'b1101111);
  end else begin
    assign w_std_inst = w_s2_inst[c_idx*16 +: 32];
    assign is_std_jal = (w_std_inst[11:7] == 5'h1) & (w_std_inst[ 6:0] == 7'b1101111);
  end
  assign w_std_call_be[c_idx] = is_std_jal;

  assign w_call_size_array[c_idx] = w_std_call_be[c_idx] ? STD_CALL : RVC_CALL;
  assign w_s2_call_be[c_idx] = (w_rvc_call_be[c_idx] | w_std_call_be[c_idx]) & i_s2_ic_resp.valid &
                               i_s2_ic_resp.be[c_idx * 2];


  // --------------------------
  // Decode RET (JALR X0,X1,0)
  // --------------------------
  logic             w_is_rvc_ret;
  logic             w_is_std_ret;
  if (c_idx != 0) begin
    assign w_is_rvc_ret = !w_is_32bit_inst[c_idx-1] & (w_rvc_inst == 16'h8082);
    assign w_is_std_ret = !w_is_32bit_inst[c_idx-1] & (w_std_inst == 32'h00008067);
  end else begin
    assign w_is_rvc_ret = w_same_prev_vaddr & !r_is_32bit_inst_msb & (w_rvc_inst == 16'h8082);
    assign w_is_std_ret = w_same_prev_vaddr & !r_is_32bit_inst_msb & (w_std_inst == 32'h00008067);
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

logic [$clog2(msrh_conf_pkg::RAS_ENTRY_SIZE)-1: 0] w_ras_index_next;
logic [$clog2(msrh_conf_pkg::RAS_ENTRY_SIZE)-1: 0] r_ras_input_index;
logic [$clog2(msrh_conf_pkg::RAS_ENTRY_SIZE)-1: 0] w_ras_output_index;
/* verilator lint_off UNOPTFLAT */
logic [$clog2(msrh_conf_pkg::RAS_ENTRY_SIZE)-1: 0] w_s2_ras_index_next;
logic [$clog2(msrh_conf_pkg::RAS_ENTRY_SIZE)-1: 0] w_ras_wr_index;
logic                                              w_cmt_update_ras_idx;
logic                                              w_cmt_dead_valid;

logic [msrh_lsu_pkg::ICACHE_DATA_B_W/2-1: 0]       w_s1_pred_hit_oh;

logic [msrh_lsu_pkg::ICACHE_DATA_B_W/2-1: 0]       w_s1_btb_bim_hit_array;
logic [msrh_lsu_pkg::ICACHE_DATA_B_W/2-1: 0]       w_s1_btb_bim_hit_lsb;


logic [$clog2(msrh_conf_pkg::RAS_ENTRY_SIZE)-1: 0] r_s2_ras_index_next;

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

always_comb begin
  w_s2_ras_index_next = r_ras_input_index;

  if (w_br_call_dead & ~r_during_recover) begin
    w_s2_ras_index_next = br_upd_fe_if.ras_index;
  end else if (w_br_ret_dead & ~r_during_recover) begin
    w_s2_ras_index_next = br_upd_fe_if.ras_index + 'h1;
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

assign ras_search_if.s1_is_call   = w_s1_call_be_lsb;
assign ras_search_if.s1_is_ret    = 1'b0;
assign ras_search_if.s1_ras_vaddr = 'h0;
assign ras_search_if.s1_ras_index = 'h0;

assign ras_search_if.s2_is_call           = w_s2_call_valid;
assign ras_search_if.s2_call_target_vaddr = w_s2_call_target_vaddr;
assign ras_search_if.s2_is_ret            = w_s2_ret_valid;
assign ras_search_if.s2_ras_vaddr         = w_s2_ras_ret_vaddr;
assign ras_search_if.s2_ras_index         = |w_s2_ret_valid ? w_ras_index_next : w_s2_ras_index_next;

// assign o_sc_ras_index = w_s2_ras_index_next;
// assign o_sc_ras_vaddr = {w_sc_ras_ret_vaddr, 1'b0};

// msrh_pkg::grp_id_t w_sc_call_be_array_vld;
// msrh_pkg::disp_t w_sc_call_entry;
//
// assign w_sc_call_be_array_vld = w_sc_call_be & w_sc_grp_valid;

/* verilator lint_off WIDTH */
assign w_s2_ras_next_pc = {i_s2_ic_resp.vaddr[riscv_pkg::VADDR_W-1: $clog2(msrh_lsu_pkg::ICACHE_DATA_B_W)], {$clog2(msrh_lsu_pkg::ICACHE_DATA_B_W/2){1'b0}}} +
                          w_s2_call_enc + 'h2;

// assign w_sc_ras_next_pc = w_sc_call_entry.pc_addr[riscv_pkg::VADDR_W-1: 1] + (w_sc_call_entry.rvc_inst_valid ? 1 : 2);
//
// bit_oh_or_packed #(.T(msrh_pkg::disp_t), .WORDS(msrh_conf_pkg::DISP_SIZE))
// bit_oh_call_target(.i_oh(w_sc_call_be_array_vld), .i_data(sc_disp.inst), .o_selected(w_sc_call_entry));

msrh_pred_ras
u_ras
  (
   .i_clk (i_clk),
   .i_reset_n (i_reset_n),

   .i_wr_valid (|w_s2_call_valid),
   .i_wr_index (w_s2_ras_index_next),
   .i_wr_pa    (w_s2_ras_next_pc),

   // .i_sc_rd_valid (|(w_sc_ret_valid | w_sc_call_valid)),
   // .i_sc_rd_index (|w_sc_ret_valid ? w_ras_index_next : w_sc_call_entry.ras_index),
   // .o_sc_rd_pa    (w_sc_ras_ret_vaddr),

   .i_sc_rd_valid (1'b0),
   .i_sc_rd_index ('h0),
   .o_sc_rd_pa    (),

   .i_s1_rd_valid ((|w_s2_ret_valid)),
   .i_s1_rd_index (r_ras_input_index-1),
   .o_s1_rd_pa    (w_s2_ras_ret_vaddr),

   .i_br_call_cmt_valid     (w_br_call_dead & ~r_during_recover),
   .i_br_call_cmt_ras_index (br_upd_fe_if.ras_index),
   .i_br_call_cmt_wr_vpc    (br_upd_fe_if.ras_prev_vaddr[riscv_pkg::VADDR_W-1: 1])
   );

// `ifdef SIMULATION
// function void dump_json(int fp);
//   $fwrite(fp, "  \"msrh_predictor\" : {\n");
//
//   if (w_cmt_update_ras_idx) begin
//     $fwrite(fp, "    r_ras_input_index : \"%d\",\n", i_s0_req.valid);
//     $fwrite(fp, "    i_s0_req.vaddr : \"0x%x\",\n", i_s0_req.vaddr);
//   end
//   // $fwrite(fp, "    state : \"%d\",\n", r_ic_state);
//   if (r_s1_valid) begin
//     for(int way = 0; way < msrh_conf_pkg::ICACHE_WAYS; way++) begin
//       $fwrite(fp, "    \"w_s1_tag_hit[%1d]\" : \"%d\",\n", way, w_s1_tag_hit[way]);
//     end
//   end
//   if (r_s2_valid) begin
//     $fwrite(fp, "    o_s2_miss : \"%d\",\n", o_s2_miss);
//     $fwrite(fp, "    o_s2_miss_vaddr : \"0x%x\",\n", o_s2_miss_vaddr);
//   end
//   if (ic_l2_req.valid) begin
//     $fwrite(fp, "    \"ic_l2_req\" : {\n");
//     $fwrite(fp, "      valid : \"%d\",\n", ic_l2_req.valid);
//     $fwrite(fp, "      cmd : \"%d\",\n", ic_l2_req.payload.cmd);
//     $fwrite(fp, "      addr : \"0x%x\",\n", ic_l2_req.payload.addr);
//     $fwrite(fp, "      tag : \"%d\",\n", ic_l2_req.payload.tag);
//     $fwrite(fp, "    },\n");
//   end
//
//   if (o_s2_resp.valid) begin
//     $fwrite(fp, "    \"o_s2_resp\" : {\n");
//     $fwrite(fp, "      valid : \"%d\",\n", o_s2_resp.valid);
//     $fwrite(fp, "      data : \"%x\",\n",  o_s2_resp.data);
//     $fwrite(fp, "      miss : \"%d\",\n",  o_s2_miss);
//     $fwrite(fp, "      vaddr : \"0x%x\",\n", o_s2_miss_vaddr);
//     $fwrite(fp, "    },\n");
//   end
//
//   $fwrite(fp, "  },\n");
// endfunction // dump



logic [msrh_lsu_pkg::ICACHE_DATA_B_W/2-1: 0] r_s2_pred_hit_oh;
logic [msrh_lsu_pkg::ICACHE_DATA_B_W/2-1: 0] w_s2_pred_hit_oh;
always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_s2_pred_hit_oh <= 'h0;
  end else begin
    r_s2_pred_hit_oh <= w_s1_pred_hit_oh;
  end
end


// ----------------------------------------
// Extracting Call/Ret for 1st instruction
// ----------------------------------------
assign w_s1_btb_bim_hit_array = search_btb_if.s1_hit & search_bim_if.s1_pred_taken;

bit_extract_lsb #(.WIDTH(msrh_lsu_pkg::ICACHE_DATA_B_W/2)) s1_pred_hit_select (.in(w_s1_btb_bim_hit_array | w_s1_call_be | w_s1_ret_be), .out(w_s1_pred_hit_oh));

bit_extract_lsb #(.WIDTH(msrh_lsu_pkg::ICACHE_DATA_B_W/2)) btb_hit_lsb (.in(w_s1_btb_bim_hit_array), .out(w_s1_btb_bim_hit_lsb));
bit_oh_or_packed #(.T(logic[riscv_pkg::VADDR_W-1:0]), .WORDS(msrh_lsu_pkg::ICACHE_DATA_B_W/2))
bit_oh_target_vaddr(.i_oh(w_s1_btb_bim_hit_lsb), .i_data(search_btb_if.s1_target_vaddr), .o_selected(o_s1_btb_target_vaddr));

bit_extract_lsb #(.WIDTH(msrh_lsu_pkg::ICACHE_DATA_B_W/2)) s2_pred_hit_select (.in(r_s2_pred_hit_oh | w_s2_call_be | w_s2_ret_be), .out(w_s2_pred_hit_oh));

// assign w_s2_call_valid = {(ICACHE_DATA_B_W/2){i_s2_valid}} & (|(w_s2_call_be & w_s2_pred_hit_oh) ? w_s2_call_be : 'h0);
assign w_s2_call_valid = {(ICACHE_DATA_B_W/2){i_s2_valid}} & w_s2_call_be;
assign w_s2_ret_valid  = {(ICACHE_DATA_B_W/2){i_s2_valid}} & (|(w_s2_ret_be  & w_s2_pred_hit_oh) ? w_s2_ret_be  : 'h0);

generate for (genvar d_idx = 0; d_idx < ICACHE_DATA_B_W/2; d_idx++) begin : inst_array_32bit_loop
  if (d_idx == ICACHE_DATA_B_W/2-1) begin
    assign w_s2_inst_array_32bit[d_idx] = {16'b0, w_s2_inst[d_idx*16 +: 16]};
  end else begin
    assign w_s2_inst_array_32bit[d_idx] = w_s2_inst[d_idx*16 +: 32];
  end
end
endgenerate

bit_extract_lsb #(.WIDTH(msrh_lsu_pkg::ICACHE_DATA_B_W/2)) s2_call_valid_oh (.in(w_s2_call_valid & w_s2_call_be), .out(w_s2_call_valid_oh));
bit_oh_or #(.T(logic[31: 0]), .WORDS(msrh_lsu_pkg::ICACHE_DATA_B_W/2))
s2_inst_arary_32bit_sel(.i_oh(w_s2_call_valid_oh), .i_data(w_s2_inst_array_32bit), .o_selected(w_s2_inst_array_oh));
encoder #(.SIZE(msrh_lsu_pkg::ICACHE_DATA_B_W/2)) s2_call_loc_encoder (.i_in(w_s2_call_valid_oh), .o_out(w_s2_call_enc));
assign w_s2_call_offset = {{(riscv_pkg::VADDR_W-11){w_s2_inst_array_oh[31]}}, w_s2_inst_array_oh[31], w_s2_inst_array_oh[19:12], w_s2_inst_array_oh[20], w_s2_inst_array_oh[30:21]};
assign w_s2_call_target_vaddr = w_s2_call_offset +
                                {i_s2_ic_resp.vaddr[riscv_pkg::VADDR_W-1: $clog2(msrh_lsu_pkg::ICACHE_DATA_B_W)], {$clog2(msrh_lsu_pkg::ICACHE_DATA_B_W/2){1'b0}}} +
                                w_s2_call_enc;

// generate for (genvar d_idx = 0; d_idx < msrh_conf_pkg::DISP_SIZE; d_idx++) begin : sc_disp_loop
//   assign w_sc_grp_valid[d_idx] = sc_disp.inst[d_idx].valid;
//   assign w_sc_call_be  [d_idx] = sc_disp.inst[d_idx].is_call;
//   assign w_sc_ret_be   [d_idx] = sc_disp.inst[d_idx].is_ret;
// end
// endgenerate
//
// assign w_sc_call_valid = sc_disp.valid & sc_disp.ready & |(w_sc_call_be & w_sc_grp_valid);
// assign w_sc_ret_valid  = sc_disp.valid & sc_disp.ready & |(w_sc_ret_be  & w_sc_grp_valid);


`ifdef SIMULATION
logic  [$clog2(msrh_conf_pkg::RAS_ENTRY_SIZE)-1: 0] r_committed_ras_index;
always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_committed_ras_index <= 'h0;
  end else begin
    if (br_upd_fe_if.update & !br_upd_fe_if.dead & br_upd_fe_if.is_call) begin
      if (r_committed_ras_index != br_upd_fe_if.ras_index) begin
        $fatal (0, "CALL : expected ras_index different. Expectd=%0d, RTL=%0d\n",
                r_committed_ras_index, br_upd_fe_if.ras_index);
      end else begin
        r_committed_ras_index <= r_committed_ras_index + 'h1;
      end
    end
    if (br_upd_fe_if.update & !br_upd_fe_if.dead & br_upd_fe_if.is_ret) begin
      if (r_committed_ras_index-1 != br_upd_fe_if.ras_index) begin
        $fatal (0, "RET : expected ras_index different. Expectd=%0d, RTL=%0d\n",
                r_committed_ras_index-1, br_upd_fe_if.ras_index);
      end else begin
        r_committed_ras_index <= r_committed_ras_index - 'h1;
      end
    end
  end // else: !if(!i_reset_n)
end // always_ff @ (posedge i_clk, negedge i_reset_n)
`endif // SIMULATION

endmodule // msrh_predictor

// `default_nettype wire
