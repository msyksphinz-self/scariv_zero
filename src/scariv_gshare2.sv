// ------------------------------------------------------------------------
// NAME : scariv_gshare
// TYPE : module
// ------------------------------------------------------------------------
// GShare Predictor
// ------------------------------------------------------------------------
//
// ------------------------------------------------------------------------

module scariv_gshare
  import scariv_pkg::*;
  import scariv_predict_pkg::*;
(
 input logic  i_clk,
 input logic  i_reset_n,

 input logic i_f1_valid,
 input logic i_f2_valid,

 // BRU dispatch valid
 input scariv_pkg::grp_id_t i_bru_disp_valid,
 scariv_front_if.watch      bru_disp_if,

 br_upd_if.slave br_upd_if,

 btb_search_if.monitor  search_btb_if,
 gshare_search_if.slave gshare_search_if,

 // Feedback into Frontend
 output logic   o_f2_predict_valid,
 output vaddr_t o_f2_predict_target_vaddr
 );

localparam IC_HWORD_LANE_W = scariv_lsu_pkg::ICACHE_DATA_B_W / 2;

gshare_hist_len_t  r_ghr;      // Branch History Register : 1=Taken / 0:NonTaken
gshare_hist_len_t  w_ghr_next; // Branch History Register : 1=Taken / 0:NonTaken

//
// F0 stage
//
logic [IC_HWORD_LANE_W-1 : 0] w_f0_pc_vaddr_mask;

//
// F1 stage
//
logic   r_f1_valid;
logic   r_f1_clear;
/* verilator lint_off UNOPTFLAT */
gshare_hist_len_t  w_f1_ghr_lane_next[IC_HWORD_LANE_W-1 : 0];

scariv_ic_pkg::ic_block_t w_f1_lane_predict;
scariv_ic_pkg::ic_block_t r_f1_pc_vaddr_mask;
scariv_ic_pkg::ic_block_t w_f1_cond_hit_valid;
scariv_ic_pkg::ic_block_t w_f1_cond_hit_active;

scariv_ic_pkg::ic_block_t w_f1_noncond_hit_valid;

logic         w_f1_update_ghr;

//
// F2 stage
//
logic                     r_f2_update_ghr;
gshare_hist_len_t         r_f2_ghr_lane_last;
scariv_ic_pkg::ic_block_t w_f2_predict_taken;
scariv_ic_pkg::ic_block_t w_f2_predict_taken_oh;
vaddr_t                   w_f2_btb_target_vaddr;
logic                     r_f2_clear;

//
// Dispattch
//
scariv_pkg::grp_id_t w_disp_noncond_match;
scariv_pkg::disp_t   w_disp[scariv_conf_pkg::DISP_SIZE];
scariv_pkg::disp_t   w_disp_noncond_oh;

//
// Br-Update
//
logic              w_br_upd_cond_rollback_valid;
gshare_hist_len_t  w_br_upd_cond_rollback_ghr;
logic              w_br_upd_noncond_rollback_valid;
gshare_hist_len_t  w_br_upd_noncond_rollback_ghr;

assign w_br_upd_cond_rollback_valid = br_upd_if.update & !br_upd_if.dead & br_upd_if.is_cond & ~br_upd_if.btb_not_hit & br_upd_if.mispredict;
assign w_br_upd_cond_rollback_ghr   = {r_gshare_info[br_upd_if.brtag].ghr[GSHARE_HIST_LEN-1:1], br_upd_if.taken};

assign w_br_upd_noncond_rollback_valid = br_upd_if.update & !br_upd_if.dead & !br_upd_if.is_cond & br_upd_if.mispredict;
assign w_br_upd_noncond_rollback_ghr   = r_gshare_info[br_upd_if.brtag].ghr;

assign w_ghr_next = w_br_upd_cond_rollback_valid    ? w_br_upd_cond_rollback_ghr    :
                    w_br_upd_noncond_rollback_valid ? w_br_upd_noncond_rollback_ghr :
                    // |w_disp_noncond_match           ? w_disp_noncond_oh.gshare_bhr  :
                    w_f1_update_ghr & i_f1_valid    ? w_f1_ghr_lane_next[IC_HWORD_LANE_W-1] : // If Branch existed but not predicted (in frontend GHR not updated), update GHR
                    r_ghr;

                    // r_f2_update_ghr & i_f2_valid    ? r_f2_ghr_lane_last            : // If Branch existed but not predicted (in frontend GHR not updated), update GHR

// --------------------------------
// F0 stage
// --------------------------------
assign w_f0_pc_vaddr_mask = ~((1 << gshare_search_if.f0_pc_vaddr[$clog2(scariv_lsu_pkg::ICACHE_DATA_B_W)-1: 1]) - 1);

// --------------------------------
// F1 stage
// --------------------------------

always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_f1_valid         <= 1'b0;
    r_f1_pc_vaddr_mask <= 'h0;
  end else begin
    r_f1_valid         <= gshare_search_if.f0_valid;
    r_f1_pc_vaddr_mask <= w_f0_pc_vaddr_mask;
  end
end

assign w_f1_cond_hit_valid    = (r_f1_clear | r_f2_clear) ? 'h0 : search_btb_if.f1_hit & search_btb_if.f1_is_cond & r_f1_pc_vaddr_mask;
assign w_f1_noncond_hit_valid = search_btb_if.f1_hit & (search_btb_if.f1_is_call | search_btb_if.f1_is_ret | search_btb_if.f1_is_noncond) & r_f1_pc_vaddr_mask;
assign w_f1_update_ghr        = r_f1_valid & i_f1_valid & |w_f1_cond_hit_valid;

// --------------------------------
// F2 stage
// --------------------------------

always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_f2_update_ghr           <= 1'b0;
    gshare_search_if.f2_valid <= 1'b0;
  end else begin
    r_f2_update_ghr           <= w_f1_update_ghr;
    r_f2_ghr_lane_last        <= w_f1_update_ghr ? w_f1_ghr_lane_next[IC_HWORD_LANE_W-1] :
                                 r_ghr;
    r_f2_clear    <= |w_f1_noncond_hit_valid;
    r_f1_clear    <= r_f2_clear; // roll back
    gshare_search_if.f2_valid <= r_f1_valid & i_f1_valid;
  end
end

// --------------------------------
// GHR stage
// --------------------------------
always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_ghr <= {GSHARE_HIST_LEN{1'b0}};
  end else begin
    r_ghr <= w_ghr_next;
  end
end



// --------------------------------
// Update by BR-Update
// --------------------------------
logic [ 1: 0] w_br_update_bim;
assign w_br_update_bim =  (((br_upd_if.bim_value == 2'b11) & !br_upd_if.mispredict &  br_upd_if.taken |
                             (br_upd_if.bim_value == 2'b00) & !br_upd_if.mispredict & !br_upd_if.taken)) ? br_upd_if.bim_value :
                           br_upd_if.taken ? br_upd_if.bim_value + 2'b01 :
                           br_upd_if.bim_value - 2'b01;

logic [$clog2(scariv_lsu_pkg::ICACHE_DATA_B_W/2)-1: 0] br_update_lane;
assign br_update_lane = br_upd_if.is_rvc ? br_upd_if.pc_vaddr[$clog2(scariv_lsu_pkg::ICACHE_DATA_B_W)-1: 1] :
                        br_upd_if.pc_vaddr[$clog2(scariv_lsu_pkg::ICACHE_DATA_B_W)-1: 1] + 'h1;
gshare_hist_len_t w_br_upd_index_raw;
gshare_bht_t      w_br_upd_xor_index;
assign w_br_upd_xor_index = r_gshare_info[br_upd_if.brtag].bhr_index;


generate for (genvar c_idx = 0; c_idx < scariv_lsu_pkg::ICACHE_DATA_B_W/2; c_idx++) begin : ghr_loop

  logic [ 1: 0] w_f1_bim_counter;
  logic [ 1: 0] r_f1_bim_counter_dram;
  gshare_bht_t       r_f1_xor_rd_index;

  // ---------------
  // F0 stage
  // ---------------
  gshare_hist_len_t  w_f0_xor_rd_index_raw;
  gshare_bht_t       w_f0_xor_rd_index;
  gshare_hist_len_t  w_f0_pc_vaddr_lane;
  assign w_f0_pc_vaddr_lane = {gshare_search_if.f0_pc_vaddr[riscv_pkg::VADDR_W-1:$clog2(scariv_lsu_pkg::ICACHE_DATA_B_W)], c_idx[$clog2(IC_HWORD_LANE_W)-1:0], 1'b0};
  if (c_idx == 0) begin
    assign w_f0_xor_rd_index_raw = r_f2_ghr_lane_last          ^ w_f0_pc_vaddr_lane;
  end else begin
    assign w_f0_xor_rd_index_raw = w_f1_ghr_lane_next[c_idx-1] ^ w_f0_pc_vaddr_lane;
  end
  assign w_f0_xor_rd_index     = fold_hash_index(w_f0_xor_rd_index_raw);

  // ---------------
  // F1 stage
  // ---------------
  assign w_f1_lane_predict     [c_idx] = w_f1_cond_hit_valid[c_idx] ? w_f1_bim_counter[1] : 1'b0;

  if (c_idx == 0) begin
    assign w_f1_cond_hit_active[c_idx] = w_f1_cond_hit_valid [c_idx];
    assign w_f1_ghr_lane_next  [c_idx] = w_f1_cond_hit_active[c_idx] ? {r_f2_ghr_lane_last, w_f1_lane_predict[c_idx]} :
                                         r_f2_ghr_lane_last;
  end else begin
    assign w_f1_cond_hit_active[c_idx] = w_f1_cond_hit_valid [c_idx] & ~(|w_f1_noncond_hit_valid[c_idx-1: 0]);
    assign w_f1_ghr_lane_next  [c_idx] = w_f1_cond_hit_active[c_idx] & ~|w_f1_lane_predict[c_idx-1: 0] ?
                                         {w_f1_ghr_lane_next[c_idx-1], w_f1_lane_predict[c_idx]} : w_f1_ghr_lane_next[c_idx-1];
  end

  // --------------
  // F2 stage
  // --------------
  assign w_f2_predict_taken[c_idx] = gshare_search_if.f2_bim_value[c_idx][1] & search_btb_if.f2_hit[c_idx];

  // data_array_2p
  //   #(
  //     .WIDTH (2),
  //     .ADDR_W (scariv_pkg::GSHARE_BHT_W)
  //     )
  // bim_array
  //   (
  //    .i_clk     (i_clk),
  //    .i_reset_n (i_reset_n),
  //
  //    .i_wr      (br_upd_if.update & !br_upd_if.dead),
  //    .i_wr_addr (br_upd_if.gshare_index),
  //    .i_wr_data (w_br_update_bim),
  //
  //    .i_rd_addr (w_f0_xor_rd_index),
  //    .o_rd_data (w_f1_bim_counter_dram)
  //    );

  logic br_update_lane_hit;
  assign br_update_lane_hit = br_update_lane == c_idx;

  logic [ 1: 0]   w_bim_array [2 ** scariv_pkg::GSHARE_BHT_W];
  for (genvar a_idx = 0; a_idx < 2 ** scariv_pkg::GSHARE_BHT_W; a_idx++) begin : bim_loop
    logic [ 1: 0]   r_bim;
    always_ff @ (posedge i_clk, negedge i_reset_n) begin
      if (!i_reset_n) begin
        r_bim <= 2'b10;
      end else begin
        if (br_upd_if.update & !br_upd_if.dead &
            br_update_lane_hit &
            (w_br_upd_xor_index == a_idx)) begin
          r_bim <= w_br_update_bim;
        end
      end
    end
    assign w_bim_array[a_idx] = r_bim;
  end // block: bim_loop

  always_ff @ (posedge i_clk, negedge i_reset_n) begin
    if (!i_reset_n) begin
      r_f1_bim_counter_dram <= 'h0;
    end else begin
      r_f1_bim_counter_dram <= w_bim_array[w_f0_xor_rd_index];
    end
  end

  assign w_f1_bim_counter = br_upd_if.update & !br_upd_if.dead &
                            (br_upd_if.gshare_index == w_f0_xor_rd_index) ? w_br_update_bim :
                            r_f1_bim_counter_dram;

  // Data SRAM is not formatted.
  // First access, default is set to TAKEN.
  logic r_f1_rd_index_valid;
  logic [scariv_conf_pkg::BTB_ENTRY_SIZE-1: 0] r_data_array_init_valid;

  always_ff @ (posedge i_clk, negedge i_reset_n) begin
    if (!i_reset_n) begin
      r_data_array_init_valid <= 'h0;
      r_f1_rd_index_valid     <= 1'b0;
      r_f1_xor_rd_index       <= 'h0;
    end else begin
      r_f1_rd_index_valid <= r_data_array_init_valid[w_f0_xor_rd_index];
      r_f1_xor_rd_index   <= w_f0_xor_rd_index;

      if (br_upd_if.update & !br_upd_if.dead) begin
        r_data_array_init_valid[w_br_upd_xor_index] <= 1'b1;
      end
    end
  end

  logic [ 1: 0] w_f1_bim_value;
  assign w_f1_bim_value = !r_f1_rd_index_valid ? 2'b10 : w_f1_bim_counter;
  always_ff @ (posedge i_clk, negedge i_reset_n) begin
    if (!i_reset_n) begin
      gshare_search_if.f2_bim_value[c_idx] <= 'h0;
      gshare_search_if.f2_index    [c_idx] <= 'h0;
      gshare_search_if.f2_bhr      [c_idx] <= 'h0;
    end else begin
      gshare_search_if.f2_bim_value[c_idx] <= w_f1_bim_value;
      gshare_search_if.f2_index    [c_idx] <= r_f1_xor_rd_index;
      // if (c_idx == 0) begin
      //   gshare_search_if.f2_bhr    [c_idx] <= r_ghr;
      // end else begin
      gshare_search_if.f2_bhr    [c_idx] <= w_f1_ghr_lane_next[c_idx];
      // end
    end // else: !if(!i_reset_n)
  end // always_ff @ (posedge i_clk, negedge i_reset_n)

end
endgenerate


// ----------------------------
// F2 stage Prediction Select
// ----------------------------
bit_extract_lsb #(.WIDTH(scariv_lsu_pkg::ICACHE_DATA_B_W/2)) f2_predict_valid_oh (.in(w_f2_predict_taken), .out(w_f2_predict_taken_oh));

assign o_f2_predict_valid        = |w_f2_predict_taken;
bit_oh_or_packed
  #(.T(vaddr_t),
    .WORDS(scariv_lsu_pkg::ICACHE_DATA_B_W/2)
    )
u_f2_target_vaddr_hit_oh (
 .i_oh      (w_f2_predict_taken_oh),
 .i_data    (search_btb_if.f2_target_vaddr),
 .o_selected(w_f2_btb_target_vaddr)
 );
assign o_f2_predict_target_vaddr = w_f2_btb_target_vaddr;

assign gshare_search_if.f2_pred_taken = w_f2_predict_taken;

`ifdef SIMULATION
int fp;
initial begin
  fp = $fopen("gshare.log", "w");
end
final begin
  $fclose(fp);
end

// -----------------------
// dispatched GHR storage
// -----------------------
typedef struct packed {
  scariv_pkg::cmt_id_t cmt_id;
  scariv_pkg::grp_id_t grp_id;
  gshare_hist_len_t ghr;
  gshare_bht_t      bhr_index;
} gshare_info_t;
gshare_info_t[scariv_conf_pkg::RV_BRU_ENTRY_SIZE-1: 0] r_gshare_info;

generate for (genvar d_idx = 0; d_idx < scariv_conf_pkg::DISP_SIZE; d_idx++) begin : bru_disp_loop
  assign w_disp_noncond_match[d_idx] = i_bru_disp_valid[d_idx] & (bru_disp_if.payload.inst[d_idx].is_call | bru_disp_if.payload.inst[d_idx].is_ret);
  assign w_disp[d_idx] = bru_disp_if.payload.inst[d_idx];
end endgenerate
bit_oh_or #(.T(disp_t), .WORDS(scariv_conf_pkg::DISP_SIZE)) u_disp_noncond_sel  (.i_oh(w_disp_noncond_match), .i_data(w_disp  ), .o_selected(w_disp_noncond_oh));

generate for (genvar brtag_idx = 0; brtag_idx < scariv_conf_pkg::RV_BRU_ENTRY_SIZE; brtag_idx++) begin: bhr_fifo_loop
  scariv_pkg::grp_id_t w_disp_cond_match;
  scariv_pkg::disp_t   w_disp_cond_oh;

  for (genvar d_idx = 0; d_idx < scariv_conf_pkg::DISP_SIZE; d_idx++) begin : bru_disp_loop
    assign w_disp_cond_match   [d_idx] = i_bru_disp_valid[d_idx] & (bru_disp_if.payload.inst[d_idx].brtag == brtag_idx);
  end

  bit_oh_or #(.T(disp_t), .WORDS(scariv_conf_pkg::DISP_SIZE)) u_disp_cond_sel     (.i_oh(w_disp_cond_match),    .i_data(w_disp  ), .o_selected(w_disp_cond_oh));

  always_ff @ (posedge i_clk) begin
    if (|w_disp_cond_match) begin
      r_gshare_info[brtag_idx].cmt_id    <= bru_disp_if.payload.cmt_id;
      r_gshare_info[brtag_idx].grp_id    <= w_disp_cond_match;
      r_gshare_info[brtag_idx].ghr       <= w_disp_cond_oh.gshare_bhr;
      r_gshare_info[brtag_idx].bhr_index <= w_disp_cond_oh.gshare_index;
    end
  end
end endgenerate // block: bhr_fifo_loop

gshare_hist_len_t sim_br_upd_gshare_bhr;
assign sim_br_upd_gshare_bhr =  w_br_upd_cond_rollback_valid ? w_br_upd_cond_rollback_ghr            :
                                r_gshare_info[br_upd_if.brtag].ghr;

typedef struct packed {
  scariv_pkg::cmt_id_t cmt_id;
  scariv_pkg::grp_id_t grp_id;
  gshare_hist_len_t    gshare_bhr;
  gshare_bht_t         gshare_rd_bht_index;
  gshare_bht_t         gshare_wr_bht_index;
  logic                taken;
  logic                predict_taken;
  logic                mispredict;
} branch_info_t;

branch_info_t branch_info_queue[$];
branch_info_t branch_info_new;
assign branch_info_new.cmt_id              = br_upd_if.cmt_id;
assign branch_info_new.grp_id              = br_upd_if.grp_id;
assign branch_info_new.gshare_bhr          = sim_br_upd_gshare_bhr;
assign branch_info_new.gshare_rd_bht_index = r_gshare_info[br_upd_if.brtag].bhr_index;
assign branch_info_new.gshare_wr_bht_index = r_gshare_info[br_upd_if.brtag].bhr_index;
assign branch_info_new.taken               = br_upd_if.taken;
assign branch_info_new.predict_taken       = br_upd_if.bim_value[1];
assign branch_info_new.mispredict          = br_upd_if.mispredict;

always_ff @ (negedge i_clk, negedge i_reset_n) begin
  if (i_reset_n) begin
    if (br_upd_if.update & !br_upd_if.dead) begin
      branch_info_queue.push_back(branch_info_new);
      $fwrite(fp, "%t PC=%08x (%d,%d) Result=%d(%s) GHR=%b\n", $time, br_upd_if.pc_vaddr,
              br_upd_if.cmt_id, br_upd_if.grp_id,
              br_upd_if.taken,
              br_upd_if.mispredict ? "MISS" : "SUCC",
              w_br_upd_cond_rollback_valid ? w_ghr_next : r_gshare_info[br_upd_if.brtag].ghr);
    end
  end
end

`endif // SIMULATION

endmodule // scariv_gshare
