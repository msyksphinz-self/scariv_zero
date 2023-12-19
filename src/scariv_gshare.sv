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

 br_upd_if.slave br_upd_if,

 btb_search_if.monitor  search_btb_if,
 gshare_search_if.slave gshare_search_if,

 // Feedback into Frontend
 output logic   o_f2_predict_valid,
 output vaddr_t o_f2_predict_target_vaddr
 );

logic         r_f1_valid;
gshare_hist_len_t  r_f1_bhr;

gshare_hist_len_t  r_bhr;      // Branch History Register : 1=Taken / 0:NonTaken
gshare_hist_len_t  w_bhr_next; // Branch History Register : 1=Taken / 0:NonTaken
/* verilator lint_off UNOPTFLAT */
gshare_hist_len_t  w_f1_bhr_lane_next[scariv_lsu_pkg::ICACHE_DATA_B_W / 2-1 : 0];

logic [scariv_lsu_pkg::ICACHE_DATA_B_W / 2-1 : 0] w_f1_lane_predict;
logic [scariv_lsu_pkg::ICACHE_DATA_B_W / 2-1 : 0] w_f0_pc_vaddr_mask;
logic [scariv_lsu_pkg::ICACHE_DATA_B_W / 2-1 : 0] r_f1_pc_vaddr_mask;
logic [scariv_lsu_pkg::ICACHE_DATA_B_W / 2-1 : 0] w_f1_cond_hit_valid;
logic [scariv_lsu_pkg::ICACHE_DATA_B_W / 2-1 : 0] w_f1_cond_hit_active;

logic [scariv_lsu_pkg::ICACHE_DATA_B_W / 2-1 : 0] r_f1_call_ret_hit_valid;

logic         w_f1_update_bhr;
logic         r_f2_update_bhr;
gshare_hist_len_t  r_f2_bhr_lane_last;
assign w_f1_update_bhr = r_f1_valid & i_f1_valid & |w_f1_cond_hit_valid;

logic        w_br_upd_noncond_rollback_valid;
gshare_hist_len_t w_br_upd_noncond_rollback_bhr;

logic        w_br_upd_rollback_valid;
gshare_hist_len_t w_br_upd_rollback_bhr;

logic        w_br_upd_btb_newly_allocated_valid;
gshare_hist_len_t w_br_upd_btb_newly_allocated_bhr;

assign w_br_upd_noncond_rollback_bhr   = br_upd_if.gshare_bhr;
assign w_br_upd_noncond_rollback_valid = br_upd_if.update & !br_upd_if.dead & !br_upd_if.is_cond &
                                         br_upd_if.mispredict;

assign w_br_upd_rollback_bhr   = {br_upd_if.gshare_bhr[GSHARE_HIST_LEN-1:1], br_upd_if.taken};
assign w_br_upd_rollback_valid = br_upd_if.update & !br_upd_if.dead & br_upd_if.is_cond &
                                 br_upd_if.mispredict;

assign w_br_upd_btb_newly_allocated_valid = br_upd_if.update & !br_upd_if.dead & br_upd_if.is_cond &
                                            br_upd_if.btb_not_hit;
assign w_br_upd_btb_newly_allocated_bhr   = {br_upd_if.gshare_bhr[GSHARE_HIST_LEN-2:0], br_upd_if.taken};

assign w_bhr_next = w_br_upd_noncond_rollback_valid    ? w_br_upd_noncond_rollback_bhr    :
                    w_br_upd_btb_newly_allocated_valid ? w_br_upd_btb_newly_allocated_bhr :
                    w_br_upd_rollback_valid            ? w_br_upd_rollback_bhr :
                    // If Branch existed but not predicted (in frontend BHR not updated), update BHR
                    r_f2_update_bhr & i_f2_valid       ? r_f2_bhr_lane_last :
                    r_bhr;

always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_bhr <= {GSHARE_HIST_LEN{1'b0}};
    r_f2_update_bhr <= 1'b0;
  end else begin
    r_bhr <= w_bhr_next;

    r_f1_pc_vaddr_mask <= w_f0_pc_vaddr_mask;

    r_f2_update_bhr <= w_f1_update_bhr;
    r_f2_bhr_lane_last <= w_f1_update_bhr ? w_f1_bhr_lane_next[scariv_lsu_pkg::ICACHE_DATA_B_W / 2-1] :
                          r_f2_bhr_lane_last;
  end
end

assign w_f0_pc_vaddr_mask = ~((1 << gshare_search_if.f0_pc_vaddr[$clog2(scariv_lsu_pkg::ICACHE_DATA_B_W)-1: 1]) - 1);
assign w_f1_cond_hit_valid     = search_btb_if.f1_hit & search_btb_if.f1_is_cond & r_f1_pc_vaddr_mask;
assign r_f1_call_ret_hit_valid = search_btb_if.f1_hit & (search_btb_if.f1_is_call | search_btb_if.f1_is_ret | search_btb_if.f1_is_noncond) & r_f1_pc_vaddr_mask;

logic [ 1: 0] w_update_counter;

assign w_update_counter =  (((br_upd_if.bim_value == 2'b11) & !br_upd_if.mispredict &  br_upd_if.taken |
                             (br_upd_if.bim_value == 2'b00) & !br_upd_if.mispredict & !br_upd_if.taken)) ? br_upd_if.bim_value :
                           br_upd_if.taken ? br_upd_if.bim_value + 2'b01 :
                           br_upd_if.bim_value - 2'b01;

logic [$clog2(scariv_lsu_pkg::ICACHE_DATA_B_W/2)-1: 0] br_update_lane;
assign br_update_lane = br_upd_if.is_rvc ? br_upd_if.pc_vaddr[$clog2(scariv_lsu_pkg::ICACHE_DATA_B_W)-1: 1] :
                        br_upd_if.pc_vaddr[$clog2(scariv_lsu_pkg::ICACHE_DATA_B_W)-1: 1] + 'h1;
gshare_hist_len_t w_br_upd_index_raw;
gshare_bht_t      w_br_upd_xor_index;
assign w_br_upd_index_raw = br_upd_if.gshare_bhr ^ (br_upd_if.pc_vaddr >> $clog2(scariv_lsu_pkg::ICACHE_DATA_B_W));
assign w_br_upd_xor_index = fold_hash_index(w_br_upd_index_raw);


generate for (genvar c_idx = 0; c_idx < scariv_lsu_pkg::ICACHE_DATA_B_W / 2; c_idx++) begin : bhr_loop
  logic [ 1: 0] w_f1_bim_counter;
  logic [ 1: 0] r_f1_bim_counter_dram;
  gshare_hist_len_t  w_f0_xor_rd_index_raw;
  gshare_bht_t       w_f0_xor_rd_index;
  gshare_bht_t       r_f1_xor_rd_index;

  // assign w_f0_xor_rd_index_raw = r_bhr ^ gshare_search_if.f0_pc_vaddr[$clog2(scariv_lsu_pkg::ICACHE_DATA_B_W) +: GSHARE_HIST_LEN];
  if (c_idx == 0) begin
    assign w_f0_xor_rd_index_raw = r_f2_bhr_lane_last          ^ (gshare_search_if.f0_pc_vaddr >> $clog2(scariv_lsu_pkg::ICACHE_DATA_B_W));
  end else begin
    assign w_f0_xor_rd_index_raw = w_f1_bhr_lane_next[c_idx-1] ^ (gshare_search_if.f0_pc_vaddr >> $clog2(scariv_lsu_pkg::ICACHE_DATA_B_W));
  end
  assign w_f0_xor_rd_index     = fold_hash_index(w_f0_xor_rd_index_raw);


  assign w_f1_lane_predict   [c_idx] = w_f1_cond_hit_valid[c_idx] ? w_f1_bim_counter[1] : 1'b0;

  if (c_idx == 0) begin
    assign w_f1_cond_hit_active[c_idx] = w_f1_cond_hit_valid[c_idx];
    assign w_f1_bhr_lane_next  [c_idx] = w_f1_cond_hit_active[c_idx] ? {r_f2_bhr_lane_last, w_f1_lane_predict[c_idx]} :
                                         r_f2_bhr_lane_last;
  end else begin
    assign w_f1_cond_hit_active[c_idx] = w_f1_cond_hit_valid[c_idx] & ~(|r_f1_call_ret_hit_valid[c_idx-1: 0]);
    assign w_f1_bhr_lane_next  [c_idx] = w_f1_cond_hit_active[c_idx] & ~|w_f1_lane_predict[c_idx-1: 0] ?
                                         {w_f1_bhr_lane_next[c_idx-1], w_f1_lane_predict[c_idx]} : w_f1_bhr_lane_next[c_idx-1];
  end

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
  //    .i_wr_data (w_update_counter),
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
          r_bim <= w_update_counter;
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
                            (br_upd_if.gshare_index == w_f0_xor_rd_index) ? w_update_counter :
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
      if (c_idx == 0) begin
        gshare_search_if.f2_bhr    [c_idx] <= r_bhr;
      end else begin
        gshare_search_if.f2_bhr    [c_idx] <= w_f1_bhr_lane_next[c_idx];
      end
    end // else: !if(!i_reset_n)
  end // always_ff @ (posedge i_clk, negedge i_reset_n)

end
endgenerate


always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_f1_valid <= 1'b0;

    gshare_search_if.f2_valid <= 1'b0;
  end else begin
    r_f1_valid <= gshare_search_if.f0_valid;

    gshare_search_if.f2_valid <= r_f1_valid & i_f1_valid;
  end // else: !if(!i_reset_n)
end // always_ff @ (posedge i_clk, negedge i_reset_n)


// ------------------------------
// S2 Prediction Valid
// ------------------------------
scariv_ic_pkg::ic_block_t w_f2_predict_taken;
scariv_ic_pkg::ic_block_t w_f2_predict_taken_oh;
vaddr_t                 w_f2_btb_target_vaddr;

generate for (genvar b_idx = 0; b_idx < scariv_lsu_pkg::ICACHE_DATA_B_W/2; b_idx++) begin : bim_loop
  assign w_f2_predict_taken[b_idx] = gshare_search_if.f2_bim_value[b_idx][1] &
                                     search_btb_if.f2_hit[b_idx];
end
endgenerate

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

gshare_hist_len_t sim_br_upd_gshare_bhr;
assign sim_br_upd_gshare_bhr =  w_br_upd_noncond_rollback_valid    ? w_br_upd_noncond_rollback_bhr    :
                                w_br_upd_btb_newly_allocated_valid ? w_br_upd_btb_newly_allocated_bhr :
                                w_br_upd_rollback_valid            ? w_br_upd_rollback_bhr            :
                                br_upd_if.gshare_bhr;

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
assign branch_info_new.gshare_rd_bht_index = br_upd_if.gshare_index;
assign branch_info_new.gshare_wr_bht_index = w_br_upd_xor_index;
assign branch_info_new.taken               = br_upd_if.taken;
assign branch_info_new.predict_taken       = br_upd_if.bim_value[1];
assign branch_info_new.mispredict          = br_upd_if.mispredict;

always_ff @ (negedge i_clk, negedge i_reset_n) begin
  if (i_reset_n) begin
    if (br_upd_if.update & !br_upd_if.dead & br_upd_if.is_cond) begin
      branch_info_queue.push_back(branch_info_new);
      $fwrite(fp, "%t PC=%08x (%d,%d) Result=%d(%s) BHR=%b\n", $time, br_upd_if.pc_vaddr,
              br_upd_if.cmt_id, br_upd_if.grp_id,
              br_upd_if.taken,
              br_upd_if.mispredict ? "MISS" : "SUCC",
              w_br_upd_rollback_valid ? w_bhr_next : br_upd_if.gshare_bhr);
    end
  end
end

`endif // SIMULATION

endmodule // scariv_gshare
