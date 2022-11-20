// ------------------------------------------------------------------------
// NAME : MRSH GShare Predictor
// TYPE : module
// ------------------------------------------------------------------------
// GShare Predictor
// ------------------------------------------------------------------------
//
// ------------------------------------------------------------------------

module msrh_gshare
  import msrh_pkg::*;
  import msrh_predict_pkg::*;
(
 input logic  i_clk,
 input logic  i_reset_n,

 br_upd_if.slave  br_upd_fe_if,

 btb_search_if.monitor  search_btb_if,
 gshare_search_if.slave gshare_search_if,

 // Feedback into Frontend
 output logic   o_s2_predict_valid,
 output vaddr_t o_s2_predict_target_vaddr
 );

logic         r_s1_valid;
gshare_bht_t  r_s1_bhr;

gshare_bht_t  r_bhr;      // Branch History Register : 1=Taken / 0:NonTaken
gshare_bht_t  w_bhr_next; // Branch History Register : 1=Taken / 0:NonTaken
/* verilator lint_off UNOPTFLAT */
gshare_bht_t  w_bhr_lane_next[msrh_lsu_pkg::ICACHE_DATA_B_W / 2];

logic [ 1: 0] w_update_counter;
logic [ 1: 0] w_s1_bim_counter;
logic [ 1: 0] r_s1_bim_counter_dram;

logic         s1_update_bhr;
assign s1_update_bhr = r_s1_valid & |(search_btb_if.s1_hit & search_btb_if.s1_is_cond);
gshare_bht_t  w_cmt_next_bhr;
assign w_cmt_next_bhr = {br_upd_fe_if.gshare_bhr[GSHARE_BHT_W-2:0], br_upd_fe_if.taken};

assign w_bhr_next = br_upd_fe_if.update & !br_upd_fe_if.dead & br_upd_fe_if.mispredict ? w_cmt_next_bhr :
                    // If Branch existed but not predicted (in frontend BHR not updated), update BHR
                    s1_update_bhr ? w_bhr_lane_next[msrh_lsu_pkg::ICACHE_DATA_B_W / 2-1] :
                    r_bhr;

always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_bhr <= {GSHARE_BHT_W{1'b0}};
  end else begin
    r_bhr <= w_bhr_next;
  end
end

generate for (genvar c_idx = 0; c_idx < msrh_lsu_pkg::ICACHE_DATA_B_W / 2; c_idx++) begin : bhr_loop
  gshare_bht_t  w_s0_xor_rd_index;
  gshare_bht_t  r_s1_xor_rd_index;
  assign w_s0_xor_rd_index = r_bhr ^ gshare_search_if.s0_pc_vaddr[$clog2(msrh_lsu_pkg::ICACHE_DATA_B_W) +: GSHARE_BHT_W];

  assign w_update_counter =  (((br_upd_fe_if.bim_value == 2'b11) & !br_upd_fe_if.mispredict &  br_upd_fe_if.taken |
                               (br_upd_fe_if.bim_value == 2'b00) & !br_upd_fe_if.mispredict & !br_upd_fe_if.taken)) ? br_upd_fe_if.bim_value :
                             br_upd_fe_if.taken ? br_upd_fe_if.bim_value + 2'b01 :
                             br_upd_fe_if.bim_value - 2'b01;

  if (c_idx == 0) begin
    assign w_bhr_lane_next[c_idx] = search_btb_if.s1_hit[c_idx] ?
                                    w_s1_bim_counter[1] ? {r_bhr, 1'b1} : {r_bhr, 1'b0} :
                                    r_bhr;
  end else begin
    assign w_bhr_lane_next[c_idx] = search_btb_if.s1_hit[c_idx] ?
                                    w_s1_bim_counter[1] ? {w_bhr_lane_next[c_idx-1], 1'b1} : {w_bhr_lane_next[c_idx-1], 1'b0} :
                                    w_bhr_lane_next[c_idx-1];
  end

  // data_array_2p
  //   #(
  //     .WIDTH (2),
  //     .ADDR_W (msrh_pkg::GSHARE_BHT_W)
  //     )
  // bim_array
  //   (
  //    .i_clk     (i_clk),
  //    .i_reset_n (i_reset_n),
  //
  //    .i_wr      (br_upd_fe_if.update & !br_upd_fe_if.dead),
  //    .i_wr_addr (br_upd_fe_if.gshare_index),
  //    .i_wr_data (w_update_counter),
  //
  //    .i_rd_addr (w_s0_xor_rd_index),
  //    .o_rd_data (w_s1_bim_counter_dram)
  //    );

  logic [$clog2(msrh_lsu_pkg::ICACHE_DATA_B_W/2)-1: 0] br_update_lane;
  logic br_update_lane_hit;
  assign br_update_lane = br_upd_fe_if.is_rvc ? br_upd_fe_if.pc_vaddr[$clog2(msrh_lsu_pkg::ICACHE_DATA_B_W)-1: 1] :
                          br_upd_fe_if.pc_vaddr[$clog2(msrh_lsu_pkg::ICACHE_DATA_B_W)-1: 1] + 'h1;

  assign br_update_lane_hit = br_update_lane == c_idx;

  logic [ 1: 0]   w_bim_array [2 ** msrh_pkg::GSHARE_BHT_W];
  for (genvar a_idx = 0; a_idx < 2 ** msrh_pkg::GSHARE_BHT_W; a_idx++) begin : bim_loop
    logic [ 1: 0]   r_bim;
    always_ff @ (posedge i_clk, negedge i_reset_n) begin
      if (!i_reset_n) begin
        r_bim <= 2'b10;
      end else begin
        if (br_upd_fe_if.update & !br_upd_fe_if.dead &
            br_update_lane_hit &
            (br_upd_fe_if.gshare_index == a_idx)) begin
          r_bim <= w_update_counter;
        end
      end
    end
    assign w_bim_array[a_idx] = r_bim;
  end // block: bim_loop

  always_ff @ (posedge i_clk, negedge i_reset_n) begin
    if (!i_reset_n) begin
      r_s1_bim_counter_dram <= 'h0;
    end else begin
      r_s1_bim_counter_dram <= w_bim_array[w_s0_xor_rd_index];
    end
  end

  assign w_s1_bim_counter = br_upd_fe_if.update & !br_upd_fe_if.dead &
                            (br_upd_fe_if.gshare_index == w_s0_xor_rd_index) ? w_update_counter :
                            r_s1_bim_counter_dram;

  // Data SRAM is not formatted.
  // First access, default is set to TAKEN.
  logic r_s1_rd_index_valid;
  logic [BTB_ENTRY_SIZE-1: 0] r_data_array_init_valid;

  always_ff @ (posedge i_clk, negedge i_reset_n) begin
    if (!i_reset_n) begin
      r_data_array_init_valid <= 'h0;
      r_s1_rd_index_valid     <= 1'b0;
      r_s1_xor_rd_index       <= 'h0;
    end else begin
      r_s1_rd_index_valid <= r_data_array_init_valid[w_s0_xor_rd_index];
      r_s1_xor_rd_index   <= w_s0_xor_rd_index;

      if (br_upd_fe_if.update & !br_upd_fe_if.dead) begin
        r_data_array_init_valid[br_upd_fe_if.gshare_index] <= 1'b1;
      end
    end
  end

  logic [ 1: 0] w_s1_bim_value;
  assign w_s1_bim_value = !r_s1_rd_index_valid ? 2'b10 : w_s1_bim_counter;
  always_ff @ (posedge i_clk, negedge i_reset_n) begin
    if (!i_reset_n) begin
      gshare_search_if.s2_bim_value[c_idx] <= 'h0;
      gshare_search_if.s2_index    [c_idx] <= 'h0;
      gshare_search_if.s2_bhr      [c_idx] <= 'h0;
    end else begin
      gshare_search_if.s2_bim_value[c_idx] <= w_s1_bim_value;
      gshare_search_if.s2_index    [c_idx] <= r_s1_xor_rd_index;
      if (c_idx == 0) begin
        gshare_search_if.s2_bhr    [c_idx] <= r_bhr;
      end else begin
        gshare_search_if.s2_bhr    [c_idx] <= w_bhr_lane_next[c_idx-1];
      end
    end // else: !if(!i_reset_n)
  end // always_ff @ (posedge i_clk, negedge i_reset_n)

end
endgenerate


always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_s1_valid <= 1'b0;

    gshare_search_if.s2_valid <= 1'b0;
  end else begin
    r_s1_valid <= gshare_search_if.s0_valid;

    gshare_search_if.s2_valid <= r_s1_valid;
  end // else: !if(!i_reset_n)
end // always_ff @ (posedge i_clk, negedge i_reset_n)


// ------------------------------
// S2 Prediction Valid
// ------------------------------
msrh_ic_pkg::ic_block_t w_s2_predict_taken;
msrh_ic_pkg::ic_block_t w_s2_predict_taken_oh;
vaddr_t                 w_s2_btb_target_vaddr;

generate for (genvar b_idx = 0; b_idx < msrh_lsu_pkg::ICACHE_DATA_B_W/2; b_idx++) begin : bim_loop
  assign w_s2_predict_taken[b_idx] = gshare_search_if.s2_bim_value[b_idx][1] &
                                     search_btb_if.s2_hit[b_idx];
end
endgenerate

bit_extract_lsb #(.WIDTH(msrh_lsu_pkg::ICACHE_DATA_B_W/2)) s2_predict_valid_oh (.in(w_s2_predict_taken), .out(w_s2_predict_taken_oh));

assign o_s2_predict_valid        = |w_s2_predict_taken;
bit_oh_or_packed
  #(.T(vaddr_t),
    .WORDS(msrh_lsu_pkg::ICACHE_DATA_B_W/2)
    )
u_s2_target_vaddr_hit_oh (
 .i_oh      (w_s2_predict_taken_oh),
 .i_data    (search_btb_if.s2_target_vaddr),
 .o_selected(w_s2_btb_target_vaddr)
 );
assign o_s2_predict_target_vaddr = w_s2_btb_target_vaddr;

assign gshare_search_if.s2_pred_taken = w_s2_predict_taken;

endmodule // msrh_gshare
