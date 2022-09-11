// ------------------------------------------------------------------------
// NAME : MRSH Predictor for GSHare
// TYPE : module
// ------------------------------------------------------------------------
// It includes GShare predictors for MSRH
// ------------------------------------------------------------------------
//
// ------------------------------------------------------------------------

module msrh_predictor_gshare
  import msrh_pkg::*;
  import msrh_predict_pkg::*;
  import msrh_lsu_pkg::*;
(
 input logic  i_clk,
 input logic  i_reset_n,

 input commit_blk_t i_commit,

 input logic i_s1_valid,
 input logic i_s2_valid,
 input msrh_ic_pkg::ic_resp_t i_s2_ic_resp,

 btb_update_if.slave update_btb_if,
 btb_search_if.slave search_btb_if,
 output vaddr_t o_s1_btb_target_vaddr,

 ras_search_if.master ras_search_if,

 gshare_search_if.slave gshare_search_if,

 br_upd_if.slave  br_upd_fe_if
 );

typedef logic [ICACHE_DATA_B_W/2-1: 0] ic_block_t;


ic_block_t w_s1_btb_hit_oh;

// -----------
// BTB Search
// -----------

msrh_btb u_btb
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


// -----------------
// GShare Predictor
// -----------------

msrh_gshare
u_gshare
  (
   .i_clk     (i_clk),
   .i_reset_n (i_reset_n),

   .search_btb_if    (search_btb_if   ),
   .gshare_search_if (gshare_search_if),
   .br_upd_fe_if     (br_upd_fe_if    )
   );

// Temporary
assign ras_search_if.s1_is_call = 1'b0;
assign ras_search_if.s1_is_ret  = 1'b0;
assign ras_search_if.s2_is_call = 1'b0;
assign ras_search_if.s2_is_ret  = 1'b0;

endmodule // msrh_predictor_gshare
