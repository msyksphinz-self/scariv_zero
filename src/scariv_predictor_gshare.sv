// ------------------------------------------------------------------------
// NAME : MRSH Predictor for GSHare
// TYPE : module
// ------------------------------------------------------------------------
// It includes GShare predictors for SCARIV
// ------------------------------------------------------------------------
//
// ------------------------------------------------------------------------

module scariv_predictor_gshare
  import scariv_pkg::*;
  import scariv_ic_pkg::*;
  import scariv_predict_pkg::*;
  import scariv_lsu_pkg::*;
(
 input logic  i_clk,
 input logic  i_reset_n,

 input commit_blk_t i_commit,

 input logic   i_f0_valid,
 input vaddr_t i_f0_vaddr,

 input logic i_f1_valid,
 input logic i_f2_valid,
 input scariv_ic_pkg::ic_resp_t i_f2_ic_resp,

 btb_update_if.slave   update_btb_if,
 btb_search_if.slave   search_btb_if,
 btb_search_if.monitor search_btb_mon_if,
 output vaddr_t o_f1_btb_target_vaddr,

 ras_search_if.master ras_search_if,

 gshare_search_if.slave gshare_search_if,

 // Feedback into Frontend for s0 stage
 ubtb_search_if.master  f1_ubtb_predict_if,

 // Feedback into Frontend
 output logic   o_f2_predict_valid,
 output vaddr_t o_f2_predict_target_vaddr,

 br_upd_if.slave      br_upd_if
 );

ic_block_t w_f1_btb_hit_oh;

// -----------
// BTB Search
// -----------

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

// Temporary
assign ras_search_if.f1_is_call = 1'b0;
assign ras_search_if.f1_is_ret  = 1'b0;
assign ras_search_if.f2_is_call = 1'b0;
assign ras_search_if.f2_is_ret  = 1'b0;

scariv_fetch_target_buffer
u_ftb
  (
   .i_clk     (i_clk    ),
   .i_reset_n (i_reset_n),

   .i_f0_valid (i_f0_valid),
   .i_f0_pc    (i_f0_vaddr),

   .f1_ubtb_predict_if (f1_ubtb_predict_if),

   .br_upd_if (br_upd_if)
   );

endmodule // scariv_predictor_gshare
