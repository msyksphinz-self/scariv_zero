// ------------------------------------------------------------------------
// NAME : MRSH Predictor
// TYPE : module
// ------------------------------------------------------------------------
// It includes all variations of predictors for MSRH
// ------------------------------------------------------------------------
//
// ------------------------------------------------------------------------

module msrh_predictor
  import msrh_predict_pkg::*;
(
 input logic  i_clk,
 input logic  i_reset_n,

 btb_update_if.slave update_btb_if,
 btb_search_if.slave search_btb_if,

 bim_update_if.slave update_bim_if,
 bim_search_if.slave search_bim_if,

 input msrh_pkg::commit_blk_t i_commit

 );

msrh_btb u_btb
  (
   .i_clk(i_clk),
   .i_reset_n(i_reset_n),

   .update_btb_if (update_btb_if),
   .search_btb_if (search_btb_if)
   );

msrh_bim u_bim
  (
   .i_clk    (i_clk),
   .i_reset_n(i_reset_n),

   .update_bim_if (update_bim_if),
   .search_bim_if (search_bim_if)
   );

endmodule // msrh_predictor
