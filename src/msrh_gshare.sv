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

 gshare_search_if.slave gshare_search_if

 );

logic [GSHARE_BHT_W-1: 0] w_xor_rd_index;
logic [ 1: 0]             w_update_counter;
logic [ 1: 0]             w_s1_bim_counter;
logic [GSHARE_BHT_W-1: 0] r_bhr; // Branch History Register : 1=Taken / 0:NonTaken

always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_bhr <= {GSHARE_BHT_W{1'b0}};
  end else begin
    if (br_upd_fe_if.update & !br_upd_fe_if.dead & br_upd_fe_if.mispredict) begin
      r_bhr <= br_upd_fe_if.gshare_bhr;
    end else if (gshare_search_if.s1_valid) begin
      r_bhr <= {r_bhr[GSHARE_BHT_W-2:0], gshare_search_if.s1_pred_taken};
    end
  end
end

assign w_xor_rd_index = r_bhr ^ gshare_search_if.s0_pc_vaddr[msrh_pkg::VADDR_W-1 -: GSHARE_BHT_W];

assign w_update_counter =  (((br_upd_fe_if.bim_value == 2'b11) |
                             (br_upd_fe_if.bim_value == 2'b00)) & !br_upd_fe_if.mispredict) ? br_upd_fe_if.bim_value :
                           br_upd_fe_if.taken ? br_upd_fe_if.bim_value + 2'b01 :
                           br_upd_fe_if.bim_value - 2'b01;


data_array_2p
  #(
    .WIDTH (2),
    .ADDR_W ($clog2(BTB_ENTRY_SIZE))
    )
bim_array
  (
   .i_clk     (i_clk),
   .i_reset_n (i_reset_n),

   .i_wr      (br_upd_fe_if.update & !br_upd_fe_if.dead),
   .i_wr_addr (br_upd_fe_if.gshare_index),
   .i_wr_data (w_update_counter),

   .i_rd_addr (w_xor_rd_index),
   .o_rd_data (w_s1_bim_counter)
   );

assign gshare_search_if.s1_pred_taken = w_s1_bim_counter[1];

always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    gshare_search_if.s1_valid <= 1'b0;
    gshare_search_if.s1_index <= 'h0;
    gshare_search_if.s1_bhr <= 'h0;

    gshare_search_if.s2_valid <= 1'b0;
    gshare_search_if.s2_index <= 'h0;
    gshare_search_if.s2_bhr   <= 'h0;
  end else begin
    gshare_search_if.s1_valid <= gshare_search_if.s0_valid;
    gshare_search_if.s1_index <= w_xor_rd_index;
    gshare_search_if.s1_bhr   <= r_bhr;

    gshare_search_if.s2_valid <= gshare_search_if.s1_valid;
    gshare_search_if.s2_index <= gshare_search_if.s1_index;
    gshare_search_if.s2_bhr   <= gshare_search_if.s1_bhr  ;
  end // else: !if(!i_reset_n)
end // always_ff @ (posedge i_clk, negedge i_reset_n)


endmodule // msrh_gshare
