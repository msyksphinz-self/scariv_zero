// ------------------------------------------------------------------------
// NAME : MRSH Bimodal Predictor
// TYPE : module
// ------------------------------------------------------------------------
// Branch Predictor, Bimodal
// ------------------------------------------------------------------------
//
// ------------------------------------------------------------------------

module msrh_bim
  import msrh_predict_pkg::*;
(
 input logic  i_clk,
 input logic  i_reset_n,

 bim_update_if.slave update_bim_if,
 bim_search_if.slave search_bim_if
 );

logic [ 1: 0] w_update_counter;
logic [ 1: 0] w_counter;

logic [BTB_ENTRY_SIZE-1: 0] r_bim_valids;
logic                       r_s1_bim_valids;

always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_bim_valids <= {BTB_ENTRY_SIZE{1'b0}};
    r_s1_bim_valids <= 1'b0;
  end else begin
    if (update_bim_if.valid) begin
      r_bim_valids[update_bim_if.pc_vaddr[$clog2(BTB_ENTRY_SIZE): 1]] <= 1'b1;
    end
    r_s1_bim_valids <= r_bim_valids[search_bim_if.s0_pc_vaddr[$clog2(BTB_ENTRY_SIZE): 1]];
  end
end


data_array_2p
  #(
    .WIDTH (2),
    .ADDR_W ($clog2(BTB_ENTRY_SIZE))
    )
bim_array
  (
   .i_clk (i_clk),
   .i_reset_n (i_reset_n),

   .i_wr   (update_bim_if.valid),
   .i_wr_addr (update_bim_if.pc_vaddr[$clog2(BTB_ENTRY_SIZE): 1]),
   .i_wr_data (w_update_counter),

   .i_rd_addr (search_bim_if.s0_pc_vaddr[$clog2(BTB_ENTRY_SIZE): 1]),
   .o_rd_data (w_counter)
 );

assign w_update_counter =  (&update_bim_if.bim_value & update_bim_if.hit |
                           ~|update_bim_if.bim_value & update_bim_if.hit) ? update_bim_if.bim_value :
                           update_bim_if.taken ? update_bim_if.bim_value + 2'b01 :
                           update_bim_if.bim_value - 2'b01;

assign search_bim_if.s1_bim_value = r_s1_bim_valids ? w_counter : 2'b10;  // by default, weakly taken

endmodule // msrh_bim
