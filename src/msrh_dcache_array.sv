module msrh_dcache_array
  (
   input logic i_clk,
   input logic i_reset_n,

   input msrh_lsu_pkg::dc_update_t i_dc_update

   );

localparam TAG_SIZE = riscv_pkg::PADDR_W - msrh_lsu_pkg::DCACHE_TAG_LOW;

logic [msrh_lsu_pkg::ICACHE_WAY_W-1 : 0] w_s1_tag_hit;

logic [msrh_lsu_pkg::DCACHE_DATA_W-1: 0] w_s2_data[msrh_lsu_pkg::DCACHE_WAY_W];

generate for(genvar way = 0; way < msrh_lsu_pkg::DCACHE_WAY_W; way++) begin : icache_way_loop
logic    w_s1_tag_valid;
logic [TAG_SIZE-1:0] w_s1_tag;

  tag_array
    #(
      .TAG_W(TAG_SIZE),
      .WORDS(msrh_lsu_pkg::DCACHE_TAG_LOW)
      )
  tag (
       .i_clk(i_clk),
       .i_reset_n(i_reset_n),

       .i_wr  (i_dc_update.valid),
       .i_addr(i_dc_update.addr [$clog2(msrh_lsu_pkg::DCACHE_DATA_B_W) +: msrh_lsu_pkg::DCACHE_TAG_LOW]),
       .i_tag_valid  (1'b1),
       .i_tag (i_dc_update.addr[riscv_pkg::PADDR_W-1:msrh_lsu_pkg::DCACHE_TAG_LOW]),
       .o_tag(w_s1_tag),
       .o_tag_valid(w_s1_tag_valid)
       );

  // assign w_s1_tag_hit[way] = (i_s1_paddr[riscv_pkg::PADDR_W-1:msrh_lsu_pkg::DCACHE_TAG_LOW] == w_s1_tag) & w_s1_tag_valid;

  data_array
    #(
      .WIDTH(msrh_lsu_pkg::DCACHE_DATA_W),
      .ADDR_W(msrh_lsu_pkg::DCACHE_TAG_LOW)
      )
  data (
        .i_clk(i_clk),
        .i_reset_n(i_reset_n),
        .i_wr  (i_dc_update.valid),
        .i_addr(i_dc_update.addr[$clog2(msrh_lsu_pkg::DCACHE_DATA_B_W) +: msrh_lsu_pkg::DCACHE_TAG_LOW]),
        .i_data(i_dc_update.data),
        .o_data(w_s2_data[way])
        );

  // always_ff @ (posedge i_clk, negedge i_reset_n) begin
  //   if (!i_reset_n) begin
  //     r_s2_tag_hit[way] <= 1'b0;
  //   end else begin
  //     r_s2_tag_hit[way] <= w_s1_tag_hit[way];
  //   end
  // end

end
endgenerate

endmodule // msrh_dcache_array
