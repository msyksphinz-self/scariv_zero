`default_nettype none

module icache(
  input logic i_clk,
  input logic i_reset_n,

  input mrh_pkg::ic_req_t i_s0_req,
  input logic [riscv_pkg::PADDR_W-1:0] i_s1_paddr,
  input logic                          i_s1_tlb_miss,

  output mrh_pkg::ic_resp_t            o_s2_resp
);

/* S1 stage */
logic r_s1_valid;
logic [mrh_pkg::ICACHE_WAY_W-1 : 0] w_s1_tag_hit;
logic [mrh_pkg::ICACHE_TAG_LOW-1:0] r_s1_addr_low_bit;

/* S2 stage */
logic                               r_s2_valid;
logic [mrh_pkg::ICACHE_WAY_W-1 : 0] r_s2_tag_hit;
logic [mrh_pkg::ICACHE_DATA_W-1: 0] w_s2_data[mrh_pkg::ICACHE_WAY_W];
logic [mrh_pkg::ICACHE_DATA_W-1: 0] w_s2_selected_data;

generate for(genvar way = 0; way < mrh_pkg::ICACHE_WAY_W; way++) begin : icache_way_loop
  logic    w_s1_tag_valid;
  logic [riscv_pkg::PADDR_W-1:mrh_pkg::ICACHE_TAG_LOW] w_s1_tag;

  tag_array
  #(
    .TAG_W(riscv_pkg::PADDR_W-mrh_pkg::ICACHE_TAG_LOW),
    .WORDS(mrh_pkg::ICACHE_TAG_LOW)
  )
  tag (
    .i_clk(i_clk),
    .i_reset_n(i_reset_n),
    .i_addr(i_s0_req.vaddr[mrh_pkg::ICACHE_TAG_LOW-1:0]),
    .o_tag(w_s1_tag),
    .o_tag_valid(w_s1_tag_valid)
  );

  assign w_s1_tag_hit[way] = (i_s1_paddr[riscv_pkg::PADDR_W-1:mrh_pkg::ICACHE_TAG_LOW] == w_s1_tag) & w_s1_tag_valid;

  data_array
  #(
    .WIDTH(mrh_pkg::ICACHE_DATA_W),
    .ADDR_W(mrh_pkg::ICACHE_TAG_LOW)
  )
  data (
    .i_clk(i_clk),
    .i_reset_n(i_reset_n),
    .i_addr(r_s1_addr_low_bit),
    .o_data(w_s2_data[way])
  );

  always_ff @ (posedge i_clk, negedge i_reset_n) begin
    if (!i_reset_n) begin
      r_s2_tag_hit[way] <= 1'b0;
    end else begin
      r_s2_tag_hit[way] <= w_s1_tag_hit[way];
    end
  end

end
endgenerate

// ===============
// S1 stage
// ===============
always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_s1_valid <= 1'b0;
    r_s1_addr_low_bit <= {mrh_pkg::ICACHE_TAG_LOW{1'b0}};
  end else begin
    r_s1_valid <= i_s0_req.valid;
    r_s1_addr_low_bit <= i_s0_req.vaddr[mrh_pkg::ICACHE_TAG_LOW-1:0];
  end
end

// ===============
// S2 stage
// ===============
always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_s2_valid <= 1'b0;
  end else begin
    r_s2_valid <= r_s1_valid & (|w_s1_tag_hit) & !i_s1_tlb_miss;
  end
end



bit_oh_or
#(
  .WIDTH(mrh_pkg::ICACHE_DATA_W),
  .WORDS(mrh_pkg::ICACHE_WAY_W)
)
cache_data_sel (
    .i_oh      (r_s2_tag_hit      ),
    .i_data    (w_s2_data         ),
    .o_selected(w_s2_selected_data)
);

assign o_s2_resp.valid = r_s2_valid;
assign o_s2_resp.data  = w_s2_selected_data;

endmodule

`default_nettype wire
