module msrh_dcache_array
  #(
    // from LSU Pipeline + STQ Update + PTW
    parameter READ_PORT_NUM = msrh_conf_pkg::LSU_INST_NUM + 1 + 1 + 1
    )
  (
   input logic i_clk,
   input logic i_reset_n,

   input msrh_lsu_pkg::dc_update_t     i_dc_update,
   input msrh_lsu_pkg::dc_read_req_t   i_dc_read_req [READ_PORT_NUM],
   output msrh_lsu_pkg::dc_read_resp_t o_dc_read_resp[READ_PORT_NUM]
   );

localparam TAG_SIZE = riscv_pkg::PADDR_W - msrh_lsu_pkg::DCACHE_TAG_LOW;

logic [READ_PORT_NUM-1:0] w_s0_dc_read_req_valid;
logic [READ_PORT_NUM-1:0] w_s0_dc_read_req_valid_oh;
msrh_lsu_pkg::dc_read_req_t w_s0_dc_selected_read_req;

logic                              w_s0_dc_tag_valid;
logic                              w_s0_dc_tag_wr;
logic [riscv_pkg::PADDR_W-1: 0]    w_s0_dc_tag_addr;


logic [READ_PORT_NUM-1:0]       r_s1_dc_read_req_valid;
logic [READ_PORT_NUM-1:0]       r_s1_dc_read_req_valid_oh;
logic [msrh_conf_pkg::DCACHE_DATA_W-1: 0] w_s1_data[msrh_lsu_pkg::DCACHE_WAY_W];
logic [msrh_lsu_pkg::DCACHE_WAY_W-1 : 0]  w_s1_tag_valid;
logic [TAG_SIZE-1:0]                      w_s1_tag[msrh_lsu_pkg::DCACHE_WAY_W];

logic [riscv_pkg::PADDR_W-1: 0]          r_s1_dc_tag_addr;

logic                                    r_s1_dc_update_valid;

// Selection of Request from LSU ports
generate for (genvar l_idx = 0; l_idx < READ_PORT_NUM; l_idx++) begin : lsu_loop
  assign w_s0_dc_read_req_valid[l_idx] = i_dc_read_req[l_idx].valid;

  logic w_s0_dc_read_tag_same;
  logic r_s1_dc_read_tag_same;
  logic [riscv_pkg::PADDR_W-1:msrh_lsu_pkg::DCACHE_TAG_LOW] r_s1_dc_lsu_tag_addr;
  logic [msrh_conf_pkg::DCACHE_DATA_W-1: 0]                 w_s1_selected_data;

  assign w_s0_dc_read_tag_same = w_s0_dc_tag_addr[$clog2(msrh_lsu_pkg::DCACHE_DATA_B_W) +: msrh_lsu_pkg::DCACHE_TAG_LOW] ==
                                 i_dc_read_req[l_idx].paddr[$clog2(msrh_lsu_pkg::DCACHE_DATA_B_W) +: msrh_lsu_pkg::DCACHE_TAG_LOW];
  always_ff @ (posedge i_clk, negedge i_reset_n) begin
    if (!i_reset_n) begin
      r_s1_dc_read_tag_same <= 1'b0;
      r_s1_dc_lsu_tag_addr <= 'h0;
    end else begin
      r_s1_dc_read_tag_same <= w_s0_dc_read_tag_same;
      r_s1_dc_lsu_tag_addr <= i_dc_read_req[l_idx].paddr[riscv_pkg::PADDR_W-1:msrh_lsu_pkg::DCACHE_TAG_LOW];
    end
  end

  logic [msrh_lsu_pkg::DCACHE_WAY_W-1 : 0] w_s1_tag_hit;
  for(genvar way = 0; way < msrh_lsu_pkg::DCACHE_WAY_W; way++) begin : icache_way_loop
    assign w_s1_tag_hit[way] = (r_s1_dc_lsu_tag_addr == w_s1_tag[way]) & w_s1_tag_valid[way];
  end

  bit_oh_or #(.T(logic[msrh_conf_pkg::ICACHE_DATA_W-1:0]), .WORDS(msrh_lsu_pkg::ICACHE_WAY_W))
  cache_data_sel (.i_oh (w_s1_tag_hit), .i_data(w_s1_data), .o_selected(w_s1_selected_data));

  logic w_s1_read_req_valid;
  // read_req_valid condition:
  // 1. Not Update Path
  // 2. Read Request
  // 3. Read Request Selected
  // 4. Read Request not selected, but same as selected address line.
  assign w_s1_read_req_valid = !r_s1_dc_update_valid & r_s1_dc_read_req_valid[l_idx] & (r_s1_dc_read_req_valid_oh[l_idx] | r_s1_dc_read_tag_same);

  assign o_dc_read_resp[l_idx].hit      = w_s1_read_req_valid & (|w_s1_tag_hit);
  assign o_dc_read_resp[l_idx].miss     = w_s1_read_req_valid & ~(|w_s1_tag_hit);
  assign o_dc_read_resp[l_idx].conflict =  r_s1_dc_update_valid |
                                           r_s1_dc_read_req_valid[l_idx] & !r_s1_dc_read_req_valid_oh[l_idx] & !r_s1_dc_read_tag_same;

  assign o_dc_read_resp[l_idx].data     =  w_s1_selected_data;

  // Need to replace: line existed but not hit
  // temporary tied to way-0
  assign o_dc_read_resp[l_idx].replace_valid = |(w_s1_tag_valid & ~w_s1_tag_hit);
  assign o_dc_read_resp[l_idx].replace_way   = 'h0;  // temporary
  assign o_dc_read_resp[l_idx].replace_data  = w_s1_data[0];
  assign o_dc_read_resp[l_idx].replace_paddr = {w_s1_tag[0],
                                                r_s1_dc_tag_addr[msrh_lsu_pkg::DCACHE_TAG_LOW-1:$clog2(msrh_lsu_pkg::DCACHE_DATA_B_W)],
                                                {$clog2(msrh_lsu_pkg::DCACHE_DATA_B_W){1'b0}}};
end
endgenerate
bit_extract_lsb #(.WIDTH(READ_PORT_NUM)) u_bit_req_sel (.in(w_s0_dc_read_req_valid), .out(w_s0_dc_read_req_valid_oh));
bit_oh_or #(.T(msrh_lsu_pkg::dc_read_req_t), .WORDS(READ_PORT_NUM)) select_rerun_oh  (.i_oh(w_s0_dc_read_req_valid_oh), .i_data(i_dc_read_req), .o_selected(w_s0_dc_selected_read_req));

assign w_s0_dc_tag_valid = i_dc_update.valid | (|w_s0_dc_read_req_valid);
assign w_s0_dc_tag_wr    = i_dc_update.valid;
assign w_s0_dc_tag_addr  = i_dc_update.valid ? i_dc_update.addr : w_s0_dc_selected_read_req.paddr;

always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_s1_dc_read_req_valid_oh <= 'h0;
    r_s1_dc_read_req_valid    <= 'h0;
    r_s1_dc_tag_addr          <= 'h0;

    r_s1_dc_update_valid <= 1'b0;
  end else begin
    r_s1_dc_read_req_valid_oh <= w_s0_dc_read_req_valid_oh;
    r_s1_dc_read_req_valid    <= w_s0_dc_read_req_valid;
    r_s1_dc_tag_addr          <= w_s0_dc_tag_addr;

    r_s1_dc_update_valid <= i_dc_update.valid;
  end
end


generate for(genvar way = 0; way < msrh_lsu_pkg::DCACHE_WAY_W; way++) begin : icache_way_loop

  tag_array
    #(
      .TAG_W(TAG_SIZE),
      .WORDS(msrh_lsu_pkg::DCACHE_TAG_LOW)
      )
  tag (
       .i_clk(i_clk),
       .i_reset_n(i_reset_n),

       .i_wr  (w_s0_dc_tag_wr),
       .i_addr(w_s0_dc_tag_addr[$clog2(msrh_lsu_pkg::DCACHE_DATA_B_W) +: msrh_lsu_pkg::DCACHE_TAG_LOW]),
       .i_tag_valid  (1'b1),
       .i_tag (i_dc_update.addr[riscv_pkg::PADDR_W-1:msrh_lsu_pkg::DCACHE_TAG_LOW]),
       .o_tag(w_s1_tag[way]),
       .o_tag_valid(w_s1_tag_valid[way])
       );

  data_array
    #(
      .WIDTH(msrh_conf_pkg::DCACHE_DATA_W),
      .ADDR_W(msrh_lsu_pkg::DCACHE_TAG_LOW)
      )
  data (
        .i_clk(i_clk),
        .i_reset_n(i_reset_n),
        .i_wr  (i_dc_update.valid),
        .i_addr(w_s0_dc_tag_addr[$clog2(msrh_lsu_pkg::DCACHE_DATA_B_W) +: msrh_lsu_pkg::DCACHE_TAG_LOW]),
        .i_be  (i_dc_update.be),
        .i_data(i_dc_update.data),
        .o_data(w_s1_data[way])
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
