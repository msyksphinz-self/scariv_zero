// ------------------------------------------------------------------------
// NAME : scariv_dcache_array
// TYPE : module
// ------------------------------------------------------------------------
// SCARIV Data Cache Array
// ------------------------------------------------------------------------
//
// ------------------------------------------------------------------------


module scariv_dcache_array
  #(
    // from LSU Pipeline + STQ Update + PTW
    parameter READ_PORT_NUM = scariv_conf_pkg::LSU_INST_NUM + 1 + 1 + 1
    )
  (
   input logic i_clk,
   input logic i_reset_n,

   input logic [$clog2(scariv_conf_pkg::DCACHE_BANKS)-1: 0] i_bank,   // static

   input scariv_lsu_pkg::dc_wr_req_t     i_dc_wr_req,
   output scariv_lsu_pkg::dc_wr_resp_t   o_dc_wr_resp,
   input scariv_lsu_pkg::dc_read_req_t   i_dc_read_req [READ_PORT_NUM],
   output scariv_lsu_pkg::dc_read_resp_t o_dc_read_resp[READ_PORT_NUM]
   );

//
//                            <------> log2(NWORDS/DCACHE_BANKS) = log2(DCACHE_WORDS_PER_BANK)
//                                   <---> log2(DCACHE_BANKS)
// PADDR_W(TAG_HIGH)   TAG_LOW           <-------> log2(DCACHE_DATA_B_W)
// +--------------------------+------+---+-------+
// |                          |      |   |       |
// +--------------------------+------+---+-------+
//
// Standard configuration
//  1000 0000 0000 0000 0011|0 000 |1  00 0| 0000   0x8000_3080
//  1000 0000 0000 0000 0011|0 000 |1  01 0| 0000   0x8000_30A0
// +--------------------------+------+---+-------+
// |                          |      |   |       |
// +--------------------------+------+---+-------+
// 55                       11 10   7 6 5 4     0
//
//
localparam TAG_SIZE = scariv_lsu_pkg::DCACHE_TAG_HIGH - scariv_lsu_pkg::DCACHE_TAG_LOW + 1;
localparam DCACHE_WORDS_PER_BANK = scariv_conf_pkg::DCACHE_WORDS / scariv_conf_pkg::DCACHE_BANKS;

logic [READ_PORT_NUM-1:0] w_s0_dc_read_req_valid;
logic [READ_PORT_NUM-1:0] w_s0_dc_read_priority;
logic [READ_PORT_NUM-1:0] w_s0_dc_read_req_valid_with_priority;
logic [READ_PORT_NUM-1:0] w_s0_dc_read_req_valid_oh;
scariv_lsu_pkg::dc_read_req_t w_s0_dc_selected_read_req;
logic [READ_PORT_NUM-1:0]       w_s0_dc_read_req_norm_valid_oh;

logic                              w_s0_dc_tag_valid;
logic                              w_s0_dc_tag_wr_valid;
logic                              r_s1_dc_tag_wr_valid;
scariv_pkg::paddr_t                  w_s0_dc_tag_addr;
logic [$clog2(scariv_conf_pkg::DCACHE_WAYS)-1: 0] w_s0_dc_tag_way;

logic [$clog2(scariv_conf_pkg::DCACHE_WAYS)-1: 0] r_s1_dc_tag_way;

logic [READ_PORT_NUM-1:0]       r_s1_dc_read_req_valid;
logic [READ_PORT_NUM-1:0]       r_s1_dc_read_req_valid_oh;
logic [scariv_conf_pkg::DCACHE_DATA_W-1: 0] w_s1_data[scariv_conf_pkg::DCACHE_WAYS];
scariv_lsu_pkg::mesi_t                      w_s1_mesi[scariv_conf_pkg::DCACHE_WAYS];
logic [scariv_conf_pkg::DCACHE_WAYS-1 : 0]  w_s1_tag_valid;
logic [TAG_SIZE-1:0]                      w_s1_tag[scariv_conf_pkg::DCACHE_WAYS];

scariv_pkg::paddr_t          r_s1_dc_tag_addr;

logic [scariv_conf_pkg::DCACHE_WAYS-1 : 0]  w_s1_wr_tag_hit;
logic                                     r_s1_wr_req_valid;
logic [scariv_conf_pkg::DCACHE_DATA_W-1:0]  r_s1_wr_data;
scariv_lsu_pkg::mesi_t                      r_s1_wr_mesi;
logic [scariv_lsu_pkg::DCACHE_DATA_B_W-1:0] r_s1_wr_be;
logic                                     r_s1_wr_data_valid;
logic                                     w_s1_wr_data_valid;

logic [READ_PORT_NUM-1: 0]                        w_s0_dc_rd_wr_conflict;
logic [READ_PORT_NUM-1: 0]                        r_s1_dc_rd_wr_conflict;

logic [$clog2(scariv_conf_pkg::DCACHE_WAYS)-1 : 0] r_replace_target[DCACHE_WORDS_PER_BANK];
logic [READ_PORT_NUM-1: 0]                       w_update_tag_valid;
logic [$clog2(DCACHE_WORDS_PER_BANK)-1: 0]       w_update_tag_addr[READ_PORT_NUM];

// Selection of Request from LSU ports
generate for (genvar p_idx = 0; p_idx < READ_PORT_NUM; p_idx++) begin : lsu_loop
  assign w_s0_dc_read_req_valid[p_idx] = i_dc_read_req[p_idx].valid;
  assign w_s0_dc_read_priority [p_idx] = i_dc_read_req[p_idx].valid & i_dc_read_req[p_idx].high_priority;

  logic w_s0_dc_read_tag_same;
  logic r_s1_dc_read_tag_same;
  logic [riscv_pkg::PADDR_W-1:scariv_lsu_pkg::DCACHE_TAG_LOW] r_s1_dc_lsu_tag_addr;
  logic [scariv_conf_pkg::DCACHE_DATA_W-1: 0]                 w_s1_selected_data;
  scariv_lsu_pkg::mesi_t                                      w_s1_selected_mesi;
  logic [$clog2(DCACHE_WORDS_PER_BANK)-1: 0]                r_s1_dc_tag_low;

  assign w_s0_dc_read_tag_same = w_s0_dc_tag_addr[$clog2(scariv_lsu_pkg::DCACHE_DATA_B_W) +: scariv_lsu_pkg::DCACHE_TAG_LOW] ==
                                 i_dc_read_req[p_idx].paddr[$clog2(scariv_lsu_pkg::DCACHE_DATA_B_W) +: scariv_lsu_pkg::DCACHE_TAG_LOW];
  always_ff @ (posedge i_clk, negedge i_reset_n) begin
    if (!i_reset_n) begin
      r_s1_dc_read_tag_same <= 1'b0;
      r_s1_dc_lsu_tag_addr  <= 'h0;
      r_s1_dc_tag_low       <= 'h0;
    end else begin
      r_s1_dc_read_tag_same <= w_s0_dc_read_tag_same;
      r_s1_dc_lsu_tag_addr  <= i_dc_read_req[p_idx].paddr[riscv_pkg::PADDR_W-1:scariv_lsu_pkg::DCACHE_TAG_LOW];
      r_s1_dc_tag_low       <= w_s0_dc_tag_addr[scariv_lsu_pkg::DCACHE_TAG_LOW-1 -: $clog2(DCACHE_WORDS_PER_BANK)];
    end
  end

  logic [scariv_conf_pkg::DCACHE_WAYS-1 : 0] w_s1_tag_hit;
  for(genvar way_idx = 0; way_idx < scariv_conf_pkg::DCACHE_WAYS; way_idx++) begin : dcache_way_loop
    assign w_s1_tag_hit[way_idx] = (r_s1_dc_lsu_tag_addr == w_s1_tag[way_idx]) & w_s1_tag_valid[way_idx] &
                                   (w_s1_mesi[way_idx] != scariv_lsu_pkg::MESI_INVALID);
  end

`ifdef SIMULATION
  always_ff @ (negedge i_clk, negedge i_reset_n) begin
    if (i_reset_n) begin
      if (!$onehot0(w_s1_tag_hit)) begin
        $fatal(0, "DCache : w_s1_tag_hit should be one-hot : %x\n", w_s1_tag_hit);
      end
    end
  end
`endif // SIMULATION

  bit_oh_or #(.T(logic[scariv_conf_pkg::DCACHE_DATA_W-1:0]), .WORDS(scariv_conf_pkg::DCACHE_WAYS))
  cache_data_sel (.i_oh (w_s1_tag_hit), .i_data(w_s1_data), .o_selected(w_s1_selected_data));
  bit_oh_or #(.T(scariv_lsu_pkg::mesi_t), .WORDS(scariv_conf_pkg::DCACHE_WAYS))
  cache_mesi_sel (.i_oh (w_s1_tag_hit), .i_data(w_s1_mesi), .o_selected(w_s1_selected_mesi));

  logic w_s1_read_req_valid;
  // read_req_valid condition:
  // 1. Not Update Path
  // 2. Read Request
  // 3. Read Request Selected
  // 4. Read Request not selected, but same as selected address line.
  assign w_s1_read_req_valid = !r_s1_wr_req_valid & r_s1_dc_read_req_valid[p_idx] & (r_s1_dc_read_req_valid_oh[p_idx] | r_s1_dc_read_tag_same);

  logic [$clog2(scariv_conf_pkg::DCACHE_WAYS)-1: 0] w_s1_tag_hit_idx;
  encoder #(.SIZE(scariv_conf_pkg::DCACHE_WAYS)) hit_encoder (.i_in(w_s1_tag_hit), .o_out(w_s1_tag_hit_idx));

  assign o_dc_read_resp[p_idx].hit      = w_s1_read_req_valid & (|w_s1_tag_hit);
  assign o_dc_read_resp[p_idx].hit_way  = (|w_s1_tag_hit) ? w_s1_tag_hit_idx : r_replace_target[0];
  assign o_dc_read_resp[p_idx].miss     = w_s1_read_req_valid & ~(|w_s1_tag_hit);
  assign o_dc_read_resp[p_idx].conflict =  r_s1_wr_req_valid |
                                           r_s1_dc_rd_wr_conflict[p_idx] |
                                           r_s1_dc_read_req_valid[p_idx] & !r_s1_dc_read_req_valid_oh[p_idx] & !r_s1_dc_read_tag_same;

  assign o_dc_read_resp[p_idx].data     =  w_s1_selected_data;
  assign o_dc_read_resp[p_idx].mesi     =  w_s1_selected_mesi;

  assign w_update_tag_valid [p_idx] = ~o_dc_read_resp[p_idx].conflict &
                                      o_dc_read_resp[p_idx].miss;
  assign w_update_tag_addr  [p_idx] = r_s1_dc_tag_low;
end
endgenerate

assign w_s0_dc_read_req_valid_with_priority = w_s0_dc_read_priority == 'h0 ? w_s0_dc_read_req_valid : w_s0_dc_read_priority;
bit_extract_lsb #(.WIDTH(READ_PORT_NUM)) u_bit_req_sel (.in(w_s0_dc_read_req_valid_with_priority), .out(w_s0_dc_read_req_norm_valid_oh));
assign w_s0_dc_read_req_valid_oh = w_s0_dc_read_req_norm_valid_oh;
bit_oh_or #(.T(scariv_lsu_pkg::dc_read_req_t), .WORDS(READ_PORT_NUM)) select_rerun_oh  (.i_oh(w_s0_dc_read_req_valid_oh), .i_data(i_dc_read_req), .o_selected(w_s0_dc_selected_read_req));

assign w_s0_dc_tag_valid    = i_dc_wr_req.s0_valid | (|w_s0_dc_read_req_valid);
assign w_s0_dc_tag_wr_valid = i_dc_wr_req.s0_valid & i_dc_wr_req.s0_tag_update_valid;

assign w_s0_dc_tag_addr     = i_dc_wr_req.s0_valid ? i_dc_wr_req.s0_paddr : w_s0_dc_selected_read_req.paddr;
assign w_s0_dc_tag_way      = i_dc_wr_req.s0_way;

assign w_s0_dc_rd_wr_conflict = w_s0_dc_read_req_valid & {READ_PORT_NUM{w_s1_wr_data_valid}};

always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_s1_dc_read_req_valid_oh <= 'h0;
    r_s1_dc_read_req_valid    <= 'h0;
    r_s1_dc_tag_addr          <= 'h0;

    r_s1_wr_req_valid <= 1'b0;
  end else begin
    r_s1_dc_rd_wr_conflict    <= w_s0_dc_rd_wr_conflict;
    r_s1_dc_read_req_valid_oh <= w_s0_dc_read_req_valid_oh;
    r_s1_dc_read_req_valid    <= w_s0_dc_read_req_valid;
    r_s1_dc_tag_addr          <= w_s0_dc_tag_addr;

    r_s1_wr_req_valid <= i_dc_wr_req.s0_valid;
    r_s1_wr_be        <= i_dc_wr_req.s0_be;
    r_s1_wr_data      <= i_dc_wr_req.s0_data;
    r_s1_wr_mesi      <= i_dc_wr_req.s0_mesi;

    r_s1_wr_data_valid <= i_dc_wr_req.s0_valid & ~i_dc_wr_req.s0_tag_update_valid;
    r_s1_dc_tag_wr_valid  <= w_s0_dc_tag_wr_valid;

    r_s1_dc_tag_way <= w_s0_dc_tag_way;

  end
end

logic [scariv_conf_pkg::DCACHE_DATA_W-1: 0] w_s2_evicted_data[scariv_conf_pkg::DCACHE_WAYS];
scariv_lsu_pkg::mesi_t                      w_s2_evicted_mesi[scariv_conf_pkg::DCACHE_WAYS];

assign w_s1_wr_data_valid = r_s1_wr_data_valid & (|w_s1_wr_tag_hit) | r_s1_dc_tag_wr_valid;
for(genvar way = 0; way < scariv_conf_pkg::DCACHE_WAYS; way++) begin : dcache_way_loop
  assign w_s1_wr_tag_hit[way] = (r_s1_dc_tag_addr[riscv_pkg::PADDR_W-1:scariv_lsu_pkg::DCACHE_TAG_LOW] == w_s1_tag[way]) &
                                w_s1_tag_valid[way];
  assign w_s2_evicted_data[way] = w_s1_data[way];  // Actually this is evicted data at s2 stage
  always_ff @ (posedge i_clk) begin
    w_s2_evicted_mesi[way] <= w_s1_mesi[way];;
  end
end

assign o_dc_wr_resp.s1_hit  = |w_s1_wr_tag_hit;
assign o_dc_wr_resp.s1_miss = ~(|w_s1_wr_tag_hit);

logic [scariv_conf_pkg::DCACHE_WAYS-1: 0]  w_s1_dc_tag_way_oh;
logic [TAG_SIZE-1:0]                     w_s1_evicted_sel_tag;
logic                                    w_s1_evicted_sel_tag_valid;
logic [scariv_conf_pkg::DCACHE_WAYS-1: 0]  r_s2_dc_tag_way_oh;
logic [TAG_SIZE-1:0]                     r_s2_tag[scariv_conf_pkg::DCACHE_WAYS];
logic [scariv_conf_pkg::DCACHE_DATA_W-1:0] w_s2_evicted_sel_data;
scariv_lsu_pkg::mesi_t                     w_s2_evicted_sel_mesi;
logic [TAG_SIZE-1:0]                     r_s2_evicted_sel_tag;
logic                                    r_s2_evicted_valid;
scariv_pkg::paddr_t          r_s2_dc_tag_addr;

assign w_s1_dc_tag_way_oh = 'h1 << r_s1_dc_tag_way;

bit_oh_or #(.T(logic[scariv_conf_pkg::DCACHE_DATA_W-1:0]), .WORDS(scariv_conf_pkg::DCACHE_WAYS))
cache_evicted_data_sel (.i_oh (r_s2_dc_tag_way_oh), .i_data(w_s2_evicted_data), .o_selected(w_s2_evicted_sel_data));
bit_oh_or #(.T(scariv_lsu_pkg::mesi_t), .WORDS(scariv_conf_pkg::DCACHE_WAYS))
cache_evicted_mesi_sel (.i_oh (r_s2_dc_tag_way_oh), .i_data(w_s2_evicted_mesi), .o_selected(w_s2_evicted_sel_mesi));

bit_oh_or #(.T(logic[TAG_SIZE-1:0]), .WORDS(scariv_conf_pkg::DCACHE_WAYS))
cache_evicted_tag_sel (.i_oh (w_s1_dc_tag_way_oh), .i_data(w_s1_tag), .o_selected(w_s1_evicted_sel_tag));

assign w_s1_evicted_sel_tag_valid = w_s1_tag_valid[r_s1_dc_tag_way];


always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_s2_dc_tag_way_oh   <= 'h0;
    r_s2_evicted_valid   <= 1'b0;
    r_s2_evicted_sel_tag <= 'h0;
    r_s2_dc_tag_addr     <= 'h0;
  end else begin
    r_s2_dc_tag_way_oh <= w_s1_dc_tag_way_oh;
    r_s2_tag <= w_s1_tag;
    r_s2_evicted_valid         <= (w_s1_evicted_sel_tag != r_s1_dc_tag_addr[riscv_pkg::PADDR_W-1:scariv_lsu_pkg::DCACHE_TAG_LOW]) &
                                  r_s1_dc_tag_wr_valid &
                                  w_s1_evicted_sel_tag_valid;
    r_s2_evicted_sel_tag       <= w_s1_evicted_sel_tag;

    r_s2_dc_tag_addr     <= r_s1_dc_tag_addr;
  end
end

assign o_dc_wr_resp.s2_evicted_valid = r_s2_evicted_valid;
assign o_dc_wr_resp.s2_evicted_paddr = {r_s2_evicted_sel_tag,
                                        r_s2_dc_tag_addr[$clog2(scariv_lsu_pkg::DCACHE_DATA_B_W * scariv_conf_pkg::DCACHE_BANKS) +: $clog2(DCACHE_WORDS_PER_BANK)],
                                        i_bank,
                                        {$clog2(scariv_lsu_pkg::DCACHE_DATA_B_W){1'b0}}};
assign o_dc_wr_resp.s2_evicted_data  = w_s2_evicted_sel_data;
assign o_dc_wr_resp.s2_evicted_mesi  = w_s2_evicted_sel_mesi;


generate for (genvar w_idx = 0; w_idx < DCACHE_WORDS_PER_BANK; w_idx++) begin : tag_loop
  logic [READ_PORT_NUM-1: 0] w_s1_dc_read_resp_miss;
  for (genvar i = 0; i < READ_PORT_NUM; i++) begin
    assign w_s1_dc_read_resp_miss[i] = o_dc_read_resp[i].miss;
  end
  always_ff @ (posedge i_clk, negedge i_reset_n) begin
    if (!i_reset_n) begin
      r_replace_target[w_idx] <= 'h0;
    end else begin
      for (int i = 0; i < READ_PORT_NUM; i++) begin
        if (|r_s1_dc_read_req_valid_oh) begin
          // Temporary : This is sequential and rando mreplace policy
          r_replace_target[w_idx] <= r_replace_target[w_idx] + 'h1;
        end
      end
    end
  end
end
endgenerate


generate for(genvar way = 0; way < scariv_conf_pkg::DCACHE_WAYS; way++) begin : dc_way_loop

  logic [$clog2(DCACHE_WORDS_PER_BANK)-1: 0] w_s0_tag_addr;
  logic [$clog2(DCACHE_WORDS_PER_BANK)-1: 0] r_s1_tag_addr;
  assign w_s0_tag_addr = w_s0_dc_tag_addr[$clog2(scariv_lsu_pkg::DCACHE_DATA_B_W * scariv_conf_pkg::DCACHE_BANKS) +: $clog2(DCACHE_WORDS_PER_BANK)];

  tag_array
    #(
      .TAG_W($bits(scariv_lsu_pkg::mesi_t) + TAG_SIZE),
      .WORDS(DCACHE_WORDS_PER_BANK)
      )
  tag (
       .i_clk(i_clk),
       .i_reset_n(i_reset_n),

       .i_tag_clear  (1'b0),
       .i_wr         (w_s0_dc_tag_wr_valid & (w_s0_dc_tag_way == way)),
       .i_addr       (w_s0_tag_addr),
       .i_tag_valid  (1'b1),
       .i_tag        ({i_dc_wr_req.s0_mesi, i_dc_wr_req.s0_paddr[riscv_pkg::PADDR_W-1:scariv_lsu_pkg::DCACHE_TAG_LOW]}),
       .o_tag        ({w_s1_mesi[way],      w_s1_tag[way]}),
       .o_tag_valid  (w_s1_tag_valid[way])
       );

  logic [$clog2(DCACHE_WORDS_PER_BANK)-1: 0] w_data_addr;
  assign w_data_addr = w_s1_wr_data_valid ?
                       r_s1_dc_tag_addr[$clog2(scariv_lsu_pkg::DCACHE_DATA_B_W * scariv_conf_pkg::DCACHE_BANKS) +: $clog2(DCACHE_WORDS_PER_BANK)] :  // For Data Write
                       w_s0_dc_tag_addr[$clog2(scariv_lsu_pkg::DCACHE_DATA_B_W * scariv_conf_pkg::DCACHE_BANKS) +: $clog2(DCACHE_WORDS_PER_BANK)];   // For Data Read

  logic [$bits(scariv_lsu_pkg::mesi_t)-1: 0] w_mesi_be;
  assign w_mesi_be = {$bits(scariv_lsu_pkg::mesi_t){1'b1}};

  localparam dcache_w = scariv_conf_pkg::DCACHE_DATA_W;

  data_array
    #(
      .WIDTH(dcache_w),
      .WORDS(DCACHE_WORDS_PER_BANK)
      )
  data (
        .i_clk     (i_clk),
        .i_reset_n (i_reset_n),
        .i_wr      (w_s1_wr_data_valid & (r_s1_dc_tag_way == way)  ),
        .i_addr    (w_data_addr                                    ),
        .i_be      (r_s1_wr_be                                     ),
        .i_data    (r_s1_wr_data                                   ),
        .o_data    (w_s1_data[way]                                 )
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

endmodule // scariv_dcache_array
