module msrh_l1d_load_requester
  (
   input logic  i_clk,
   input logic  i_reset_n,

   // from Pipeline for Load + PTW for Load
   l1d_lrq_if.slave l1d_lrq[msrh_conf_pkg::LSU_INST_NUM],
   // from STQ request
   l1d_lrq_if.slave l1d_lrq_stq_miss_if,

   output msrh_lsu_pkg::lrq_resolve_t o_lrq_resolve,

   l2_req_if.master  l1d_ext_rd_req,
   l2_resp_if.slave  l1d_ext_rd_resp,

   // Interface to L1D eviction
   l1d_evict_if.master l1d_evict_if,
   // Search LRQ interface during eviction
   lrq_evict_search_if.slave  lrq_evict_search_if,
   // LRQ search interface
   lrq_search_if.slave lrq_search_if
   );

localparam REQ_PORT_NUM = msrh_conf_pkg::LSU_INST_NUM;


logic [msrh_pkg::LRQ_NORM_ENTRY_SIZE-1: 0] w_norm_lrq_valids;
logic [msrh_pkg::LRQ_NORM_ENTRY_SIZE-1: 0] w_norm_lrq_load_valid_oh;
logic                                      w_lrq_norm_entries_full;

logic [msrh_pkg::LRQ_ENTRY_SIZE-1: 0] w_hit_lrq_same_addr_valid[REQ_PORT_NUM];
logic [REQ_PORT_NUM-1: 0]   w_hit_port_same_addr_valid[REQ_PORT_NUM];
logic [REQ_PORT_NUM-1: 0]   w_resp_confilct;

logic [msrh_pkg::LRQ_NORM_ENTRY_SIZE-1:0] w_norm_in_ptr_oh;
logic [msrh_pkg::LRQ_NORM_ENTRY_SIZE-1:0] w_norm_out_ptr_oh;
logic [$clog2(msrh_pkg::LRQ_NORM_ENTRY_SIZE)-1:0] w_norm_out_ptr;
logic                                        w_in_valid;
logic                                        w_out_valid;
logic [msrh_pkg::LRQ_ENTRY_SIZE-1:0]         w_lrq_load_valid;
logic [msrh_pkg::LRQ_NORM_ENTRY_SIZE-1: 0]   w_norm_lrq_clear_ready;

msrh_lsu_pkg::lrq_entry_t w_lrq_entries[msrh_pkg::LRQ_ENTRY_SIZE];

logic [REQ_PORT_NUM-1: 0]       w_l1d_lrq_loads;
logic [REQ_PORT_NUM-1: 0]       w_l1d_lrq_picked_valids;
logic [REQ_PORT_NUM-1: 0]       w_l1d_lrq_loads_no_conflicts;
logic [$clog2(REQ_PORT_NUM): 0] w_l1d_lrq_loads_cnt;
logic [$clog2(msrh_pkg::LRQ_ENTRY_SIZE):0] r_lrq_remained_size;
logic [$clog2(REQ_PORT_NUM): 0] w_l1d_lrq_valid_load_cnt;
msrh_lsu_pkg::lrq_req_t w_l1d_req_payloads        [REQ_PORT_NUM];
msrh_lsu_pkg::lrq_req_t w_l1d_picked_req_payloads [REQ_PORT_NUM];

logic [msrh_pkg::LRQ_ENTRY_SIZE-1: 0]        w_load_valid [REQ_PORT_NUM] ;
logic [msrh_pkg::LRQ_ENTRY_SIZE-1: 0]        w_load_entry_valid;

logic [msrh_pkg::LRQ_ENTRY_SIZE-1: msrh_pkg::LRQ_NORM_ENTRY_SIZE] w_st_lrq_valids;


// LRQ Miss Load from STQ
logic                                        w_stq_miss_lrq_load;
logic [$clog2(msrh_pkg::LRQ_ENTRY_SIZE)-1:0] w_stq_miss_lrq_idx;
msrh_lsu_pkg::lrq_entry_t                    w_stq_load_entry;


// LRQ Request selection
msrh_lsu_pkg::lrq_entry_t             w_lrq_ready_to_send_entry;
logic [msrh_pkg::LRQ_ENTRY_SIZE-1: 0] w_lrq_ready_to_send;
logic [msrh_pkg::LRQ_ENTRY_SIZE-1: 0] w_lrq_ready_to_send_oh;
logic [$clog2(msrh_pkg::LRQ_ENTRY_SIZE)-1: 0] w_lrq_send_tag;

logic r_rp1_l1d_exp_resp_valid;
logic [msrh_pkg::LRQ_ENTRY_W-1:0] r_rp1_lrq_resp_tag;
logic [msrh_conf_pkg::DCACHE_DATA_W-1: 0] r_rp1_lrq_resp_data;

msrh_lsu_pkg::lrq_entry_t             w_lrq_ready_to_l1d_upddate_entry;
logic [msrh_pkg::LRQ_ENTRY_SIZE-1: 0] w_lrq_ready_to_l1d_upddate;
logic [msrh_pkg::LRQ_ENTRY_SIZE-1: 0] w_lrq_ready_to_l1d_upddate_oh;

msrh_lsu_pkg::lrq_entry_t             w_lrq_ready_to_evict_entry;
logic [msrh_pkg::LRQ_ENTRY_SIZE-1: 0] w_lrq_ready_to_evict;
logic [msrh_pkg::LRQ_ENTRY_SIZE-1: 0] w_lrq_ready_to_evict_oh;
logic [$clog2(msrh_pkg::LRQ_ENTRY_SIZE)-1: 0] w_lrq_evict_tag;

// LRQ Search Registers
logic                                         r_lrq_search_valid;
logic [msrh_pkg::LRQ_ENTRY_SIZE-1: 0]         r_lrq_search_index_oh;


logic [msrh_pkg::LRQ_ENTRY_SIZE-1: 0]         w_s0_evict_search_hit;

bit_extract_lsb #(.WIDTH(msrh_pkg::LRQ_NORM_ENTRY_SIZE)) u_load_valid (.in(~w_norm_lrq_valids), .out(w_norm_lrq_load_valid_oh));
bit_cnt #(.WIDTH(REQ_PORT_NUM)) u_lrq_req_cnt(.in(w_l1d_lrq_loads_no_conflicts), .out(w_l1d_lrq_loads_cnt));

/* verilator lint_off WIDTH */
assign w_l1d_lrq_valid_load_cnt = r_lrq_remained_size > w_l1d_lrq_loads_cnt ? w_l1d_lrq_loads_cnt : r_lrq_remained_size;

always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_lrq_remained_size <= msrh_pkg::LRQ_NORM_ENTRY_SIZE;
  end else begin
    r_lrq_remained_size <= r_lrq_remained_size -
                           (w_in_valid ? w_l1d_lrq_valid_load_cnt : 'h0) +
                           (w_out_valid ? 'h1 : 'h0);
  end
end

//
// LRQ Pointer
//
assign w_in_valid  = |w_l1d_lrq_loads_no_conflicts;
assign w_out_valid = r_lrq_search_valid & (|r_lrq_search_index_oh[msrh_pkg::LRQ_NORM_ENTRY_SIZE-1: 0]);

inoutptr_var_oh #(.SIZE(msrh_pkg::LRQ_NORM_ENTRY_SIZE)) u_req_ptr(.i_clk (i_clk), .i_reset_n(i_reset_n),
                                                                  .i_rollback(1'b0),
                                                                  .i_in_valid (w_in_valid ),
                                                                  /* verilator lint_off WIDTH */
                                                                  .i_in_val({{($clog2(msrh_pkg::LRQ_ENTRY_SIZE)-$clog2(msrh_conf_pkg::LSU_INST_NUM)-1){1'b0}}, w_l1d_lrq_valid_load_cnt}),
                                                                  .o_in_ptr_oh (w_norm_in_ptr_oh ),

                                                                  .i_out_valid(w_out_valid),
                                                                  .i_out_val({{($clog2(msrh_pkg::LRQ_ENTRY_SIZE)-1){1'b0}}, 1'b1}),
                                                                  .o_out_ptr_oh(w_norm_out_ptr_oh));

encoder #(.SIZE(msrh_pkg::LRQ_ENTRY_SIZE)) u_bit_out_ptr_encoder (.i_in(w_norm_out_ptr_oh), .o_out(w_norm_out_ptr));

generate for (genvar p_idx = 0; p_idx < REQ_PORT_NUM; p_idx++) begin : lsu_req_loop
  assign w_l1d_lrq_loads[p_idx] = l1d_lrq[p_idx].load;
  assign w_l1d_req_payloads[p_idx] = l1d_lrq[p_idx].req_payload;
  assign w_l1d_lrq_loads_no_conflicts[p_idx] = w_l1d_lrq_loads[p_idx] &
                                               !w_resp_confilct[p_idx];
  bit_pick_1_index
                             #(.NUM(p_idx),
                               .SEL_WIDTH(REQ_PORT_NUM),
                               .DATA_WIDTH($size(msrh_lsu_pkg::lrq_req_t))
                               )
  u_l1d_req_pick
                             (
                              .i_valids(w_l1d_lrq_loads_no_conflicts),
                              .i_data  (w_l1d_req_payloads),

                              .o_valid (w_l1d_lrq_picked_valids  [p_idx]),
                              .o_data  (w_l1d_picked_req_payloads[p_idx]),
                              .o_picked_pos()
                              );
end
endgenerate

// Full condition: next target input entry is still "valid".
assign w_lrq_norm_entries_full = |(w_norm_in_ptr_oh & w_norm_lrq_valids);

logic [msrh_pkg::LRQ_ENTRY_SIZE-1: 0] w_rp1_lrq_resp_tag_oh;
assign w_rp1_lrq_resp_tag_oh = 1 << r_rp1_lrq_resp_tag;


// ---------------------
// Eviction Data Search
// ---------------------
always_ff @ (posedge i_clk, negedge i_reset_n) begin
    if (!i_reset_n) begin
      lrq_evict_search_if.s1_hit_merged <= 1'b0;
    end else begin
      lrq_evict_search_if.s1_hit_merged <= |w_s0_evict_search_hit;
    end
end

generate for (genvar b_idx = 0; b_idx < msrh_pkg::LRQ_ENTRY_SIZE; b_idx++) begin : buffer_loop

  // ---------------------
  // Eviction Data Search
  // ---------------------
  assign w_s0_evict_search_hit[b_idx] = w_lrq_entries[b_idx].valid &
                                     w_lrq_entries[b_idx].evict_valid &
                                     ~w_lrq_entries[b_idx].evict_sent &
                                     lrq_evict_search_if.s0_valid &
                                     (w_lrq_entries[b_idx].evict.paddr[riscv_pkg::PADDR_W-1: $clog2(msrh_lsu_pkg::DCACHE_DATA_B_W)] ==
                                      lrq_evict_search_if.s0_paddr [riscv_pkg::PADDR_W-1: $clog2(msrh_lsu_pkg::DCACHE_DATA_B_W)]);
  msrh_lsu_pkg::evict_merge_t w_evict_merge;
  assign w_evict_merge.valid = lrq_evict_search_if.s0_valid & w_s0_evict_search_hit[b_idx];
  assign w_evict_merge.data  = lrq_evict_search_if.s0_data;
  assign w_evict_merge.be    = lrq_evict_search_if.s0_strb << lrq_evict_search_if.s0_paddr[$clog2(msrh_lsu_pkg::DCACHE_DATA_B_W)-1: 0];


  if (b_idx < msrh_pkg::LRQ_NORM_ENTRY_SIZE) begin : normal_entry
    // ----------------------------
    // Load Miss Request
    // ----------------------------

    assign w_norm_lrq_valids[b_idx] = w_lrq_entries[b_idx].valid;
    msrh_lsu_pkg::lrq_req_t w_l1d_picked_req_payloads_oh;

    for (genvar p_idx = 0; p_idx < REQ_PORT_NUM; p_idx++) begin : lrq_port_loop
      logic [msrh_pkg::LRQ_ENTRY_SIZE-1: 0]  w_entry_ptr_oh;
      bit_rotate_left #(.WIDTH(msrh_pkg::LRQ_ENTRY_SIZE), .VAL(p_idx)) target_bit_rotate (.i_in(w_norm_in_ptr_oh), .o_out(w_entry_ptr_oh));
      assign w_load_valid[p_idx][b_idx] = w_l1d_lrq_picked_valids[p_idx] & w_entry_ptr_oh[b_idx] & (p_idx < w_l1d_lrq_valid_load_cnt);
    end

    logic [REQ_PORT_NUM-1: 0] w_rev_load_valid;
    for (genvar p_idx = 0; p_idx < msrh_conf_pkg::LSU_INST_NUM; p_idx++) begin : rev_loop
      assign w_rev_load_valid[p_idx] =  w_load_valid[p_idx][b_idx];
    end

    assign w_load_entry_valid[b_idx] = |w_rev_load_valid;

    bit_oh_or #(.T(msrh_lsu_pkg::lrq_req_t), .WORDS(REQ_PORT_NUM)) bit_oh_paddr (.i_oh(w_rev_load_valid), .i_data(w_l1d_picked_req_payloads), .o_selected(w_l1d_picked_req_payloads_oh));

    msrh_lsu_pkg::lrq_entry_t load_entry;
    assign load_entry = msrh_lsu_pkg::assign_lrq_entry(w_load_entry_valid[b_idx],
                                                       w_l1d_picked_req_payloads_oh);

    msrh_lrq_entry
      u_entry
        (
         .i_clk     (i_clk    ),
         .i_reset_n (i_reset_n),

         .i_load       (w_load_entry_valid[b_idx]),
         .i_load_entry (load_entry),

         .i_clear (r_lrq_search_valid & r_lrq_search_index_oh[b_idx]),

         .i_evict_merge (w_evict_merge),

         .i_sent       (l1d_ext_rd_req.valid & l1d_ext_rd_req.ready & w_lrq_ready_to_send_oh[b_idx]),
         .i_evict_sent (l1d_evict_if.valid   & l1d_evict_if.ready   & w_lrq_ready_to_evict_oh[b_idx]),
         .o_entry (w_lrq_entries[b_idx])
         );
  end else begin : stq_entry // if (b_idx < msrh_pkg::LRQ_NORM_ENTRY_SIZE)
    // ----------------------------
    // STQ Load Request
    // ----------------------------

    assign w_st_lrq_valids[b_idx] = w_lrq_entries[b_idx].valid;

    msrh_lrq_entry
      u_entry
        (
         .i_clk     (i_clk    ),
         .i_reset_n (i_reset_n),

         .i_load       (w_stq_miss_lrq_load & w_stq_miss_lrq_idx == b_idx),
         .i_load_entry (w_stq_load_entry),

         .i_evict_merge (w_evict_merge),

         .i_clear (r_lrq_search_valid & r_lrq_search_index_oh[b_idx]),

         .i_sent       (l1d_ext_rd_req.valid & l1d_ext_rd_req.ready & w_lrq_ready_to_send_oh[b_idx]),
         .i_evict_sent (l1d_evict_if.valid   & l1d_evict_if.ready   & w_lrq_ready_to_evict_oh[b_idx]),
         .o_entry (w_lrq_entries[b_idx])
         );

  end // else: !if(b_idx < msrh_pkg::LRQ_NORM_ENTRY_SIZE)

end // block: buffer_loop
endgenerate

generate for (genvar p_idx = 0; p_idx < REQ_PORT_NUM; p_idx++) begin : port_loop
  // check the address with different pipeline
  for (genvar p2_idx = 0; p2_idx < REQ_PORT_NUM; p2_idx++) begin : adj_port_loop
    if (p_idx <= p2_idx) begin
      assign w_hit_port_same_addr_valid[p_idx][p2_idx] = 1'b0;
    end else begin
      assign w_hit_port_same_addr_valid[p_idx][p2_idx] = l1d_lrq[p_idx].load & l1d_lrq[p2_idx].load &
                                                       (l1d_lrq[p_idx ].req_payload.paddr[riscv_pkg::PADDR_W-1:$clog2(msrh_lsu_pkg::DCACHE_DATA_B_W)] ==
                                                        l1d_lrq[p2_idx].req_payload.paddr[riscv_pkg::PADDR_W-1:$clog2(msrh_lsu_pkg::DCACHE_DATA_B_W)]);
    end
  end

  // check the address with exist lrq
  for (genvar b_idx = 0; b_idx < msrh_pkg::LRQ_ENTRY_SIZE; b_idx++) begin : buffer_loop
    assign w_hit_lrq_same_addr_valid[p_idx][b_idx] = l1d_lrq[p_idx].load &
                                                     w_lrq_entries[b_idx].valid &
                                                     (w_lrq_entries[b_idx].paddr[riscv_pkg::PADDR_W-1:$clog2(msrh_lsu_pkg::DCACHE_DATA_B_W)] ==
                                                      l1d_lrq[p_idx].req_payload.paddr[riscv_pkg::PADDR_W-1:$clog2(msrh_lsu_pkg::DCACHE_DATA_B_W)]);
  end

  assign w_resp_confilct[p_idx] = (|w_hit_lrq_same_addr_valid[p_idx]) | (|w_hit_port_same_addr_valid[p_idx]);
  assign l1d_lrq[p_idx].resp_payload.full         = (p_idx >= w_l1d_lrq_valid_load_cnt);
  assign l1d_lrq[p_idx].resp_payload.conflict     = |w_hit_lrq_same_addr_valid[p_idx];
  assign l1d_lrq[p_idx].resp_payload.lrq_index_oh = w_hit_lrq_same_addr_valid[p_idx];

`ifdef SIMULATION
  always @(negedge i_clk, negedge i_reset_n) begin
    if (!i_reset_n) begin
    end else begin
      if (!$onehot0(l1d_lrq[p_idx].resp_payload.lrq_index_oh)) begin
        $fatal (0, "l1d_lrq[%d].resp_payload.lrq_index_oh must be one hot but actually %x\n", p_idx, l1d_lrq[p_idx].resp_payload.lrq_index_oh);
      end
    end
  end
`endif // SIMULATION
end
endgenerate

// ---------------------------------------
// Interface of Filling L1D for STQ
// ---------------------------------------
logic [msrh_pkg::LRQ_ENTRY_SIZE-1: 0] w_hit_stq_lrq_same_addr_valid;
assign l1d_lrq_stq_miss_if.resp_payload.full         = l1d_lrq_stq_miss_if.load &
                                                       &w_st_lrq_valids;

for (genvar b_idx = 0; b_idx < msrh_pkg::LRQ_ENTRY_SIZE; b_idx++) begin : stq_buffer_loop
  assign w_hit_stq_lrq_same_addr_valid[b_idx] = l1d_lrq_stq_miss_if.load &
                                                w_lrq_entries[b_idx].valid &
                                                (w_lrq_entries[b_idx].paddr[riscv_pkg::PADDR_W-1:$clog2(msrh_lsu_pkg::DCACHE_DATA_B_W)] ==
                                                 l1d_lrq_stq_miss_if.req_payload.paddr[riscv_pkg::PADDR_W-1:$clog2(msrh_lsu_pkg::DCACHE_DATA_B_W)]) &
                                                ~(o_lrq_resolve.valid & o_lrq_resolve.resolve_index_oh[b_idx]);  // L1D is loaded, Entry resolved
end

assign l1d_lrq_stq_miss_if.resp_payload.conflict     = |w_hit_stq_lrq_same_addr_valid;
assign l1d_lrq_stq_miss_if.resp_payload.lrq_index_oh =  w_hit_stq_lrq_same_addr_valid;
assign w_stq_miss_lrq_load = l1d_lrq_stq_miss_if.load &
                             !l1d_lrq_stq_miss_if.resp_payload.full & !(|w_hit_stq_lrq_same_addr_valid);
assign w_stq_miss_lrq_idx  = w_lrq_entries[msrh_pkg::LRQ_ENTRY_SIZE-2].valid ? msrh_pkg::LRQ_ENTRY_SIZE-1 : msrh_pkg::LRQ_ENTRY_SIZE-2;
assign w_stq_load_entry = msrh_lsu_pkg::assign_lrq_entry(1'b1, l1d_lrq_stq_miss_if.req_payload);

localparam TAG_FILLER_W = msrh_lsu_pkg::L2_CMD_TAG_W - 2 - $clog2(msrh_pkg::LRQ_ENTRY_SIZE);

// selection of external memory request
generate for (genvar b_idx = 0; b_idx < msrh_pkg::LRQ_ENTRY_SIZE; b_idx++) begin : lrq_sel_loop
  assign w_lrq_ready_to_send[b_idx] = w_lrq_entries[b_idx].valid &
                                      !w_lrq_entries[b_idx].sent;

  assign w_lrq_ready_to_evict[b_idx] = w_lrq_entries[b_idx].valid &
                                       w_lrq_entries[b_idx].evict_valid &
                                       !w_lrq_entries[b_idx].evict_sent;
end
endgenerate
bit_extract_lsb_ptr #(.WIDTH(msrh_pkg::LRQ_ENTRY_SIZE)) u_bit_send_sel (.in(w_lrq_ready_to_send), .i_ptr(w_norm_out_ptr), .out(w_lrq_ready_to_send_oh));
encoder#(.SIZE(msrh_pkg::LRQ_ENTRY_SIZE)) u_bit_send_tag_encoder (.i_in(w_lrq_ready_to_send_oh), .o_out(w_lrq_send_tag));
bit_oh_or #(.T(msrh_lsu_pkg::lrq_entry_t), .WORDS(msrh_pkg::LRQ_ENTRY_SIZE)) select_send_entry  (.i_oh(w_lrq_ready_to_send_oh), .i_data(w_lrq_entries), .o_selected(w_lrq_ready_to_send_entry));

bit_extract_lsb_ptr #(.WIDTH(msrh_pkg::LRQ_ENTRY_SIZE)) u_bit_evict_sel (.in(w_lrq_ready_to_evict), .i_ptr(w_norm_out_ptr), .out(w_lrq_ready_to_evict_oh));
encoder#(.SIZE(msrh_pkg::LRQ_ENTRY_SIZE)) u_bit_evict_tag_encoder (.i_in(w_lrq_ready_to_evict_oh), .o_out(w_lrq_evict_tag));
bit_oh_or #(.T(msrh_lsu_pkg::lrq_entry_t), .WORDS(msrh_pkg::LRQ_ENTRY_SIZE)) select_evict_entry  (.i_oh(w_lrq_ready_to_evict_oh), .i_data(w_lrq_entries), .o_selected(w_lrq_ready_to_evict_entry));


assign l1d_ext_rd_req.valid = w_lrq_ready_to_send_entry.valid & !w_lrq_ready_to_send_entry.sent;
assign l1d_ext_rd_req.payload.cmd     = msrh_lsu_pkg::M_XRD;
assign l1d_ext_rd_req.payload.addr    = w_lrq_ready_to_send_entry.paddr;
assign l1d_ext_rd_req.payload.tag     = {msrh_lsu_pkg::L2_UPPER_TAG_RD_L1D, {TAG_FILLER_W{1'b0}}, w_lrq_send_tag};
assign l1d_ext_rd_req.payload.data    = 'h0;
assign l1d_ext_rd_req.payload.byte_en = 'h0;

// -----------------
// Eviction Request
// -----------------
assign l1d_evict_if.valid = w_lrq_ready_to_evict_entry.valid &
                            w_lrq_ready_to_evict_entry.evict_valid &
                            !w_lrq_ready_to_evict_entry.evict_sent;
// assign l1d_evict_if.payload.cmd     = msrh_lsu_pkg::M_XWR;
// assign l1d_evict_if.payload.tag     = {msrh_lsu_pkg::L2_UPPER_TAG_RD_L1D, {TAG_FILLER_W{1'b0}}, w_lrq_evict_tag};
assign l1d_evict_if.payload.paddr = w_lrq_ready_to_evict_entry.evict.paddr;
assign l1d_evict_if.payload.data  = w_lrq_ready_to_evict_entry.evict.data;

// Searching LRQ Interface from DCache
assign lrq_search_if.lrq_entry = w_lrq_entries[lrq_search_if.index];

// Notification to LRQ resolve to LDQ
// Note: Now searching from LRQ means L1D will be written and resolve confliction
always_ff @ (posedge i_clk, posedge i_reset_n) begin
  if (!i_reset_n) begin
    o_lrq_resolve <= 'h0;

    r_lrq_search_valid <= 1'b0;
    r_lrq_search_index_oh <= 'h0;
  end else begin
    r_lrq_search_valid <= lrq_search_if.valid;
    r_lrq_search_index_oh <= 1 << lrq_search_if.index;

    o_lrq_resolve.valid            <= r_lrq_search_valid;
    o_lrq_resolve.resolve_index_oh <= r_lrq_search_index_oh;
  end
end

initial begin
  assert (msrh_lsu_pkg::L2_CMD_TAG_W >= $clog2(msrh_pkg::LRQ_ENTRY_SIZE) + 1);
end

endmodule // msrh_l1d_load_requester
