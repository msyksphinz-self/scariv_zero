// ------------------------------------------------------------------------
// NAME : MSRH Load Requseter (LRQ) for L1D
// TYPE : module
// ------------------------------------------------------------------------
// L1D Load Requestor and Replace Data
// ------------------------------------------------------------------------
//
// ------------------------------------------------------------------------

module msrh_load_requester
  (
   input logic  i_clk,
   input logic  i_reset_n,

   // from Pipeline for Load + PTW for Load
   l1d_lrq_if.slave l1d_lrq[msrh_conf_pkg::LSU_INST_NUM],
   // from LS-Pipe hazard check
   lrq_haz_check_if.slave lrq_haz_check_if[msrh_conf_pkg::LSU_INST_NUM],

   // from STQ request
   l1d_lrq_if.slave lrq_stq_if,

   // Information of LRQ
   output msrh_lsu_pkg::lrq_resolve_t o_lrq_resolve,
   output logic                       o_lrq_is_full,

   // L2 External Interface
   l2_req_if.master  l1d_ext_rd_req,
   l2_resp_if.slave  l1d_ext_rd_resp,

   // Interface to L1D eviction to Store Requestor
   l1d_evict_if.master l1d_evict_if,

   // LRQ search interface (from DCache)
   lrq_search_if.slave lrq_search_if
   );

logic [REQ_PORT_NUM-1: 0]   w_resp_conflict;
logic [REQ_PORT_NUM-1: 0]   w_resp_evict_conflict;

logic [REQ_PORT_NUM-1: 0]       w_l1d_lrq_loads;
msrh_lsu_pkg::lrq_req_t         w_l1d_req_payloads        [REQ_PORT_NUM];
msrh_lsu_pkg::lrq_req_t         w_l1d_picked_req_payloads [REQ_PORT_NUM];
logic [REQ_PORT_NUM-1: 0]       w_l1d_lrq_loads_no_conflicts;

msrh_lsu_pkg::lrq_entry_t w_lrq_entries[msrh_pkg::LRQ_ENTRY_SIZE];

// -------------------------------------
// Conflict Check of Normal LRQ Entries
// -------------------------------------
function automatic logic hit_lrq_same_pa (logic valid, logic [riscv_pkg::PADDR_W-1: 0] req_paddr,
                                          msrh_lsu_pkg::lrq_entry_t lrq_entry,
                                          logic [$clog2(msrh_pkg::LRQ_ENTRY_SIZE)-1: 0] entry_idx);

  return valid &
    lrq_entry.valid &
      ~(o_lrq_resolve.valid & o_lrq_resolve.resolve_index_oh[entry_idx]) &
        (lrq_entry.paddr[riscv_pkg::PADDR_W-1:$clog2(msrh_lsu_pkg::DCACHE_DATA_B_W)] ==
         req_paddr[riscv_pkg::PADDR_W-1:$clog2(msrh_lsu_pkg::DCACHE_DATA_B_W)]);

endfunction // hit_lrq_same_pa

function automatic logic hit_lrq_same_evict_pa (logic valid, logic [riscv_pkg::PADDR_W-1: 0] req_evict_paddr,
                                                msrh_lsu_pkg::lrq_entry_t lrq_entry,
                                                logic [$clog2(msrh_pkg::LRQ_ENTRY_SIZE)-1: 0] entry_idx);

  return valid &
    lrq_entry.valid &
      ~(o_lrq_resolve.valid & o_lrq_resolve.resolve_index_oh[entry_idx]) &
        (lrq_entry.evict.paddr[riscv_pkg::PADDR_W-1:$clog2(msrh_lsu_pkg::DCACHE_DATA_B_W)] ==
         req_evict_paddr[riscv_pkg::PADDR_W-1:$clog2(msrh_lsu_pkg::DCACHE_DATA_B_W)]);

endfunction // hit_lrq_same_pa


function automatic logic hit_port_pa (logic p0_valid, logic p1_valid,
                                      logic [riscv_pkg::PADDR_W-1: 0] p0_pa,
                                      logic [riscv_pkg::PADDR_W-1: 0] p1_pa);
  return p0_valid & p1_valid &
    (p0_pa[riscv_pkg::PADDR_W-1:$clog2(msrh_lsu_pkg::DCACHE_DATA_B_W)] ==
     p1_pa[riscv_pkg::PADDR_W-1:$clog2(msrh_lsu_pkg::DCACHE_DATA_B_W)]);

endfunction // hit_port_pa


generate for (genvar p_idx = 0; p_idx < REQ_PORT_NUM; p_idx++) begin : port_loop
  if (p_idx == 0) begin
    assign w_valid_load_index[p_idx] = w_l1d_lrq_loads_no_conflicts[p_idx] ? 1 : 0;
  end else begin
    assign w_valid_load_index[p_idx] = w_l1d_lrq_loads_no_conflicts[p_idx] ? w_valid_load_index[p_idx-1] + 'h1 :
                                       w_valid_load_index[p_idx-1];
  end

  // 1. check the address with exist lrq
  logic [msrh_pkg::LRQ_ENTRY_SIZE-1: 0] w_hit_lrq_same_pa;
  for (genvar e_idx = 0; e_idx < msrh_pkg::LRQ_ENTRY_SIZE; e_idx++) begin : entry_loop
    assign w_hit_lrq_same_pa[e_idx] = hit_lrq_same_pa (l1d_lrq[p_idx].load, l1d_lrq[p_idx].req_payload.paddr,
                                                       w_lrq_entries[e_idx], e_idx);
  end

  // 2. check the address with different pipeline
  logic [REQ_PORT_NUM-1: 0]             w_hit_port_same_pa;
  for (genvar p2_idx = 0; p2_idx < REQ_PORT_NUM; p2_idx++) begin : adj_port_loop
    if (p_idx <= p2_idx) begin
      assign w_hit_port_same_pa[p2_idx] = 1'b0;
    end else begin
      assign w_hit_port_same_pa[p2_idx] = hit_port_pa (l1d_lrq[p_idx].load, w_l1d_lrq_picked_valids[p2_idx],
                                                       l1d_lrq[p_idx ].req_payload.paddr,
                                                       w_l1d_picked_req_payloads[p2_idx].paddr);
    end
  end

  logic [REQ_PORT_NUM-1: 0] w_hit_port_same_pa_lsb;
  logic [msrh_pkg::LRQ_ENTRY_SIZE-1: 0] w_hit_port_same_pa_load_valid;
  bit_extract_lsb #(.WIDTH(REQ_PORT_NUM)) u_same_port_lsb (.in(w_hit_port_same_pa), .out(w_hit_port_same_pa_lsb));
  bit_oh_or #(.T(msrh_pkg::LRQ_ENTRY_SIZE), .WORDS(REQ_PORT_NUM)) select_port_pa_entry  (.i_oh(w_hit_port_same_pa_lsb), .i_data(w_load_picked_valid), .o_selected(w_hit_port_same_pa_load_valid));

  // 3. check the evicted address with existed evict LRQ
  logic [msrh_pkg::LRQ_ENTRY_SIZE-1: 0] w_hit_lrq_same_evict_pa;
  for (genvar e_idx = 0; e_idx < msrh_pkg::LRQ_ENTRY_SIZE; e_idx++) begin : entry_evict_loop
    assign w_hit_lrq_same_evict_pa[e_idx] = hit_lrq_same_evict_pa (l1d_lrq[p_idx].load, l1d_lrq[p_idx].req_payload.evict_payload.paddr
                                                                   w_lrq_entries[e_idx], e_idx);
  end

  // 4. check the evicted address with different pipeline
  logic [REQ_PORT_NUM-1: 0]             w_hit_port_same_evict_pa;
  for (genvar p2_idx = 0; p2_idx < REQ_PORT_NUM; p2_idx++) begin : adj_evict_port_loop
    if (p_idx <= p2_idx) begin
      assign w_hit_port_same_evict_pa[p2_idx] = 1'b0;
    end else begin
      assign w_hit_port_same_evict_pa[p2_idx] = hit_port_pa (l1d_lrq[p_idx ].load & l1d_lrq[p_idx ].req_payload.evict_valid,
                                                             l1d_lrq[p2_idx].load & l1d_lrq[p2_idx].req_payload.evict_valid,
                                                             l1d_lrq[p_idx ].req_payload.evict_payload.paddr,
                                                             l1d_lrq[p2_idx].req_payload.evict_payload.paddr);
    end
  end

  logic [REQ_PORT_NUM-1: 0] w_hit_port_same_evict_pa_lsb;
  logic [msrh_pkg::LRQ_ENTRY_SIZE-1: 0] w_hit_port_same_evict_pa_load_valid
  bit_extract_lsb #(.WIDTH(REQ_PORT_NUM)) u_same_port_lsb (.in(w_hit_port_same_evict_pa[p_idx]), .out(w_hit_port_same_evict_pa_lsb));
  bit_oh_or #(.T(msrh_pkg::LRQ_ENTRY_SIZE), .WORDS(REQ_PORT_NUM)) select_port_evict_pa_entry  (.i_oh(w_hit_port_same_evict_pa_lsb), .i_data(w_load_picked_valid), .o_selected(w_hit_port_same_evict_pa_load_valid));

  assign w_resp_conflict[p_idx] = (|w_hit_lrq_same_pa) |  // 1. hazard
                                  (|w_hit_port_same_pa);   // 2. hazard

  assign w_resp_evict_conflict[p_idx] = (|w_hit_lrq_same_evict_pa) |  // 3. hazard
                                        (|w_hit_port_same_evict_pa);   // 4. hazard

  assign l1d_lrq[p_idx].resp_payload.full           = (w_valid_load_index[p_idx] > w_l1d_lrq_valid_load_cnt);
  assign l1d_lrq[p_idx].resp_payload.evict_conflict = w_resp_evict_conflict[p_idx];
  assign l1d_lrq[p_idx].resp_payload.conflict       = w_resp_conflict[p_idx];
  assign l1d_lrq[p_idx].resp_payload.lrq_index_oh   = |w_l1d_lrq_loads_no_conflicts[p_idx] ? w_load_picked_valid[w_l1d_lrq_picked_index_enc[p_idx]] : // Success Load
                                                      |w_hit_lrq_same_pa        ? w_hit_lrq_same_pa                   :                               // 1. hazard
                                                      |w_hit_port_same_pa       ? w_hit_port_same_pa_load_valid       :                               // 2. hazard
                                                      |w_hit_lrq_same_evict_pa  ? w_hit_lrq_same_evict_pa             :                               // 3. hazard
                                                      |w_hit_port_same_evict_pa ? w_hit_port_same_evict_pa_load_valid :                               // 4. hazard
                                                      'h0;

end // block: port_loop
endgenerate

// -------------------------------------
// Conflict check of Store LRQ Entries
// -------------------------------------

// 1. check the address with exist lrq
logic [msrh_pkg::LRQ_ENTRY_SIZE-1: 0]   w_hit_lrq_same_pa;
for (genvar e_idx = 0; e_idx < msrh_pkg::LRQ_ENTRY_SIZE; e_idx++) begin : entry_loop
  assign w_hit_stq_same_pa[e_idx] = hit_lrq_same_pa (lrq_stq_if.load, lrq_stq_if.req_payload.paddr,
                                                     w_lrq_entries[e_idx], e_idx);
end

// 2. check the address with different pipeline
logic [REQ_PORT_NUM-1: 0]             w_hit_stq_port_same_pa;
for (genvar p2_idx = 0; p2_idx < REQ_PORT_NUM; p2_idx++) begin : adj_port_loop
  if (p_idx <= p2_idx) begin
    assign w_hit_stq_port_same_pa[p2_idx] = 1'b0;
  end else begin
    assign w_hit_stq_port_same_pa[p2_idx] = hit_port_pa (lrq_stq_if.load, w_l1d_lrq_picked_valids[p2_idx],
                                                         l1d_stq_if.req_payload.paddr,
                                                         w_l1d_picked_req_payloads[p2_idx].paddr);
  end
end

logic [REQ_PORT_NUM-1: 0] w_hit_stq_port_same_pa_lsb;
logic [msrh_pkg::LRQ_ENTRY_SIZE-1: 0] w_hit_stq_port_same_pa_load_valid;
bit_extract_lsb #(.WIDTH(REQ_PORT_NUM)) u_stq_same_port_lsb (.in(w_hit_stq_port_same_pa), .out(w_hit_stq_port_same_pa_lsb));
bit_oh_or #(.T(msrh_pkg::LRQ_ENTRY_SIZE), .WORDS(REQ_PORT_NUM)) select_stq_port_pa_entry  (.i_oh(w_hit_stq_port_same_pa_lsb), .i_data(w_load_picked_valid), .o_selected(w_hit_stq_port_same_pa_load_valid));

// 3. check the evicted address with existed evict LRQ
logic [msrh_pkg::LRQ_ENTRY_SIZE-1: 0] w_hit_lrq_same_evict_pa;
for (genvar e_idx = 0; e_idx < msrh_pkg::LRQ_ENTRY_SIZE; e_idx++) begin : entry_evict_loop

  assign w_hit_lrq_same_evict_pa[e_idx] = hit_lrq_same_evict_pa (lrq_stq_if.load, lrq_stq_if.req_payload.evict_payload.paddr,
                                                                 w_lrq_entries[e_idx], e_idx);
end

// 4. check the evicted address with different pipeline
logic [REQ_PORT_NUM-1: 0]             w_hit_port_same_evict_pa;
for (genvar p2_idx = 0; p2_idx < REQ_PORT_NUM; p2_idx++) begin : adj_evict_port_loop
  if (p_idx <= p2_idx) begin
    assign w_hit_port_same_evict_pa[p2_idx] = 1'b0;
  end else begin
    assign w_hit_port_same_evict_pa[p2_idx] = hit_port_pa(l1d_lrq[p_idx ].load & l1d_lrq[p_idx ].req_payload.evict_valid,
                                                          l1d_lrq[p2_idx].load & l1d_lrq[p2_idx].req_payload.evict_valid,
                                                          l1d_lrq[p_idx ].req_payload.evict_payload.paddr,
                                                          l1d_lrq[p2_idx].req_payload.evict_payload.paddr);
  end
end

logic [REQ_PORT_NUM-1: 0] w_hit_stq_port_same_evict_pa_lsb;
logic [msrh_pkg::LRQ_ENTRY_SIZE-1: 0] w_hit_stq_port_same_evict_pa_load_valid;
bit_extract_lsb #(.WIDTH(REQ_PORT_NUM)) u_same_port_lsb (.in(w_hit_stq_port_same_evict_pa[p_idx]), .out(w_hit_stq_port_same_evict_pa_lsb));
bit_oh_or #(.T(msrh_pkg::LRQ_ENTRY_SIZE), .WORDS(REQ_PORT_NUM)) select_port_stq_evict_pa_entry  (.i_oh(w_hit_stq_port_same_evict_pa_lsb), .i_data(w_load_picked_valid), .o_selected(w_hit_stq_port_same_evict_pa_load_valid));

assign w_resp_conflict[p_idx] = (|w_hit_stq_lrq_same_pa) |  // 1. hazard
                                (|w_hit_stq_port_same_pa);   // 2. hazard

assign w_resp_evict_conflict[p_idx] = (|w_hit_stq_lrq_same_evict_pa) |  // 3. hazard
                                      (|w_hit_stq_port_same_evict_pa);   // 4. hazard

assign lrq_stq_if.resp_payload.full           = (w_valid_load_index[p_idx] > w_l1d_lrq_valid_load_cnt);
assign lrq_stq_if.resp_payload.evict_conflict = w_resp_evict_conflict[p_idx];
assign lrq_stq_if.resp_payload.conflict       = w_resp_conflict[p_idx];
assign lrq_stq_if.resp_payload.lrq_index_oh   = |w_l1d_lrq_loads_no_conflicts[p_idx] ? w_load_picked_valid[w_l1d_lrq_picked_index_enc[p_idx]] : // Success Load
                                                |w_hit_stq_lrq_same_pa        ? w_hit_stq_lrq_same_pa                   :                               // 1. hazard
                                                |w_hit_stq_port_same_pa       ? w_hit_stq_port_same_pa_load_valid       :                               // 2. hazard
                                                |w_hit_stq_lrq_same_evict_pa  ? w_hit_stq_lrq_same_evict_pa             :                               // 3. hazard
                                                |w_hit_stq_port_same_evict_pa ? w_hit_stq_port_same_evict_pa_load_valid :                               // 4. hazard
                                                'h0;

// ===================================
// LRQ Load Pickup
// ===================================
generate for (genvar p_idx = 0; p_idx < REQ_PORT_NUM; p_idx++) begin : lsu_req_loop

  always_comb begin
    w_l1d_lrq_loads[p_idx] = l1d_lrq[p_idx].load;
    w_l1d_req_payloads[p_idx] = l1d_lrq[p_idx].req_payload;
    w_l1d_lrq_loads_no_conflicts[p_idx] = w_l1d_lrq_loads[p_idx] &
                                          !w_resp_conflict[p_idx] &
                                          !w_resp_evict_conflict[p_idx];
  end

  bit_pick_1_index
    #(.NUM(p_idx),
      .SEL_WIDTH (REQ_PORT_NUM),
      .DATA_WIDTH($size(msrh_lsu_pkg::lrq_req_t))
      )
  u_l1d_req_pick
    (
     .i_valids    (w_l1d_lrq_loads_no_conflicts),
     .i_data      (w_l1d_req_payloads),

     .o_valid     (w_l1d_lrq_picked_valids  [p_idx]),
     .o_data      (w_l1d_picked_req_payloads[p_idx]),
     .o_picked_pos(w_l1d_lrq_picked_index_oh[p_idx])
     );

  encoder #(.SIZE(REQ_PORT_NUM)) encode_picked_index (.i_in(w_l1d_lrq_picked_index_oh[p_idx]), .o_out(w_l1d_lrq_picked_index_enc[p_idx]));
end
endgenerate

// ----------------------
// Entries
// ----------------------

generate for (genvar e_idx = 0; e_idx < msrh_pkg::LRQ_ENTRY_SIZE; e_idx++) begin : entry_loop

  if (e_idx < msrh_pkg::LRQ_NORM_ENTRY_SIZE) begin : normal_entry
    // ----------------------------
    // Load Miss Request
    // ----------------------------

    for (genvar p_idx = 0; p_idx < REQ_PORT_NUM; p_idx++) begin : lrq_port_loop
      logic [msrh_pkg::LRQ_NORM_ENTRY_SIZE-1: 0]  w_entry_ptr_oh;
      bit_rotate_left #(.WIDTH(msrh_pkg::LRQ_NORM_ENTRY_SIZE), .VAL(p_idx)) target_bit_rotate (.i_in(w_norm_in_ptr_oh), .o_out(w_entry_ptr_oh));
      assign w_load_picked_valid[p_idx][e_idx] = w_l1d_lrq_picked_valids[p_idx] & w_entry_ptr_oh[e_idx] & (p_idx < w_l1d_lrq_valid_load_cnt);
    end

    logic [REQ_PORT_NUM-1: 0] w_sel_load_valid;
    bit_matrix_pcik_column #(.WIDTH(msrh_pkg::LRQ_NORM_ENTRY_SIZE), .WORDS(REQ_PORT_NUM), .H_IDX(e_idx)) pick_load_valid (.in(w_load_picked_valid), .out(w_sel_load_valid));

    assign w_load_entry_valid[e_idx] = |w_sel_load_valid;

    msrh_lrq_entry
      u_entry
        (
         .i_clk     (i_clk    ),
         .i_reset_n (i_reset_n),

         .i_load       (w_load_entry_valid[e_idx]),
         .i_load_entry (load_entry),

         .i_ext_load_fin (lrq_search_if.valid & (lrq_search_if.index == e_idx)),

         .i_sent       (w_ext_req_sent),
         .i_evict_sent (w_evict_sent),
         .o_entry (w_lrq_entries[e_idx]),
         .o_evict_ready (w_lrq_entry_evict_ready[e_idx]),
         .o_entry_finish (w_entry_finish[e_idx])
         );

  end else begin : store_entry // if (b_idx < msrh_pkg::LRQ_NORM_ENTRY_SIZE)
    // ----------------------------
    // STQ Load Request
    // ----------------------------

    assign w_st_lrq_valids[b_idx] = w_lrq_entries[b_idx].valid;

    msrh_lrq_entry
      u_entry
        (
         .i_clk     (i_clk    ),
         .i_reset_n (i_reset_n),

         .i_load       (w_stq_miss_lrq_load & (w_stq_miss_lrq_idx == b_idx)),
         .i_load_entry (w_stq_load_entry),

         .i_ext_load_fin (lrq_search_if.valid & (lrq_search_if.index == b_idx)),

         .i_sent       (l1d_ext_rd_req.valid & l1d_ext_rd_req.ready & w_lrq_ready_to_send_oh[b_idx]),
         .i_evict_sent (l1d_evict_if.valid   & l1d_evict_if.ready   & w_lrq_ready_to_evict_oh[b_idx]),
         .o_entry (w_lrq_entries[b_idx]),
         .o_evict_ready (w_lrq_entry_evict_ready[b_idx]),
         .o_entry_finish ()
         );

  end // block: store_entry

end // block: entry_loop
endgenerate





initial begin
  assert (msrh_lsu_pkg::L2_CMD_TAG_W >= $clog2(msrh_pkg::LRQ_ENTRY_SIZE) + 1);
end

`ifdef SIMULATION
function void dump_entry_json(int fp, msrh_lsu_pkg::lrq_entry_t entry, int index);

  if (entry.valid) begin
    $fwrite(fp, "    \"lrq_entry[%02d]\" : {", index[$clog2(msrh_pkg::LRQ_ENTRY_SIZE)-1:0]);
    $fwrite(fp, "valid:%d, ", entry.valid);
    $fwrite(fp, "paddr:\"0x%0x\", ", entry.paddr);
    $fwrite(fp, "sent:\"%01d\", ", entry.sent);
    $fwrite(fp, "evict_valid:\"%01d\", ", entry.evict_valid);
    $fwrite(fp, "evict_sent:\"%01d\", ", entry.evict_sent);
    if (entry.evict_valid) begin
      $fwrite(fp, "evict_way :\"0x%d\", ", entry.evict.way);
      $fwrite(fp, "evict_paddr :\"0x%08x\"", entry.evict.paddr);
    end
    $fwrite(fp, " },\n");
  end // if (entry.valid)

endfunction // dump_json


function void dump_json(int fp);
  if ((|w_norm_lrq_valids) | (|w_st_lrq_valids)) begin
    $fwrite(fp, "  \"msrh_lrq\" : {\n");
    for (int c_idx = 0; c_idx < msrh_pkg::LRQ_ENTRY_SIZE; c_idx++) begin
      dump_entry_json (fp, w_lrq_entries[c_idx], c_idx);
    end
    $fwrite(fp, "  },\n");
  end
endfunction // dump_json
`endif // SIMULATION


endmodule // msrh_load_requester
