// ------------------------------------------------------------------------
// NAME : MSRH Load Requseter (LRQ) for L1D
// TYPE : module
// ------------------------------------------------------------------------
// L1D Load Requestor and Replace Data
// ------------------------------------------------------------------------
//
// ------------------------------------------------------------------------

module msrh_miss_unit
  (
   input logic  i_clk,
   input logic  i_reset_n,

   // from Pipeline for Load + STQ Load
   l1d_lrq_if.slave l1d_lrq[msrh_conf_pkg::LSU_INST_NUM + 1],
   // from LS-Pipe hazard check
   lrq_haz_check_if.slave lrq_haz_check_if[msrh_conf_pkg::LSU_INST_NUM],

   // Information of LRQ
   output msrh_lsu_pkg::lrq_resolve_t o_lrq_resolve,
   output logic                       o_lrq_is_full,

   // L2 External Interface
   l2_req_if.master  l1d_ext_rd_req,
   l2_resp_if.slave  l1d_ext_rd_resp,

   l1d_wr_if.master  l1d_wr_if,

   // Interface to L1D eviction to Store Requestor
   l1d_evict_if.master l1d_evict_if,

   // Search LRQ entry
   lrq_pa_search_if.slave   lrq_pa_search_if,

   // LRQ search interface (from DCache)
   lrq_dc_search_if.slave lrq_dc_search_if
   );

localparam NORMAL_REQ_PORT_NUM = msrh_conf_pkg::LSU_INST_NUM;
localparam REQ_PORT_NUM        = msrh_conf_pkg::LSU_INST_NUM + 1;

logic [msrh_pkg::LRQ_ENTRY_SIZE-1:0] w_in_ptr_oh;
logic [msrh_pkg::LRQ_ENTRY_SIZE-1:0] w_out_ptr_oh;
logic [$clog2(msrh_pkg::LRQ_ENTRY_SIZE)-1:0] w_out_ptr;
logic                                             w_in_valid;
logic                                             w_out_valid;
logic [msrh_pkg::LRQ_ENTRY_SIZE-1: 0]             w_entry_finish;
logic [msrh_pkg::LRQ_ENTRY_SIZE-1: 0]             w_lrq_valids;

logic [REQ_PORT_NUM-1: 0]   w_resp_conflict;
logic [REQ_PORT_NUM-1: 0]   w_resp_evict_conflict;

logic [REQ_PORT_NUM-1: 0]   w_l1d_lrq_loads;
logic [msrh_pkg::LRQ_ENTRY_SIZE-1: 0] w_load_picked_valid [REQ_PORT_NUM] ;
logic [$clog2(REQ_PORT_NUM)-1: 0]     w_l1d_lrq_picked_index[REQ_PORT_NUM];
logic [REQ_PORT_NUM-1: 0]             w_l1d_lrq_picked_valids;
logic [REQ_PORT_NUM-1: 0]             w_l1d_lrq_picked_index_oh[REQ_PORT_NUM];
msrh_lsu_pkg::lrq_req_t               w_l1d_req_payloads        [REQ_PORT_NUM];
msrh_lsu_pkg::lrq_req_t               w_l1d_picked_req_payloads [REQ_PORT_NUM];
logic [REQ_PORT_NUM-1: 0]             w_l1d_lrq_loads_no_conflicts;

logic [msrh_pkg::LRQ_ENTRY_SIZE-1: 0] w_load_entry_valid;
msrh_lsu_pkg::miss_entry_t w_lrq_entries[msrh_pkg::LRQ_ENTRY_SIZE];

logic [$clog2(REQ_PORT_NUM): 0] w_l1d_lrq_valid_load_cnt;
logic [$clog2(REQ_PORT_NUM): 0] w_l1d_lrq_loads_cnt;
logic [$clog2(msrh_pkg::LRQ_ENTRY_SIZE):0] r_lrq_remained_size;

//
// LRQ Request selection
//
msrh_lsu_pkg::miss_entry_t             w_lrq_ready_to_send_entry;
logic [msrh_pkg::LRQ_ENTRY_SIZE-1: 0] w_lrq_ready_to_send;
logic [msrh_pkg::LRQ_ENTRY_SIZE-1: 0] w_lrq_ready_to_send_oh;
logic [$clog2(msrh_pkg::LRQ_ENTRY_SIZE)-1: 0] w_lrq_send_tag;


//
// Write L1D
//
logic [msrh_pkg::LRQ_ENTRY_SIZE-1: 0]         w_wr_req_valid;
logic [msrh_pkg::LRQ_ENTRY_SIZE-1: 0]         w_wr_req_valid_oh;
msrh_lsu_pkg::miss_entry_t                    w_wr_lrq_entry_sel;

//
// Evict Information
//
msrh_lsu_pkg::miss_entry_t             w_lrq_ready_to_evict_entry;
logic [msrh_pkg::LRQ_ENTRY_SIZE-1: 0] w_lrq_entry_evict_ready;
logic [msrh_pkg::LRQ_ENTRY_SIZE-1: 0] w_lrq_ready_to_evict;
logic [msrh_pkg::LRQ_ENTRY_SIZE-1: 0] w_lrq_ready_to_evict_oh;
logic [$clog2(msrh_pkg::LRQ_ENTRY_SIZE)-1: 0] w_lrq_evict_tag;


bit_cnt #(.WIDTH(REQ_PORT_NUM)) u_lrq_req_cnt(.in(w_l1d_lrq_loads_no_conflicts), .out(w_l1d_lrq_loads_cnt));
/* verilator lint_off WIDTH */
assign w_l1d_lrq_valid_load_cnt = r_lrq_remained_size > w_l1d_lrq_loads_cnt ? w_l1d_lrq_loads_cnt : r_lrq_remained_size;


always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_lrq_remained_size <= msrh_pkg::LRQ_ENTRY_SIZE;
  end else begin
    r_lrq_remained_size <= r_lrq_remained_size -
                           (w_in_valid ? w_l1d_lrq_valid_load_cnt : 'h0) +
                           (w_out_valid ? 'h1 : 'h0);
  end
end

`ifdef SIMULATION
always_ff @ (negedge i_clk, negedge i_reset_n) begin
  if (i_reset_n) begin
    if (r_lrq_remained_size > msrh_pkg::LRQ_ENTRY_SIZE) begin
      $fatal (0, "LRQ remained size must not exceed default value %d\n",
            msrh_pkg::LRQ_ENTRY_SIZE);
    end
    if (r_lrq_remained_size != msrh_pkg::LRQ_ENTRY_SIZE - $countones(w_lrq_valids)) begin
      $fatal (0, "LRQ counter size and emptied LRQ entry size is different %d != %d\n",
              r_lrq_remained_size, msrh_pkg::LRQ_ENTRY_SIZE - $countones(w_lrq_valids));
    end
  end
end

final begin
  if (r_lrq_remained_size != msrh_pkg::LRQ_ENTRY_SIZE) begin
    $fatal (0, "LRQ remained size must return to default value %d, but currently %d\n",
            msrh_pkg::LRQ_ENTRY_SIZE, r_lrq_remained_size);
  end
end
`endif // SIMULATION

//
// LRQ Pointer
//
assign w_in_valid  = |w_l1d_lrq_loads_no_conflicts;
assign w_out_valid = |w_entry_finish;

inoutptr_var_oh #(.SIZE(msrh_pkg::LRQ_ENTRY_SIZE)) u_req_ptr(.i_clk (i_clk), .i_reset_n(i_reset_n),
                                                                  .i_rollback(1'b0),
                                                                  .i_in_valid (w_in_valid ),
                                                                  /* verilator lint_off WIDTH */
                                                                  .i_in_val({{($clog2(msrh_pkg::LRQ_ENTRY_SIZE)-$clog2(msrh_conf_pkg::LSU_INST_NUM)){1'b0}}, w_l1d_lrq_valid_load_cnt}),
                                                                  .o_in_ptr_oh (w_in_ptr_oh ),

                                                                  .i_out_valid(w_out_valid),
                                                                  .i_out_val({{($clog2(msrh_pkg::LRQ_ENTRY_SIZE)){1'b0}}, 1'b1}),
                                                                  .o_out_ptr_oh(w_out_ptr_oh));

encoder #(.SIZE(msrh_pkg::LRQ_ENTRY_SIZE)) u_bit_out_ptr_encoder (.i_in(w_out_ptr_oh), .o_out(w_out_ptr));


// -------------------------------------
// Conflict Check of Normal LRQ Entries
// -------------------------------------
function automatic logic hit_lrq_same_pa (logic valid, logic [riscv_pkg::PADDR_W-1: 0] req_paddr,
                                          msrh_lsu_pkg::miss_entry_t lrq_entry,
                                          logic [$clog2(msrh_pkg::LRQ_ENTRY_SIZE)-1: 0] entry_idx);

  return valid & lrq_entry.valid & ~w_entry_finish[entry_idx] &
    (lrq_entry.paddr[riscv_pkg::PADDR_W-1:$clog2(msrh_lsu_pkg::DCACHE_DATA_B_W)] ==
     req_paddr[riscv_pkg::PADDR_W-1:$clog2(msrh_lsu_pkg::DCACHE_DATA_B_W)]);

endfunction // hit_lrq_same_pa

function automatic logic hit_lrq_same_evict_pa (logic valid, logic [riscv_pkg::PADDR_W-1: 0] req_evict_paddr,
                                                msrh_lsu_pkg::miss_entry_t lrq_entry,
                                                logic [$clog2(msrh_pkg::LRQ_ENTRY_SIZE)-1: 0] entry_idx);

  // return valid & lrq_entry.valid & lrq_entry.evict_valid & ~w_entry_finish[entry_idx] &
  //   (lrq_entry.evict.paddr[riscv_pkg::PADDR_W-1:$clog2(msrh_lsu_pkg::DCACHE_DATA_B_W)] ==
  //    req_evict_paddr[riscv_pkg::PADDR_W-1:$clog2(msrh_lsu_pkg::DCACHE_DATA_B_W)]);
  return 1'b0;

endfunction // hit_lrq_same_pa


function automatic logic hit_port_pa (logic p0_valid, logic p1_valid,
                                      logic [riscv_pkg::PADDR_W-1: 0] p0_pa,
                                      logic [riscv_pkg::PADDR_W-1: 0] p1_pa);
  return p0_valid & p1_valid &
    (p0_pa[riscv_pkg::PADDR_W-1:$clog2(msrh_lsu_pkg::DCACHE_DATA_B_W)] ==
     p1_pa[riscv_pkg::PADDR_W-1:$clog2(msrh_lsu_pkg::DCACHE_DATA_B_W)]);

endfunction // hit_port_pa

/* verilator lint_off UNOPTFLAT */
logic [$clog2(REQ_PORT_NUM): 0] w_valid_load_index[REQ_PORT_NUM];
logic [msrh_pkg::LRQ_ENTRY_SIZE-1: 0] w_lrq_index_oh[REQ_PORT_NUM];

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
      assign w_hit_port_same_pa[p2_idx] = hit_port_pa (l1d_lrq[p_idx].load, l1d_lrq[p2_idx].load,
                                                       l1d_lrq[p_idx ].req_payload.paddr,
                                                       l1d_lrq[p2_idx].req_payload.paddr);
    end
  end

  logic [REQ_PORT_NUM-1: 0] w_hit_port_same_pa_lsb;
  logic [msrh_pkg::LRQ_ENTRY_SIZE-1: 0] hit_port_same_pa_entry_idx_oh;
  bit_extract_lsb #(.WIDTH(REQ_PORT_NUM)) u_same_port_lsb (.in(w_hit_port_same_pa), .out(w_hit_port_same_pa_lsb));
  bit_oh_or #(.T(logic[msrh_pkg::LRQ_ENTRY_SIZE-1:0]), .WORDS(REQ_PORT_NUM)) select_port_pa_entry  (.i_oh(w_hit_port_same_pa_lsb), .i_data(w_lrq_index_oh), .o_selected(hit_port_same_pa_entry_idx_oh));

  // 3. check the evicted address with existed evict LRQ
  logic [msrh_pkg::LRQ_ENTRY_SIZE-1: 0]   w_hit_lrq_same_evict_pa;
  // for (genvar e_idx = 0; e_idx < msrh_pkg::LRQ_ENTRY_SIZE; e_idx++) begin : entry_evict_loop
  //   assign w_hit_lrq_same_evict_pa[e_idx] = hit_lrq_same_evict_pa (l1d_lrq[p_idx].load & l1d_lrq[p_idx].req_payload.evict_valid,
  //                                                                  l1d_lrq[p_idx].req_payload.evict_payload.paddr,
  //                                                                  w_lrq_entries[e_idx], e_idx);
  // end
  assign w_hit_lrq_same_evict_pa = 'h0;

  // 4. check the evicted address with different pipeline
  logic [REQ_PORT_NUM-1: 0]             w_hit_port_same_evict_pa;
  // for (genvar p2_idx = 0; p2_idx < REQ_PORT_NUM; p2_idx++) begin : adj_evict_port_loop
  //   if (p_idx <= p2_idx) begin
  //     assign w_hit_port_same_evict_pa[p2_idx] = 1'b0;
  //   end else begin
  //     assign w_hit_port_same_evict_pa[p2_idx] = hit_port_pa (l1d_lrq[p_idx ].load & l1d_lrq[p_idx ].req_payload.evict_valid,
  //                                                            l1d_lrq[p2_idx].load & l1d_lrq[p2_idx].req_payload.evict_valid,
  //                                                            l1d_lrq[p_idx ].req_payload.evict_payload.paddr,
  //                                                            l1d_lrq[p2_idx].req_payload.evict_payload.paddr);
  //   end
  // end
  assign w_hit_port_same_evict_pa = 'h0;

  logic [REQ_PORT_NUM-1: 0] w_hit_port_same_evict_pa_lsb;
  logic [msrh_pkg::LRQ_ENTRY_SIZE-1: 0] w_hit_port_same_evict_pa_idx_oh;
  bit_extract_lsb #(.WIDTH(REQ_PORT_NUM)) u_same_port_evict_lsb (.in(w_hit_port_same_evict_pa), .out(w_hit_port_same_evict_pa_lsb));
  bit_oh_or #(.T(logic[msrh_pkg::LRQ_ENTRY_SIZE-1:0]), .WORDS(REQ_PORT_NUM)) select_port_evict_pa_entry  (.i_oh(w_hit_port_same_evict_pa_lsb), .i_data(w_lrq_index_oh), .o_selected(w_hit_port_same_evict_pa_idx_oh));

  assign w_resp_conflict[p_idx] = (|w_hit_lrq_same_pa) |  // 1. hazard
                                  (|w_hit_port_same_pa);   // 2. hazard

  assign w_resp_evict_conflict[p_idx] = (|w_hit_lrq_same_evict_pa) |  // 3. hazard
                                        (|w_hit_port_same_evict_pa);   // 4. hazard

  assign w_lrq_index_oh[p_idx] = |w_l1d_lrq_loads_no_conflicts[p_idx] ? w_load_picked_valid[w_l1d_lrq_picked_index[p_idx]] : // Success Load
                                 |w_hit_lrq_same_pa        ? w_hit_lrq_same_pa                   :                               // 1. hazard
                                 |w_hit_port_same_pa       ? hit_port_same_pa_entry_idx_oh       :                               // 2. hazard
                                 |w_hit_lrq_same_evict_pa  ? w_hit_lrq_same_evict_pa             :                               // 3. hazard
                                 |w_hit_port_same_evict_pa ? w_hit_port_same_evict_pa_idx_oh     :                               // 4. hazard
                                 'h0;

  assign l1d_lrq[p_idx].resp_payload.full           = (w_valid_load_index[p_idx] > w_l1d_lrq_valid_load_cnt);
  assign l1d_lrq[p_idx].resp_payload.evict_conflict = w_resp_evict_conflict[p_idx];
  assign l1d_lrq[p_idx].resp_payload.conflict       = w_resp_conflict[p_idx];
  assign l1d_lrq[p_idx].resp_payload.lrq_index_oh   = w_lrq_index_oh[p_idx];

end // block: port_loop
endgenerate

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

  logic [REQ_PORT_NUM-1: 0] selected_index_oh;
  bit_matrix_pick_column #(.WIDTH(REQ_PORT_NUM), .WORDS(REQ_PORT_NUM), .H_IDX(p_idx)) pick_selected_index
    (.in(w_l1d_lrq_picked_index_oh), .out(selected_index_oh));
  encoder #(.SIZE(REQ_PORT_NUM)) encode_picked_index (.i_in(selected_index_oh), .o_out(w_l1d_lrq_picked_index[p_idx]));

end
endgenerate



// ----------------------
// Entries
// ----------------------

generate for (genvar e_idx = 0; e_idx < msrh_pkg::LRQ_ENTRY_SIZE; e_idx++) begin : entry_loop

  // ----------------------------
  // Load Miss Request
  // ----------------------------
  for (genvar p_idx = 0; p_idx < REQ_PORT_NUM; p_idx++) begin : lrq_port_loop
    logic [msrh_pkg::LRQ_ENTRY_SIZE-1: 0]  w_entry_ptr_oh;
    bit_rotate_left #(.WIDTH(msrh_pkg::LRQ_ENTRY_SIZE), .VAL(p_idx)) target_bit_rotate (.i_in(w_in_ptr_oh), .o_out(w_entry_ptr_oh));
    assign w_load_picked_valid[p_idx][e_idx] = w_l1d_lrq_picked_valids[p_idx] & w_entry_ptr_oh[e_idx] & (p_idx < w_l1d_lrq_valid_load_cnt);
  end

  logic                                    w_ext_req_sent;
  logic                                    w_evict_sent;
  logic [REQ_PORT_NUM-1: 0]                w_sel_load_valid;
  bit_matrix_pick_column #(.WIDTH(msrh_pkg::LRQ_ENTRY_SIZE), .WORDS(REQ_PORT_NUM), .H_IDX(e_idx)) pick_load_valid (.in(w_load_picked_valid), .out(w_sel_load_valid));

  assign w_load_entry_valid[e_idx] = |w_sel_load_valid;

  msrh_lsu_pkg::lrq_req_t w_l1d_picked_req_payloads_oh;
  bit_oh_or #(.T(msrh_lsu_pkg::lrq_req_t), .WORDS(REQ_PORT_NUM)) pick_entry (.i_oh(w_sel_load_valid), .i_data(w_l1d_picked_req_payloads), .o_selected(w_l1d_picked_req_payloads_oh));

  msrh_lsu_pkg::miss_entry_t w_load_entry;
  assign w_load_entry = msrh_lsu_pkg::assign_miss_entry(w_load_entry_valid[e_idx],
                                                        w_l1d_picked_req_payloads_oh);

  assign w_evict_sent   = l1d_evict_if.valid   & l1d_evict_if.ready   & w_lrq_ready_to_evict_oh[e_idx];
  assign w_ext_req_sent = l1d_ext_rd_req.valid & l1d_ext_rd_req.ready & w_lrq_ready_to_send_oh [e_idx];

  msrh_miss_entry
    u_entry
      (
       .i_clk     (i_clk    ),
       .i_reset_n (i_reset_n),

       .i_load       (w_load_entry_valid[e_idx]),
       .i_load_entry (w_load_entry),

       .i_ext_load_fin (l1d_ext_rd_resp.valid &
                        (l1d_ext_rd_resp.payload.tag[msrh_lsu_pkg::L2_CMD_TAG_W-1 -: 2] == msrh_lsu_pkg::L2_UPPER_TAG_RD_L1D) &
                        (l1d_ext_rd_resp.payload.tag[$clog2(msrh_pkg::LRQ_ENTRY_SIZE)-1: 0] == e_idx)),
       .l2_resp        (l1d_ext_rd_resp.payload),

       .i_sent         (w_ext_req_sent),
       .i_evict_sent   (w_evict_sent),

       .o_wr_req_valid         (w_wr_req_valid   [e_idx]),
       .i_wr_accepted          (w_wr_req_valid_oh[e_idx]),
       .i_wr_conflicted        (1'b0),
       .s2_l1d_wr_resp_payload (l1d_wr_if.s2_wr_resp),

       .o_entry        (w_lrq_entries[e_idx]),
       .o_evict_ready  (w_lrq_entry_evict_ready[e_idx]),
       .i_evict_accepted (w_lrq_ready_to_evict_oh[e_idx]),

       .o_entry_finish (w_entry_finish[e_idx])
       );

  assign w_lrq_valids[e_idx] = w_lrq_entries[e_idx].valid;

end // block: entry_loop
endgenerate

localparam TAG_FILLER_W = msrh_lsu_pkg::L2_CMD_TAG_W - 2 - $clog2(msrh_pkg::LRQ_ENTRY_SIZE);

// selection of external memory request
generate for (genvar e_idx = 0; e_idx < msrh_pkg::LRQ_ENTRY_SIZE; e_idx++) begin : lrq_sel_loop
  assign w_lrq_ready_to_send[e_idx] = w_lrq_entries[e_idx].valid;

  assign w_lrq_ready_to_evict[e_idx] = w_lrq_entries[e_idx].valid &
                                       w_lrq_entry_evict_ready[e_idx];
end
endgenerate
bit_extract_lsb_ptr #(.WIDTH(msrh_pkg::LRQ_ENTRY_SIZE)) u_bit_send_sel (.in(w_lrq_ready_to_send), .i_ptr(w_out_ptr), .out(w_lrq_ready_to_send_oh));
encoder#(.SIZE(msrh_pkg::LRQ_ENTRY_SIZE)) u_bit_send_tag_encoder (.i_in(w_lrq_ready_to_send_oh), .o_out(w_lrq_send_tag));
bit_oh_or #(.T(msrh_lsu_pkg::miss_entry_t), .WORDS(msrh_pkg::LRQ_ENTRY_SIZE)) select_send_entry  (.i_oh(w_lrq_ready_to_send_oh), .i_data(w_lrq_entries), .o_selected(w_lrq_ready_to_send_entry));

bit_extract_lsb_ptr #(.WIDTH(msrh_pkg::LRQ_ENTRY_SIZE)) u_bit_evict_sel (.in(w_lrq_ready_to_evict), .i_ptr(w_out_ptr), .out(w_lrq_ready_to_evict_oh));
encoder#(.SIZE(msrh_pkg::LRQ_ENTRY_SIZE)) u_bit_evict_tag_encoder (.i_in(w_lrq_ready_to_evict_oh), .o_out(w_lrq_evict_tag));
bit_oh_or #(.T(msrh_lsu_pkg::miss_entry_t), .WORDS(msrh_pkg::LRQ_ENTRY_SIZE)) select_evict_entry  (.i_oh(w_lrq_ready_to_evict_oh), .i_data(w_lrq_entries), .o_selected(w_lrq_ready_to_evict_entry));


assign l1d_ext_rd_req.valid = w_lrq_ready_to_send_entry.valid & !w_lrq_ready_to_send_entry.sent;
assign l1d_ext_rd_req.payload.cmd     = msrh_lsu_pkg::M_XRD;
assign l1d_ext_rd_req.payload.addr    = w_lrq_ready_to_send_entry.paddr;
assign l1d_ext_rd_req.payload.tag     = {msrh_lsu_pkg::L2_UPPER_TAG_RD_L1D, {TAG_FILLER_W{1'b0}}, w_lrq_send_tag};
assign l1d_ext_rd_req.payload.data    = 'h0;
assign l1d_ext_rd_req.payload.byte_en = 'h0;


// ------------------------
// L1D Write Request
// ------------------------

assign l1d_wr_if.s0_valid = |w_wr_req_valid;
bit_extract_lsb_ptr #(.WIDTH(msrh_pkg::LRQ_ENTRY_SIZE)) u_bit_wr_req_select (.in(w_wr_req_valid), .i_ptr(w_out_ptr), .out(w_wr_req_valid_oh));
bit_oh_or #(.T(msrh_lsu_pkg::miss_entry_t), .WORDS(msrh_pkg::LRQ_ENTRY_SIZE))
select_l1d_wr_req_entry (.i_oh(w_wr_req_valid_oh), .i_data(w_lrq_entries), .o_selected(w_wr_lrq_entry_sel));

assign l1d_wr_if.s0_wr_req.s0_paddr = w_wr_lrq_entry_sel.paddr;
assign l1d_wr_if.s0_wr_req.s0_data  = w_wr_lrq_entry_sel.data;
assign l1d_wr_if.s0_wr_req.s0_be    = {msrh_lsu_pkg::DCACHE_DATA_B_W{1'b1}};
assign l1d_wr_if.s0_wr_req.s0_way   = w_wr_lrq_entry_sel.way;



// -----------------
// Eviction Request
// -----------------
assign l1d_evict_if.valid = |w_lrq_ready_to_evict;
// assign l1d_evict_if.payload.cmd     = msrh_lsu_pkg::M_XWR;
// assign l1d_evict_if.payload.tag     = {msrh_lsu_pkg::L2_UPPER_TAG_RD_L1D, {TAG_FILLER_W{1'b0}}, w_lrq_evict_tag};
assign l1d_evict_if.payload.paddr = w_lrq_ready_to_evict_entry.paddr;
assign l1d_evict_if.payload.data  = w_lrq_ready_to_evict_entry.data;

// Searching LRQ Interface from DCache
assign lrq_dc_search_if.lrq_entry = w_lrq_entries[lrq_dc_search_if.index];

// Notification to LRQ resolve to LDQ
// Note: Now searching from LRQ means L1D will be written and resolve confliction
assign o_lrq_resolve.valid            = lrq_dc_search_if.valid;
assign o_lrq_resolve.resolve_index_oh = 1 << lrq_dc_search_if.index;
assign o_lrq_resolve.lrq_entry_valids = w_lrq_valids;
assign o_lrq_is_full = &w_lrq_valids;

// ---------------------
// LRQ Search Registers
// ---------------------
logic                                         r_lrq_search_valid;
logic [msrh_pkg::LRQ_ENTRY_SIZE-1: 0]         r_lrq_search_index_oh;

always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_lrq_search_valid <= 1'b0;
    r_lrq_search_index_oh <= 'h0;
  end else begin
    r_lrq_search_valid    <= lrq_dc_search_if.valid;
    r_lrq_search_index_oh <= 1 << lrq_dc_search_if.index;
  end
end

// Eviction Hazard Check
generate for (genvar p_idx = 0; p_idx < msrh_conf_pkg::LSU_INST_NUM; p_idx++) begin : lsu_haz_loop
  // logic [msrh_pkg::LRQ_ENTRY_SIZE-1: 0] w_lrq_evict_hit;
  // for (genvar e_idx = 0; e_idx < msrh_pkg::LRQ_ENTRY_SIZE; e_idx++) begin : buffer_loop
  //   assign w_lrq_evict_hit[e_idx] = w_lrq_entries[e_idx].valid &
  //                                   w_lrq_entries[e_idx].evict_valid &
  //                                   ~(o_lrq_resolve.valid & o_lrq_resolve.resolve_index_oh[e_idx]) &
  //                                   lrq_haz_check_if[p_idx].ex2_valid &
  //                                   (w_lrq_entries[e_idx].evict.paddr [riscv_pkg::PADDR_W-1: $clog2(msrh_lsu_pkg::DCACHE_DATA_B_W)] ==
  //                                    lrq_haz_check_if[p_idx].ex2_paddr[riscv_pkg::PADDR_W-1: $clog2(msrh_lsu_pkg::DCACHE_DATA_B_W)]);
  // end
  //
  // msrh_lsu_pkg::miss_entry_t w_lrq_evict_entry;
  // bit_oh_or #(.T(msrh_lsu_pkg::miss_entry_t), .WORDS(msrh_pkg::LRQ_ENTRY_SIZE)) select_evict_entry  (.i_oh(w_lrq_evict_hit), .i_data(w_lrq_entries), .o_selected(w_lrq_evict_entry));
  //
  // assign lrq_haz_check_if[p_idx].ex2_evict_haz_valid = |w_lrq_evict_hit;
  // assign lrq_haz_check_if[p_idx].ex2_evict_entry_idx = w_lrq_evict_hit;

  assign lrq_haz_check_if[p_idx].ex2_evict_haz_valid = 1'b0;
  assign lrq_haz_check_if[p_idx].ex2_evict_entry_idx = 'h0;

// `ifdef SIMULATION
//   always_ff @ (negedge i_clk, negedge i_reset_n) begin
//     if (i_reset_n) begin
//       if (!$onehot0(w_lrq_evict_hit)) begin
//         $fatal(0, "LRQ Hazard Check : lrq_evict_hit should be one-hot. Value=%x\n", w_lrq_evict_hit);
//       end
//     end
//   end
// `endif // SIMULATION

end
endgenerate


// --------------------------------
// l1d_wr_if Eviction hazard check
// --------------------------------
// logic [msrh_pkg::LRQ_ENTRY_SIZE-1: 0] l1d_wr_eviction_hazard_vlds;
// generate for (genvar e_idx = 0; e_idx < msrh_pkg::LRQ_ENTRY_SIZE; e_idx++) begin : wr_if_evicted_loop
//   assign l1d_wr_eviction_hazard_vlds[e_idx] = w_lrq_entries[e_idx].valid & l1d_wr_if.s0_valid &
//                                               w_lrq_entries[e_idx].evict_valid &
//                                               (w_lrq_entries[e_idx].evict.paddr[riscv_pkg::PADDR_W-1: $clog2(msrh_lsu_pkg::DCACHE_DATA_B_W)] ==
//                                                l1d_wr_if.s0_wr_req.s0_paddr[riscv_pkg::PADDR_W-1: $clog2(msrh_lsu_pkg::DCACHE_DATA_B_W)]) &
//                                               w_lrq_entries[e_idx].evict_sent;
// end
// endgenerate
//
// always_ff @ (posedge i_clk, negedge i_reset_n) begin
//   if (!i_reset_n) begin
//     l1d_wr_if.s1_missunit_already_evicted <= 1'b0;
//   end else begin
//     l1d_wr_if.s1_missunit_already_evicted <= |l1d_wr_eviction_hazard_vlds;
//   end
// end


// --------------------------
// LRQ search from ST-Buffer
// --------------------------
logic [msrh_pkg::LRQ_ENTRY_SIZE-1: 0] w_stbuf_lrq_hit_array_next;
logic [msrh_pkg::LRQ_ENTRY_SIZE-1: 0] w_stbuf_lrq_evict_hit_array_next;
generate for (genvar e_idx = 0; e_idx < msrh_pkg::LRQ_ENTRY_SIZE; e_idx++) begin : stbuf_lrq_loop
  assign w_stbuf_lrq_hit_array_next[e_idx] = lrq_pa_search_if.s0_valid &
                                             w_lrq_entries[e_idx].valid &
                                             !w_entry_finish[e_idx] &
                                             (w_lrq_entries[e_idx].paddr [riscv_pkg::PADDR_W-1: $clog2(msrh_lsu_pkg::DCACHE_DATA_B_W)] ==
                                              lrq_pa_search_if.s0_paddr[riscv_pkg::PADDR_W-1: $clog2(msrh_lsu_pkg::DCACHE_DATA_B_W)]);
  always_ff @ (posedge i_clk, negedge i_reset_n) begin
    if (!i_reset_n) begin
      lrq_pa_search_if.s1_hit_index_oh[e_idx] <= 1'b0;
    end else begin
      lrq_pa_search_if.s1_hit_index_oh[e_idx] <= w_stbuf_lrq_hit_array_next[e_idx];
    end
  end


  // assign w_stbuf_lrq_evict_hit_array_next[e_idx] = lrq_pa_search_if.s0_valid &
  //                                                  w_lrq_entries[e_idx].valid &
  //                                                  w_lrq_entries[e_idx].evict_valid &
  //                                                  (w_lrq_entries[e_idx].evict.paddr [riscv_pkg::PADDR_W-1: $clog2(msrh_lsu_pkg::DCACHE_DATA_B_W)] ==
  //                                                   lrq_pa_search_if.s0_paddr[riscv_pkg::PADDR_W-1: $clog2(msrh_lsu_pkg::DCACHE_DATA_B_W)]);
  // always_ff @ (posedge i_clk, negedge i_reset_n) begin
  //   if (!i_reset_n) begin
  //     lrq_pa_search_if.s1_evict_hit_index_oh[e_idx] <= 1'b0;
  //     lrq_pa_search_if.s1_evict_sent        [e_idx] <= 1'b0;
  //   end else begin
  //     lrq_pa_search_if.s1_evict_hit_index_oh[e_idx] <= w_stbuf_lrq_evict_hit_array_next[e_idx];
  //     lrq_pa_search_if.s1_evict_sent        [e_idx] <= w_lrq_entries[e_idx].evict_sent;
  //   end
  // end

end
endgenerate



initial begin
  assert (msrh_lsu_pkg::L2_CMD_TAG_W >= $clog2(msrh_pkg::LRQ_ENTRY_SIZE) + 1);
end

`ifdef SIMULATION
function void dump_entry_json(int fp, msrh_lsu_pkg::miss_entry_t entry, int index);

  if (entry.valid) begin
    $fwrite(fp, "    \"lrq_entry[%02d]\" : {", index[$clog2(msrh_pkg::LRQ_ENTRY_SIZE)-1:0]);
    $fwrite(fp, "valid:%d, ", entry.valid);
    $fwrite(fp, "paddr:\"0x%0x\", ", entry.paddr);
    $fwrite(fp, "sent:\"%01d\", ", entry.sent);
    // $fwrite(fp, "evict_valid:\"%01d\", ", entry.evict_valid);
    // $fwrite(fp, "evict_sent:\"%01d\", ", entry.evict_sent);
    // if (entry.evict_valid) begin
    //   $fwrite(fp, "evict_way :\"0x%d\", ", entry.evict.way);
    //   $fwrite(fp, "evict_paddr :\"0x%08x\"", entry.evict.paddr);
    // end
    $fwrite(fp, " },\n");
  end // if (entry.valid)

endfunction // dump_json


function void dump_json(int fp);
  if (|w_lrq_valids) begin
    $fwrite(fp, "  \"msrh_lrq\" : {\n");
    for (int c_idx = 0; c_idx < msrh_pkg::LRQ_ENTRY_SIZE; c_idx++) begin
      dump_entry_json (fp, w_lrq_entries[c_idx], c_idx);
    end
    $fwrite(fp, "  },\n");
  end
endfunction // dump_json
`endif // SIMULATION


endmodule // msrh_miss_unit
