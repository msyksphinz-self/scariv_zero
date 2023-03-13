// ------------------------------------------------------------------------
// NAME : SCARIV Load Requseter (LRQ) for L1D
// TYPE : module
// ------------------------------------------------------------------------
// L1D Load Requestor and Replace Data
// ------------------------------------------------------------------------
//
// ------------------------------------------------------------------------

module scariv_l1d_mshr
  (
   input logic  i_clk,
   input logic  i_reset_n,

   // from Pipeline for Load + STQ Load
   l1d_missu_if.slave l1d_missu[scariv_conf_pkg::LSU_INST_NUM + 1],
   // from LS-Pipe hazard check
   missu_fwd_if.slave missu_fwd_if[scariv_conf_pkg::LSU_INST_NUM],

   // Information of MISSU
   output scariv_lsu_pkg::missu_resolve_t o_missu_resolve,
   output logic                         o_missu_is_full,
   output logic                         o_missu_is_empty,

   // L2 External Interface
   l2_req_if.master  l1d_ext_rd_req,
   l2_resp_if.slave  l1d_ext_rd_resp,

   l1d_wr_if.master  l1d_wr_if,

   // Interface to L1D eviction to Store Requestor
   l1d_evict_if.master l1d_evict_if,

   // Search MISSU entry
   missu_pa_search_if.slave   missu_pa_search_if,

   // MISSU search interface (from DCache)
   missu_dc_search_if.slave missu_dc_search_if
   );

localparam NORMAL_REQ_PORT_NUM = scariv_conf_pkg::LSU_INST_NUM;
localparam REQ_PORT_NUM        = scariv_conf_pkg::LSU_INST_NUM + 1;

logic [scariv_conf_pkg::MISSU_ENTRY_SIZE-1:0] w_in_ptr_oh;
logic [scariv_conf_pkg::MISSU_ENTRY_SIZE-1:0] w_out_ptr_oh;
logic [$clog2(scariv_conf_pkg::MISSU_ENTRY_SIZE)-1:0] w_out_ptr;
logic                                             w_in_valid;
logic                                             w_out_valid;
logic [scariv_conf_pkg::MISSU_ENTRY_SIZE-1: 0]             w_entry_finish;
logic [scariv_conf_pkg::MISSU_ENTRY_SIZE-1: 0]             w_missu_valids;

logic [REQ_PORT_NUM-1: 0]   w_resp_conflict;
logic [REQ_PORT_NUM-1: 0]   w_resp_evict_conflict;

logic [REQ_PORT_NUM-1: 0]   w_l1d_missu_loads;
logic [scariv_conf_pkg::MISSU_ENTRY_SIZE-1: 0] w_load_picked_valid [REQ_PORT_NUM] ;
logic [$clog2(REQ_PORT_NUM)-1: 0]     w_l1d_missu_picked_index[REQ_PORT_NUM];
logic [REQ_PORT_NUM-1: 0]             w_l1d_missu_picked_valids;
logic [REQ_PORT_NUM-1: 0]             w_l1d_missu_picked_index_oh[REQ_PORT_NUM];
scariv_lsu_pkg::missu_req_t               w_l1d_req_payloads        [REQ_PORT_NUM];
scariv_lsu_pkg::missu_req_t               w_l1d_picked_req_payloads [REQ_PORT_NUM];
logic [REQ_PORT_NUM-1: 0]             w_l1d_missu_loads_no_conflicts;

logic [scariv_conf_pkg::MISSU_ENTRY_SIZE-1: 0] w_load_entry_valid;
scariv_lsu_pkg::mshr_entry_t w_missu_entries[scariv_conf_pkg::MISSU_ENTRY_SIZE];

logic [$clog2(REQ_PORT_NUM): 0] w_l1d_missu_valid_load_cnt;
logic [$clog2(REQ_PORT_NUM): 0] w_l1d_missu_loads_cnt;
logic [$clog2(scariv_conf_pkg::MISSU_ENTRY_SIZE):0] r_missu_remained_size;

logic [scariv_conf_pkg::LSU_INST_NUM-1: 0]     w_uc_fwd_hit [scariv_conf_pkg::MISSU_ENTRY_SIZE] ;

//
// MISSU Request selection
//
scariv_lsu_pkg::mshr_entry_t             w_missu_ready_to_send_entry;
logic [scariv_conf_pkg::MISSU_ENTRY_SIZE-1: 0] w_missu_ready_to_send;
logic [scariv_conf_pkg::MISSU_ENTRY_SIZE-1: 0] w_missu_ready_to_send_oh;
logic [$clog2(scariv_conf_pkg::MISSU_ENTRY_SIZE)-1: 0] w_missu_send_tag;

logic                                         w_ext_rd_resp_valid;
logic [$clog2(scariv_conf_pkg::MISSU_ENTRY_SIZE)-1: 0] w_ext_rd_resp_tag;

//
// Write L1D
//
logic [scariv_conf_pkg::MISSU_ENTRY_SIZE-1: 0]         w_wr_req_valid;
logic [scariv_conf_pkg::MISSU_ENTRY_SIZE-1: 0]         w_wr_req_valid_oh;
scariv_lsu_pkg::mshr_entry_t                    w_wr_missu_entry_sel;

//
// Evict Information
//
scariv_lsu_pkg::mshr_entry_t             w_missu_ready_to_evict_entry;
logic [scariv_conf_pkg::MISSU_ENTRY_SIZE-1: 0] w_missu_entry_evict_ready;
logic [scariv_conf_pkg::MISSU_ENTRY_SIZE-1: 0] w_missu_ready_to_evict;
logic [scariv_conf_pkg::MISSU_ENTRY_SIZE-1: 0] w_missu_ready_to_evict_oh;
logic [$clog2(scariv_conf_pkg::MISSU_ENTRY_SIZE)-1: 0] w_missu_evict_tag;


bit_cnt #(.WIDTH(REQ_PORT_NUM)) u_missu_req_cnt(.in(w_l1d_missu_loads_no_conflicts), .out(w_l1d_missu_loads_cnt));
/* verilator lint_off WIDTH */
assign w_l1d_missu_valid_load_cnt = r_missu_remained_size > w_l1d_missu_loads_cnt ? w_l1d_missu_loads_cnt : r_missu_remained_size;


always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_missu_remained_size <= scariv_conf_pkg::MISSU_ENTRY_SIZE;
  end else begin
    r_missu_remained_size <= r_missu_remained_size -
                           (w_in_valid ? w_l1d_missu_valid_load_cnt : 'h0) +
                           (w_out_valid ? 'h1 : 'h0);
  end
end

`ifdef SIMULATION
always_ff @ (negedge i_clk, negedge i_reset_n) begin
  if (i_reset_n) begin
    if (r_missu_remained_size > scariv_conf_pkg::MISSU_ENTRY_SIZE) begin
      $fatal (0, "MISSU remained size must not exceed default value %d\n",
            scariv_conf_pkg::MISSU_ENTRY_SIZE);
    end
    if (r_missu_remained_size != scariv_conf_pkg::MISSU_ENTRY_SIZE - $countones(w_missu_valids)) begin
      $fatal (0, "MISSU counter size and emptied MISSU entry size is different %d != %d\n",
              r_missu_remained_size, scariv_conf_pkg::MISSU_ENTRY_SIZE - $countones(w_missu_valids));
    end
  end
end

final begin
  if (r_missu_remained_size != scariv_conf_pkg::MISSU_ENTRY_SIZE) begin
    $fatal (0, "MISSU remained size must return to default value %d, but currently %d\n",
            scariv_conf_pkg::MISSU_ENTRY_SIZE, r_missu_remained_size);
  end
end
`endif // SIMULATION

//
// MISSU Pointer
//
assign w_in_valid  = |w_l1d_missu_loads_no_conflicts;
assign w_out_valid = |w_entry_finish;

inoutptr_var_oh #(.SIZE(scariv_conf_pkg::MISSU_ENTRY_SIZE)) u_req_ptr(.i_clk (i_clk), .i_reset_n(i_reset_n),
                                                                  .i_rollback(1'b0),
                                                                  .i_in_valid (w_in_valid ),
                                                                  /* verilator lint_off WIDTH */
                                                                  .i_in_val({{($clog2(scariv_conf_pkg::MISSU_ENTRY_SIZE)-$clog2(scariv_conf_pkg::LSU_INST_NUM)){1'b0}}, w_l1d_missu_valid_load_cnt}),
                                                                  .o_in_ptr_oh (w_in_ptr_oh ),

                                                                  .i_out_valid(w_out_valid),
                                                                  .i_out_val({{($clog2(scariv_conf_pkg::MISSU_ENTRY_SIZE)){1'b0}}, 1'b1}),
                                                                  .o_out_ptr_oh(w_out_ptr_oh));

encoder #(.SIZE(scariv_conf_pkg::MISSU_ENTRY_SIZE)) u_bit_out_ptr_encoder (.i_in(w_out_ptr_oh), .o_out(w_out_ptr));


// -------------------------------------
// Conflict Check of Normal MISSU Entries
// -------------------------------------
function automatic logic hit_missu_same_pa (logic valid, scariv_pkg::paddr_t req_paddr,
                                          scariv_lsu_pkg::mshr_entry_t missu_entry,
                                          logic [$clog2(scariv_conf_pkg::MISSU_ENTRY_SIZE)-1: 0] entry_idx);

  return valid & missu_entry.valid & ~w_entry_finish[entry_idx] &
    (missu_entry.paddr[riscv_pkg::PADDR_W-1:$clog2(scariv_lsu_pkg::DCACHE_DATA_B_W)] ==
     req_paddr[riscv_pkg::PADDR_W-1:$clog2(scariv_lsu_pkg::DCACHE_DATA_B_W)]);

endfunction // hit_missu_same_pa

function automatic logic hit_missu_same_evict_pa (logic valid, scariv_pkg::paddr_t req_evict_paddr,
                                                scariv_lsu_pkg::mshr_entry_t missu_entry,
                                                logic [$clog2(scariv_conf_pkg::MISSU_ENTRY_SIZE)-1: 0] entry_idx);
  return 1'b0;

endfunction // hit_missu_same_pa


function automatic logic hit_port_pa (logic p0_valid, logic p1_valid,
                                      scariv_pkg::paddr_t p0_pa,
                                      scariv_pkg::paddr_t p1_pa);
  return p0_valid & p1_valid &
    (p0_pa[riscv_pkg::PADDR_W-1:$clog2(scariv_lsu_pkg::DCACHE_DATA_B_W)] ==
     p1_pa[riscv_pkg::PADDR_W-1:$clog2(scariv_lsu_pkg::DCACHE_DATA_B_W)]);

endfunction // hit_port_pa

/* verilator lint_off UNOPTFLAT */
logic [$clog2(REQ_PORT_NUM): 0] w_valid_load_index[REQ_PORT_NUM];
logic [scariv_conf_pkg::MISSU_ENTRY_SIZE-1: 0] w_missu_index_oh[REQ_PORT_NUM];

generate for (genvar p_idx = 0; p_idx < REQ_PORT_NUM; p_idx++) begin : port_loop
  if (p_idx == 0) begin
    assign w_valid_load_index[p_idx] = w_l1d_missu_loads_no_conflicts[p_idx] ? 1 : 0;
  end else begin
    assign w_valid_load_index[p_idx] = w_l1d_missu_loads_no_conflicts[p_idx] ? w_valid_load_index[p_idx-1] + 'h1 :
                                       w_valid_load_index[p_idx-1];
  end

  // 1. check the address with exist missu
  logic [scariv_conf_pkg::MISSU_ENTRY_SIZE-1: 0] w_hit_missu_same_pa;
  for (genvar e_idx = 0; e_idx < scariv_conf_pkg::MISSU_ENTRY_SIZE; e_idx++) begin : entry_loop
    assign w_hit_missu_same_pa[e_idx] = hit_missu_same_pa (l1d_missu[p_idx].load, l1d_missu[p_idx].req_payload.paddr,
                                                       w_missu_entries[e_idx], e_idx);
  end

  // 2. check the address with different pipeline
  logic [REQ_PORT_NUM-1: 0]             w_hit_port_same_pa;
  for (genvar p2_idx = 0; p2_idx < REQ_PORT_NUM; p2_idx++) begin : adj_port_loop
    if (p_idx <= p2_idx) begin
      assign w_hit_port_same_pa[p2_idx] = 1'b0;
    end else begin
      assign w_hit_port_same_pa[p2_idx] = hit_port_pa (l1d_missu[p_idx].load, l1d_missu[p2_idx].load,
                                                       l1d_missu[p_idx ].req_payload.paddr,
                                                       l1d_missu[p2_idx].req_payload.paddr);
    end
  end

  logic [REQ_PORT_NUM-1: 0] w_hit_port_same_pa_lsb;
  logic [scariv_conf_pkg::MISSU_ENTRY_SIZE-1: 0] hit_port_same_pa_entry_idx_oh;
  bit_extract_lsb #(.WIDTH(REQ_PORT_NUM)) u_same_port_lsb (.in(w_hit_port_same_pa), .out(w_hit_port_same_pa_lsb));
  bit_oh_or #(.T(logic[scariv_conf_pkg::MISSU_ENTRY_SIZE-1:0]), .WORDS(REQ_PORT_NUM)) select_port_pa_entry  (.i_oh(w_hit_port_same_pa_lsb), .i_data(w_missu_index_oh), .o_selected(hit_port_same_pa_entry_idx_oh));

  // 3. check the evicted address with existed evict MISSU
  logic [scariv_conf_pkg::MISSU_ENTRY_SIZE-1: 0]   w_hit_missu_same_evict_pa;
  assign w_hit_missu_same_evict_pa = 'h0;

  // 4. check the evicted address with different pipeline
  logic [REQ_PORT_NUM-1: 0]             w_hit_port_same_evict_pa;
  assign w_hit_port_same_evict_pa = 'h0;

  logic [REQ_PORT_NUM-1: 0] w_hit_port_same_evict_pa_lsb;
  logic [scariv_conf_pkg::MISSU_ENTRY_SIZE-1: 0] w_hit_port_same_evict_pa_idx_oh;
  bit_extract_lsb #(.WIDTH(REQ_PORT_NUM)) u_same_port_evict_lsb (.in(w_hit_port_same_evict_pa), .out(w_hit_port_same_evict_pa_lsb));
  bit_oh_or #(.T(logic[scariv_conf_pkg::MISSU_ENTRY_SIZE-1:0]), .WORDS(REQ_PORT_NUM)) select_port_evict_pa_entry  (.i_oh(w_hit_port_same_evict_pa_lsb), .i_data(w_missu_index_oh), .o_selected(w_hit_port_same_evict_pa_idx_oh));

  assign w_resp_conflict[p_idx] = (|w_hit_missu_same_pa) |  // 1. hazard
                                  (|w_hit_port_same_pa);   // 2. hazard

  assign w_resp_evict_conflict[p_idx] = (|w_hit_missu_same_evict_pa) |  // 3. hazard
                                        (|w_hit_port_same_evict_pa);   // 4. hazard

  assign w_missu_index_oh[p_idx] = |w_l1d_missu_loads_no_conflicts[p_idx] ? w_load_picked_valid[w_l1d_missu_picked_index[p_idx]] : // Success Load
                                 |w_hit_missu_same_pa        ? w_hit_missu_same_pa                   :                               // 1. hazard
                                 |w_hit_port_same_pa       ? hit_port_same_pa_entry_idx_oh       :                               // 2. hazard
                                 |w_hit_missu_same_evict_pa  ? w_hit_missu_same_evict_pa             :                               // 3. hazard
                                 |w_hit_port_same_evict_pa ? w_hit_port_same_evict_pa_idx_oh     :                               // 4. hazard
                                 'h0;

  assign l1d_missu[p_idx].resp_payload.full           = (w_valid_load_index[p_idx] > w_l1d_missu_valid_load_cnt);
  assign l1d_missu[p_idx].resp_payload.evict_conflict = w_resp_evict_conflict[p_idx];
  assign l1d_missu[p_idx].resp_payload.conflict       = w_resp_conflict[p_idx];
  assign l1d_missu[p_idx].resp_payload.missu_index_oh   = w_missu_index_oh[p_idx];

end // block: port_loop
endgenerate

// ===================================
// MISSU Load Pickup
// ===================================
generate for (genvar p_idx = 0; p_idx < REQ_PORT_NUM; p_idx++) begin : lsu_req_loop

  always_comb begin
    w_l1d_missu_loads[p_idx] = l1d_missu[p_idx].load;
    w_l1d_req_payloads[p_idx] = l1d_missu[p_idx].req_payload;
    w_l1d_missu_loads_no_conflicts[p_idx] = w_l1d_missu_loads[p_idx] &
                                          !w_resp_conflict[p_idx] &
                                          !w_resp_evict_conflict[p_idx];
  end

  bit_pick_1_index
    #(.NUM(p_idx),
      .SEL_WIDTH (REQ_PORT_NUM),
      .DATA_WIDTH($size(scariv_lsu_pkg::missu_req_t))
      )
  u_l1d_req_pick
    (
     .i_valids    (w_l1d_missu_loads_no_conflicts),
     .i_data      (w_l1d_req_payloads),

     .o_valid     (w_l1d_missu_picked_valids  [p_idx]),
     .o_data      (w_l1d_picked_req_payloads  [p_idx]),
     .o_picked_pos(w_l1d_missu_picked_index_oh[p_idx])
     );

  logic [REQ_PORT_NUM-1: 0] selected_index_oh;
  bit_matrix_pick_column #(.WIDTH(REQ_PORT_NUM), .WORDS(REQ_PORT_NUM), .H_IDX(p_idx)) pick_selected_index
    (.in(w_l1d_missu_picked_index_oh), .out(selected_index_oh));
  encoder #(.SIZE(REQ_PORT_NUM)) encode_picked_index (.i_in(selected_index_oh), .o_out(w_l1d_missu_picked_index[p_idx]));

end
endgenerate



// ----------------------
// Entries
// ----------------------

generate for (genvar e_idx = 0; e_idx < scariv_conf_pkg::MISSU_ENTRY_SIZE; e_idx++) begin : entry_loop

  // ----------------------------
  // Load Miss Request
  // ----------------------------
  for (genvar p_idx = 0; p_idx < REQ_PORT_NUM; p_idx++) begin : missu_port_loop
    logic [scariv_conf_pkg::MISSU_ENTRY_SIZE-1: 0]  w_entry_ptr_oh;
    bit_rotate_left #(.WIDTH(scariv_conf_pkg::MISSU_ENTRY_SIZE), .VAL(p_idx)) target_bit_rotate (.i_in(w_in_ptr_oh), .o_out(w_entry_ptr_oh));
    assign w_load_picked_valid[p_idx][e_idx] = w_l1d_missu_picked_valids[p_idx] & w_entry_ptr_oh[e_idx] & (p_idx < w_l1d_missu_valid_load_cnt);
  end

  logic                                    w_ext_req_sent;
  logic                                    w_evict_sent;
  logic [REQ_PORT_NUM-1: 0]                w_sel_load_valid;
  bit_matrix_pick_column #(.WIDTH(scariv_conf_pkg::MISSU_ENTRY_SIZE), .WORDS(REQ_PORT_NUM), .H_IDX(e_idx)) pick_load_valid (.in(w_load_picked_valid), .out(w_sel_load_valid));

  assign w_load_entry_valid[e_idx] = |w_sel_load_valid;

  scariv_lsu_pkg::missu_req_t w_l1d_picked_req_payloads_oh;
  bit_oh_or #(.T(scariv_lsu_pkg::missu_req_t), .WORDS(REQ_PORT_NUM)) pick_entry (.i_oh(w_sel_load_valid), .i_data(w_l1d_picked_req_payloads), .o_selected(w_l1d_picked_req_payloads_oh));

  scariv_lsu_pkg::mshr_entry_t w_load_entry;
  assign w_load_entry = scariv_lsu_pkg::assign_mshr_entry(w_load_entry_valid[e_idx],
                                                          w_l1d_picked_req_payloads_oh);

  assign w_evict_sent   = l1d_evict_if.valid   & l1d_evict_if.ready   & w_missu_ready_to_evict_oh[e_idx];
  assign w_ext_req_sent = l1d_ext_rd_req.valid & l1d_ext_rd_req.ready & w_missu_ready_to_send_oh [e_idx];

  scariv_l1d_mshr_entry
    u_entry
      (
       .i_clk     (i_clk    ),
       .i_reset_n (i_reset_n),

       .i_load       (w_load_entry_valid[e_idx]),
       .i_load_entry (w_load_entry),

       .i_ext_load_fin (w_ext_rd_resp_valid & (w_ext_rd_resp_tag == e_idx)),
       .l2_resp        (l1d_ext_rd_resp.payload),

       .i_sent         (w_ext_req_sent),
       .i_evict_sent   (w_evict_sent),

       .o_wr_req_valid         (w_wr_req_valid   [e_idx]),
       .i_wr_accepted          (w_wr_req_valid_oh[e_idx]),
       .i_wr_conflicted        (1'b0),
       .s2_l1d_wr_resp_payload (l1d_wr_if.s2_wr_resp),

       .i_uc_fwd_hit (|w_uc_fwd_hit[e_idx]),

       .o_entry        (w_missu_entries[e_idx]),
       .o_evict_ready  (w_missu_entry_evict_ready[e_idx]),

       .i_out_ptr_valid (w_out_ptr_oh[e_idx]),
       .o_entry_finish (w_entry_finish[e_idx])
       );

  assign w_missu_valids[e_idx] = w_missu_entries[e_idx].valid;

end // block: entry_loop
endgenerate

localparam TAG_FILLER_W = scariv_lsu_pkg::L2_CMD_TAG_W - 2 - $clog2(scariv_conf_pkg::MISSU_ENTRY_SIZE);

// selection of external memory request
generate for (genvar e_idx = 0; e_idx < scariv_conf_pkg::MISSU_ENTRY_SIZE; e_idx++) begin : missu_sel_loop
  assign w_missu_ready_to_send[e_idx] = w_missu_entries[e_idx].valid & !w_missu_entries[e_idx].sent;

  assign w_missu_ready_to_evict[e_idx] = w_missu_entries[e_idx].valid &
                                         w_missu_entry_evict_ready[e_idx];
end
endgenerate
bit_extract_lsb_ptr #(.WIDTH(scariv_conf_pkg::MISSU_ENTRY_SIZE)) u_bit_send_sel (.in(w_missu_ready_to_send), .i_ptr(w_out_ptr), .out(w_missu_ready_to_send_oh));
encoder#(.SIZE(scariv_conf_pkg::MISSU_ENTRY_SIZE)) u_bit_send_tag_encoder (.i_in(w_missu_ready_to_send_oh), .o_out(w_missu_send_tag));
bit_oh_or #(.T(scariv_lsu_pkg::mshr_entry_t), .WORDS(scariv_conf_pkg::MISSU_ENTRY_SIZE)) select_send_entry  (.i_oh(w_missu_ready_to_send_oh), .i_data(w_missu_entries), .o_selected(w_missu_ready_to_send_entry));

bit_extract_lsb_ptr #(.WIDTH(scariv_conf_pkg::MISSU_ENTRY_SIZE)) u_bit_evict_sel (.in(w_missu_ready_to_evict), .i_ptr(w_out_ptr), .out(w_missu_ready_to_evict_oh));
encoder#(.SIZE(scariv_conf_pkg::MISSU_ENTRY_SIZE)) u_bit_evict_tag_encoder (.i_in(w_missu_ready_to_evict_oh), .o_out(w_missu_evict_tag));
bit_oh_or #(.T(scariv_lsu_pkg::mshr_entry_t), .WORDS(scariv_conf_pkg::MISSU_ENTRY_SIZE)) select_evict_entry  (.i_oh(w_missu_ready_to_evict_oh), .i_data(w_missu_entries), .o_selected(w_missu_ready_to_evict_entry));


assign l1d_ext_rd_req.valid           = |w_missu_ready_to_send;
assign l1d_ext_rd_req.payload.cmd     = scariv_lsu_pkg::M_XRD;
assign l1d_ext_rd_req.payload.addr    = w_missu_ready_to_send_entry.paddr;
assign l1d_ext_rd_req.tag             = {scariv_lsu_pkg::L2_UPPER_TAG_RD_L1D, {TAG_FILLER_W{1'b0}}, w_missu_send_tag};
assign l1d_ext_rd_req.payload.data    = 'h0;
assign l1d_ext_rd_req.payload.byte_en = 'h0;

assign w_ext_rd_resp_valid = l1d_ext_rd_resp.valid &
                             (l1d_ext_rd_resp.tag        [scariv_lsu_pkg::L2_CMD_TAG_W-1 -: 2] == scariv_lsu_pkg::L2_UPPER_TAG_RD_L1D);
assign w_ext_rd_resp_tag = l1d_ext_rd_resp.tag[$clog2(scariv_conf_pkg::MISSU_ENTRY_SIZE)-1: 0];

assign l1d_ext_rd_resp.ready = 1'b1;

// ------------------------
// L1D Write Request
// ------------------------

assign l1d_wr_if.s0_valid = |w_wr_req_valid;
bit_extract_lsb_ptr #(.WIDTH(scariv_conf_pkg::MISSU_ENTRY_SIZE)) u_bit_wr_req_select (.in(w_wr_req_valid), .i_ptr(w_out_ptr), .out(w_wr_req_valid_oh));
bit_oh_or #(.T(scariv_lsu_pkg::mshr_entry_t), .WORDS(scariv_conf_pkg::MISSU_ENTRY_SIZE))
select_l1d_wr_req_entry (.i_oh(w_wr_req_valid_oh), .i_data(w_missu_entries), .o_selected(w_wr_missu_entry_sel));

assign l1d_wr_if.s0_wr_req.s0_paddr = w_wr_missu_entry_sel.paddr;
assign l1d_wr_if.s0_wr_req.s0_data  = w_wr_missu_entry_sel.data;
assign l1d_wr_if.s0_wr_req.s0_be    = {scariv_lsu_pkg::DCACHE_DATA_B_W{1'b1}};
assign l1d_wr_if.s0_wr_req.s0_way   = w_wr_missu_entry_sel.way;
assign l1d_wr_if.s0_wr_req.s0_mesi  = scariv_lsu_pkg::MESI_EXCLUSIVE;

// -----------------
// Eviction Request
// -----------------
assign l1d_evict_if.valid = |w_missu_ready_to_evict;
assign l1d_evict_if.payload.paddr = w_missu_ready_to_evict_entry.paddr;
assign l1d_evict_if.payload.data  = w_missu_ready_to_evict_entry.data;

// Searching MISSU Interface from DCache
assign missu_dc_search_if.missu_entry = w_missu_entries[missu_dc_search_if.index];

// Notification to MISSU resolve to LDQ
// Note: Now searching from MISSU means L1D will be written and resolve confliction
assign o_missu_resolve.valid            = w_ext_rd_resp_valid;
assign o_missu_resolve.resolve_index_oh = 1 << w_ext_rd_resp_tag;
assign o_missu_resolve.missu_entry_valids = w_missu_valids;
assign o_missu_is_full  = &w_missu_valids;
assign o_missu_is_empty = ~|w_missu_valids;

// ---------------------
// MISSU Search Registers
// ---------------------
logic                                         r_missu_search_valid;
logic [scariv_conf_pkg::MISSU_ENTRY_SIZE-1: 0]         r_missu_search_index_oh;

always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_missu_search_valid <= 1'b0;
    r_missu_search_index_oh <= 'h0;
  end else begin
    r_missu_search_valid    <= missu_dc_search_if.valid;
    r_missu_search_index_oh <= 1 << missu_dc_search_if.index;
  end
end

// Eviction Hazard Check
generate for (genvar p_idx = 0; p_idx < scariv_conf_pkg::LSU_INST_NUM; p_idx++) begin : lsu_haz_loop
  logic [scariv_conf_pkg::MISSU_ENTRY_SIZE-1: 0] w_missu_fwd_hit;
  for (genvar e_idx = 0; e_idx < scariv_conf_pkg::MISSU_ENTRY_SIZE; e_idx++) begin : buffer_loop
    assign w_missu_fwd_hit[e_idx] = w_missu_entries[e_idx].valid &
                                    w_missu_entries[e_idx].get_data &
                                    missu_fwd_if[p_idx].ex2_valid &
                                    (w_missu_entries[e_idx].paddr [riscv_pkg::PADDR_W-1: $clog2(scariv_lsu_pkg::DCACHE_DATA_B_W)] ==
                                     missu_fwd_if[p_idx].ex2_paddr[riscv_pkg::PADDR_W-1: $clog2(scariv_lsu_pkg::DCACHE_DATA_B_W)]);

    assign w_uc_fwd_hit[e_idx][p_idx] = w_missu_fwd_hit[e_idx];
  end

  scariv_lsu_pkg::mshr_entry_t w_missu_fwd_entry;
  bit_oh_or #(.T(scariv_lsu_pkg::mshr_entry_t), .WORDS(scariv_conf_pkg::MISSU_ENTRY_SIZE)) select_evict_entry  (.i_oh(w_missu_fwd_hit), .i_data(w_missu_entries), .o_selected(w_missu_fwd_entry));

  assign missu_fwd_if[p_idx].ex2_fwd_valid = |w_missu_fwd_hit;
  assign missu_fwd_if[p_idx].ex2_fwd_data  = w_missu_fwd_entry.data;

end
endgenerate





// --------------------------
// MISSU search from ST-Buffer
// --------------------------
logic [scariv_conf_pkg::MISSU_ENTRY_SIZE-1: 0] w_stbuf_missu_hit_array_next;
logic [scariv_conf_pkg::MISSU_ENTRY_SIZE-1: 0] w_stbuf_missu_evict_hit_array_next;
generate for (genvar e_idx = 0; e_idx < scariv_conf_pkg::MISSU_ENTRY_SIZE; e_idx++) begin : stbuf_missu_loop
  assign w_stbuf_missu_hit_array_next[e_idx] = missu_pa_search_if.s0_valid &
                                             w_missu_entries[e_idx].valid &
                                             !w_entry_finish[e_idx] &
                                             (w_missu_entries[e_idx].paddr [riscv_pkg::PADDR_W-1: $clog2(scariv_lsu_pkg::DCACHE_DATA_B_W)] ==
                                              missu_pa_search_if.s0_paddr[riscv_pkg::PADDR_W-1: $clog2(scariv_lsu_pkg::DCACHE_DATA_B_W)]);
  always_ff @ (posedge i_clk, negedge i_reset_n) begin
    if (!i_reset_n) begin
      missu_pa_search_if.s1_hit_index_oh[e_idx] <= 1'b0;
    end else begin
      missu_pa_search_if.s1_hit_index_oh[e_idx] <= w_stbuf_missu_hit_array_next[e_idx];
    end
  end

end
endgenerate



initial begin
  assert (scariv_lsu_pkg::L2_CMD_TAG_W >= $clog2(scariv_conf_pkg::MISSU_ENTRY_SIZE) + 1);
end

`ifdef SIMULATION
function void dump_entry_json(int fp, scariv_lsu_pkg::mshr_entry_t entry, int index);

  if (entry.valid) begin
    $fwrite(fp, "    \"missu_entry[%02d]\" : {", index[$clog2(scariv_conf_pkg::MISSU_ENTRY_SIZE)-1:0]);
    $fwrite(fp, "valid:%d, ", entry.valid);
    $fwrite(fp, "paddr:\"0x%0x\", ", entry.paddr);
    $fwrite(fp, "sent:\"%01d\", ", entry.sent);
    $fwrite(fp, " },\n");
  end // if (entry.valid)

endfunction // dump_json


function void dump_json(int fp);
  if (|w_missu_valids) begin
    $fwrite(fp, "  \"scariv_missu\" : {\n");
    for (int c_idx = 0; c_idx < scariv_conf_pkg::MISSU_ENTRY_SIZE; c_idx++) begin
      dump_entry_json (fp, w_missu_entries[c_idx], c_idx);
    end
    $fwrite(fp, "  },\n");
  end
endfunction // dump_json
`endif // SIMULATION


endmodule // scariv_l1d_mshr
