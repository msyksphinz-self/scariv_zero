module msrh_l1d_load_requester
  (
   input logic  i_clk,
   input logic  i_reset_n,

   l1d_lrq_if.slave l1d_lrq[msrh_pkg::LSU_INST_NUM],

   output msrh_lsu_pkg::lrq_resolve_t o_lrq_resolve,

   l2_req_if.master  l1d_ext_req,
   l2_resp_if.slave  l1d_ext_resp,

   // LRQ search interface
   lrq_search_if.slave lrq_search_if
   );


logic [msrh_pkg::LRQ_ENTRY_SIZE-1: 0] w_lrq_vlds;
logic [msrh_pkg::LRQ_ENTRY_SIZE-1: 0] w_lrq_load_valid_oh;

logic [msrh_pkg::LRQ_ENTRY_SIZE-1: 0] w_hit_same_addr_vld[msrh_pkg::LSU_INST_NUM];
logic [msrh_pkg::LSU_INST_NUM-1: 0]   w_hit_port_same_addr_vld[msrh_pkg::LSU_INST_NUM];

logic [$clog2(msrh_pkg::LRQ_ENTRY_SIZE)-1:0] w_in_ptr;
logic [$clog2(msrh_pkg::LRQ_ENTRY_SIZE)-1:0] w_out_ptr;
logic                                        w_in_vld;
logic                                        w_out_vld;
logic [msrh_pkg::LRQ_ENTRY_SIZE-1:0]         w_load_valid;

msrh_lsu_pkg::lrq_entry_t w_lrq_entries[msrh_pkg::LRQ_ENTRY_SIZE];

bit_extract_lsb #(.WIDTH(msrh_pkg::LRQ_ENTRY_SIZE)) u_load_vld (.in(~w_lrq_vlds), .out(w_lrq_load_valid_oh));

//
// LRQ Pointer
//
assign w_in_vld  = |w_load_valid;
assign w_out_vld = l1d_ext_req.valid;

inoutptr #(.SIZE(msrh_pkg::LRQ_ENTRY_SIZE)) u_req_ptr(.i_clk (i_clk), .i_reset_n(i_reset_n),
                                                      .i_in_vld (w_in_vld ), .o_in_ptr (w_in_ptr ),
                                                      .i_out_vld(w_out_vld), .o_out_ptr(w_out_ptr));

generate for(genvar b_idx = 0; b_idx < msrh_pkg::LRQ_ENTRY_SIZE; b_idx++) begin : buffer_loop
  assign w_lrq_vlds[b_idx] = w_lrq_entries[b_idx].valid;

  assign w_load_valid[b_idx] = l1d_lrq[0].load & w_lrq_load_valid_oh[b_idx] & !(|w_hit_same_addr_vld[0]);

  msrh_lsu_pkg::lrq_entry_t load_entry;
  assign load_entry.valid = !(|w_hit_same_addr_vld[0]);
  assign load_entry.paddr = {l1d_lrq[0].paddr[riscv_pkg::PADDR_W-1:$clog2(msrh_lsu_pkg::DCACHE_DATA_B_W)], {$clog2(msrh_lsu_pkg::DCACHE_DATA_B_W){1'b0}}};
  assign load_entry.sent  = 1'b0;
  msrh_lrq_entry
  u_entry
    (
     .i_clk     (i_clk    ),
     .i_reset_n (i_reset_n),

     .i_load       (w_load_valid[b_idx]),
     .i_load_entry (load_entry         ),

     .i_sent (l1d_ext_req.valid & (w_out_ptr == b_idx)),
     .o_entry (w_lrq_entries[b_idx])
     );

end // block: buffer_loop
endgenerate

generate for (genvar p_idx = 0; p_idx < msrh_pkg::LSU_INST_NUM; p_idx++) begin : port_loop
  // check the address with different pipeline
  for (genvar p2_idx = 0; p2_idx < msrh_pkg::LSU_INST_NUM; p2_idx++) begin : adj_port_loop
    if (p_idx <= p2_idx) begin
      assign w_hit_port_same_addr_vld[p_idx][p2_idx] = 1'b0;
    end else begin
      assign w_hit_port_same_addr_vld[p_idx][p2_idx] = l1d_lrq[p_idx].load & l1d_lrq[p2_idx].load &
                                                       (l1d_lrq[p_idx ].paddr[riscv_pkg::PADDR_W-1:$clog2(msrh_lsu_pkg::DCACHE_DATA_B_W)] ==
                                                        l1d_lrq[p2_idx].paddr[riscv_pkg::PADDR_W-1:$clog2(msrh_lsu_pkg::DCACHE_DATA_B_W)]);
    end
  end

  // check the address with exist lrq
  for (genvar b_idx = 0; b_idx < msrh_pkg::LRQ_ENTRY_SIZE; b_idx++) begin : buffer_loop
    assign w_hit_same_addr_vld[p_idx][b_idx] = l1d_lrq[p_idx].load &
                                               (w_lrq_entries[b_idx].paddr[riscv_pkg::PADDR_W-1:$clog2(msrh_lsu_pkg::DCACHE_DATA_B_W)] ==
                                                l1d_lrq[p_idx].paddr[riscv_pkg::PADDR_W-1:$clog2(msrh_lsu_pkg::DCACHE_DATA_B_W)]);
  end

  assign l1d_lrq[p_idx].full         = &(w_lrq_vlds | w_lrq_load_valid_oh);
  assign l1d_lrq[p_idx].conflict     = (|w_hit_same_addr_vld[p_idx]) | (|w_hit_port_same_addr_vld[p_idx]);
  assign l1d_lrq[p_idx].lrq_index_oh = l1d_lrq[p_idx].conflict ? w_hit_same_addr_vld[p_idx] : w_load_valid;
end
endgenerate

localparam TAG_FILLER_W = msrh_lsu_pkg::L2_CMD_TAG_W - 1 - $clog2(msrh_pkg::LRQ_ENTRY_SIZE);

assign l1d_ext_req.valid = w_lrq_entries[w_out_ptr].valid & !w_lrq_entries[w_out_ptr].sent;
assign l1d_ext_req.payload.cmd     = msrh_lsu_pkg::M_XRD;
assign l1d_ext_req.payload.addr    = w_lrq_entries[w_out_ptr].paddr;
assign l1d_ext_req.payload.tag     = {msrh_lsu_pkg::L2_UPPER_TAG_L1D, {TAG_FILLER_W{1'b0}}, w_out_ptr};
assign l1d_ext_req.payload.data    = 'h0;
assign l1d_ext_req.payload.byte_en = 'h0;

// Searching LRQ Interface from DCache
assign lrq_search_if.lrq_entry = w_lrq_entries[lrq_search_if.index];

// Notification to LRQ resolve to LDQ
// Note: Now searching from LRQ means L1D will be written and resolve confliction
assign o_lrq_resolve.valid = lrq_search_if.valid;
assign o_lrq_resolve.resolve_index_oh = 1 << lrq_search_if.index;

initial begin
  assert (msrh_lsu_pkg::L2_CMD_TAG_W >= $clog2(msrh_pkg::LRQ_ENTRY_SIZE) + 1);
end

endmodule // msrh_l1d_load_requester
