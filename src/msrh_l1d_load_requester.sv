module msrh_l1d_load_requester
  (
   input logic  i_clk,
   input logic  i_reset_n,

   l1d_lrq_if.slave l1d_lrq[msrh_pkg::LSU_INST_NUM],

   output       msrh_pkg::l1d_ext_req_t o_l1d_ext_req
   );


logic [msrh_pkg::LRQ_ENTRY_SIZE-1: 0] w_lrq_vlds;
logic [msrh_pkg::LRQ_ENTRY_SIZE-1: 0] w_lrq_load_valid_oh;

logic [$clog2(msrh_pkg::LRQ_ENTRY_SIZE)-1:0] w_in_ptr;
logic [$clog2(msrh_pkg::LRQ_ENTRY_SIZE)-1:0] w_out_ptr;
logic                                        w_in_vld;
logic                                        w_out_vld;
logic [msrh_pkg::LRQ_ENTRY_SIZE-1:0]         w_load_valid;

msrh_pkg::lrq_entry_t w_lrq_entries[msrh_pkg::LRQ_ENTRY_SIZE];

bit_tree_lsb #(.WIDTH(msrh_pkg::LRQ_ENTRY_SIZE)) u_load_vld (.in(~w_lrq_vlds), .out(w_lrq_load_valid_oh));

//
// LRQ Pointer
//
assign w_in_vld  = |w_load_valid;
assign w_out_vld = o_l1d_ext_req.valid;

inoutptr #(.SIZE(msrh_pkg::LRQ_ENTRY_SIZE)) u_req_ptr(.i_clk (i_clk), .i_reset_n(i_reset_n),
                                                      .i_in_vld (w_in_vld ), .o_in_ptr (w_in_ptr ),
                                                      .i_out_vld(w_out_vld), .o_out_ptr(w_out_ptr));

generate for(genvar b_idx = 0; b_idx < msrh_pkg::LRQ_ENTRY_SIZE; b_idx++) begin : buffer_loop
  assign w_lrq_vlds[b_idx] = w_lrq_entries[b_idx].valid;

  assign w_load_valid[b_idx] = w_lrq_load_valid_oh[b_idx] & l1d_lrq[0].load;

  msrh_pkg::lrq_entry_t load_entry;
  assign load_entry.valid = 1'b1;
  assign load_entry.paddr = l1d_lrq[0].paddr[riscv_pkg::PADDR_W-1:$clog2(msrh_pkg::DCACHE_DATA_B_W)];
  assign load_entry.sent  = 1'b0;
  msrh_lrq_entry
  u_entry
    (
     .i_clk     (i_clk    ),
     .i_reset_n (i_reset_n),

     .i_load       (w_load_valid[b_idx]),
     .i_load_entry (load_entry         ),

     .i_sent (o_l1d_ext_req.valid & (w_out_ptr == b_idx)),
     .o_entry (w_lrq_entries[b_idx])
     );

end // block: buffer_loop
endgenerate

generate for (genvar p_idx = 0; p_idx < msrh_pkg::LSU_INST_NUM; p_idx++) begin : port_loop
  logic [msrh_pkg::LRQ_ENTRY_SIZE-1: 0] w_hit_same_addr_vld;
  for (genvar b_idx = 0; b_idx < msrh_pkg::LRQ_ENTRY_SIZE; b_idx++) begin : buffer_loop
    assign w_hit_same_addr_vld[b_idx] = l1d_lrq[p_idx].load &
                                        (w_lrq_entries[b_idx].paddr[riscv_pkg::PADDR_W-1:$clog2(msrh_pkg::DCACHE_DATA_B_W)] ==
                                         l1d_lrq[p_idx].paddr[riscv_pkg::PADDR_W-1:$clog2(msrh_pkg::DCACHE_DATA_B_W)]);
  end

  assign l1d_lrq[p_idx].full     = &(w_lrq_vlds | w_lrq_load_valid_oh);
  assign l1d_lrq[p_idx].conflict = |w_hit_same_addr_vld;
end
endgenerate

assign o_l1d_ext_req.valid = w_lrq_entries[w_out_ptr].valid & !w_lrq_entries[w_out_ptr].sent;
assign o_l1d_ext_req.paddr = w_lrq_entries[w_out_ptr].paddr;

endmodule // msrh_l1d_load_requester
