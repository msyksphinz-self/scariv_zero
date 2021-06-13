module msrh_store_requestor
  (
   input logic  i_clk,
   input logic  i_reset_n,

   l1d_evict_if.slave l1d_evict_if,

   l2_req_if.master  l1d_ext_wr_req
   );

logic           r_ext_wr_req_valid;
msrh_lsu_pkg::evict_payload_t r_ext_evict_payload;

always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (i_reset_n) begin
    r_ext_wr_req_valid <= 1'b0;
    r_ext_evict_payload <= 'h0;
  end else begin
    if (l1d_evict_if.valid & !l1d_ext_wr_req.ready) begin
      r_ext_wr_req_valid <= 1'b1;
      r_ext_evict_payload <= l1d_evict_if.payload;
    end else if (l1d_ext_wr_req.ready) begin
      r_ext_wr_req_valid <= 1'b0;
    end
  end // else: !if(i_reset_n)
end // always_ff @ (posedge i_clk, negedge i_reset_n)

always_comb begin
  l1d_ext_wr_req.valid           = l1d_evict_if.valid | r_ext_wr_req_valid;
  l1d_ext_wr_req.payload.cmd     = msrh_lsu_pkg::M_XWR;
  if (r_ext_wr_req_valid) begin
    l1d_ext_wr_req.payload.addr    = r_ext_evict_payload.paddr;
    l1d_ext_wr_req.payload.tag     = {msrh_lsu_pkg::L2_UPPER_TAG_WR_L1D, {(msrh_lsu_pkg::L2_CMD_TAG_W-2){1'b0}}};
    l1d_ext_wr_req.payload.data    = r_ext_evict_payload.data;
    l1d_ext_wr_req.payload.byte_en = {msrh_lsu_pkg::DCACHE_DATA_B_W{1'b1}};
  end else begin
    l1d_ext_wr_req.payload.addr    = l1d_evict_if.payload.paddr;
    l1d_ext_wr_req.payload.tag     = {msrh_lsu_pkg::L2_UPPER_TAG_WR_L1D, {(msrh_lsu_pkg::L2_CMD_TAG_W-2){1'b0}}};
    l1d_ext_wr_req.payload.data    = l1d_evict_if.payload.data;
    l1d_ext_wr_req.payload.byte_en = {msrh_lsu_pkg::DCACHE_DATA_B_W{1'b1}};
  end // else: !if(r_ext_wr_req_valid)
end // always_comb

assign l1d_evict_if.ready = !r_ext_wr_req_valid;

endmodule // msrh_store_requestor
