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
  if (!i_reset_n) begin
    r_ext_wr_req_valid <= 1'b0;
    r_ext_evict_payload <= 'h0;
  end else begin
    if (l1d_evict_if.valid & !l1d_ext_wr_req.ready & ~r_ext_wr_req_valid) begin
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

`ifdef SIMULATION

import "DPI-C" function void record_l1d_evict
(
 input longint rtl_time,
 input longint paddr,
 input int     ram_addr,
 input int unsigned array[msrh_conf_pkg::DCACHE_DATA_W/32],
 input int     size
);

int unsigned l1d_array[msrh_conf_pkg::DCACHE_DATA_W/32];
generate for (genvar idx = 0; idx < msrh_conf_pkg::DCACHE_DATA_W/32; idx++) begin : array_loop
  assign l1d_array[idx] = l1d_ext_wr_req.payload.data[idx*32+:32];
end
endgenerate

always_ff @ (negedge i_clk, negedge i_reset_n) begin
  if (i_reset_n) begin
    if (l1d_ext_wr_req.valid & l1d_ext_wr_req.ready) begin
      /* verilator lint_off WIDTH */
      record_l1d_evict ($time,
                        l1d_ext_wr_req.payload.addr,
                        l1d_ext_wr_req.payload.addr[$clog2(msrh_lsu_pkg::DCACHE_DATA_B_W) +: msrh_lsu_pkg::DCACHE_TAG_LOW],
                        l1d_array,
                        msrh_lsu_pkg::DCACHE_DATA_B_W);
      // $fwrite(msrh_pkg::STDERR, "%t : L1D Store-Out : %0x(%x) <= ",
      //         $time,
      //         l1d_ext_wr_req.payload.addr,
      //         l1d_ext_wr_req.payload.addr[$clog2(msrh_lsu_pkg::DCACHE_DATA_B_W) +: msrh_lsu_pkg::DCACHE_TAG_LOW]);
      // for (int i = msrh_lsu_pkg::DCACHE_DATA_B_W/4-1; i >=0 ; i--) begin
      //   $fwrite(msrh_pkg::STDERR, "%08x", l1d_ext_wr_req.payload.data[i*32 +: 32]);
      //   if (i != 0) begin
      //     $fwrite(msrh_pkg::STDERR, "_");
      //   end else begin
      //     $fwrite(msrh_pkg::STDERR, "\n");
      //   end
      // end
    end // if (l1d_ext_wr_req.valid)
  end // if (i_reset_n)
end // always_ff @ (negedge i_clk, negedge i_reset_n)
`endif // SIMULATION

endmodule // msrh_store_requestor
