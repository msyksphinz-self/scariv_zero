module l2_if_resp_splitter
  #(parameter ARB_NUM = 4)
(
 l2_resp_if.slave  l2_resp_slave_if,
 l2_resp_if.master l2_resp_master_if[ARB_NUM]
 );

// --------
// Request
// --------

logic [ARB_NUM-1: 0] w_region_hit;
generate for (genvar idx = 0; idx < ARB_NUM; idx++) begin : req_loop
  assign w_region_hit[idx] = (l2_resp_slave_if.tag[l2_resp_slave_if.TAG_W-1 -: $clog2(ARB_NUM)] == idx[$clog2(ARB_NUM)-1: 0]);
end
endgenerate


logic [ARB_NUM-1: 0] w_l2_resp_ready;

generate for (genvar idx = 0; idx < ARB_NUM; idx++) begin : split_loop
  assign l2_resp_master_if[idx].valid   = w_region_hit[idx] &  l2_resp_slave_if.valid;
  assign l2_resp_master_if[idx].tag     = l2_resp_slave_if.tag;
  assign l2_resp_master_if[idx].payload = l2_resp_slave_if.payload;

  assign w_l2_resp_ready[idx] = w_region_hit[idx] &  l2_resp_master_if[idx].ready;
end
endgenerate

assign l2_resp_slave_if.ready = |w_l2_resp_ready;


endmodule // l2_if_resp_splitter
