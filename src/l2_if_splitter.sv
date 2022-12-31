module l2_if_splitter
  #(parameter ARB_NUM = 4)
(
 l2_req_if.slave  l2_req_slave_if,
 l2_req_if.master l2_req_master_if[ARB_NUM]

 input scariv_pkg::paddr_t i_base_addr[ARB_NUM],
 input scariv_pkg::paddr_t i_mask     [ARB_NUM],
 );

logic [ARB_NUM-1: 0] w_region_hit;
generate for (genvar idx = 0; idx < ARB_NUM; idx++) begin : req_loop
  assign w_region_hit[idx] = (l2_req_slave_if.payload.paddr & ~i_mask[idx]) == i_base_addr[idx];
end
endgenerate

always_comb begin
  $assert ($onehot0(w_region_hit));
end


logic [ARB_NUM-1: 0] w_l2_resp_ready;

generate for (genvar idx = 0; idx < ARB_NUM; idx++) begin : split_loop
  assign l2_req_master_if[idx].valid = w_region_hit[idx] &  l2_req_slave_if.valid;
  assign l2_req_master_if[idx].payload = l2_req_slave_if.payload;

  assign w_l2_resp_ready[idx] = w_region_hit[idx] &  l2_req_master_if[idx].ready;
end
endgenerate

assign l2_req_slave_if.ready = |w_l2_resp_ready;

endmodule // l2_if_arbiter
