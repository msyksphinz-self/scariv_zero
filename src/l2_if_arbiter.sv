module l2_if_arbiter
  #(parameter ARB_NUM = 4)
(
 l2_req_if.slave  l2_req_slave_if[ARB_NUM],
 l2_req_if.master l2_req_master_if

 // l2_resp_if.slave  l2_resp_slave_if,
 // l2_resp_if.master l2_resp_master_if[ARB_NUM]
 );

logic [ARB_NUM-1: 0] w_slave_valids;
msrh_lsu_pkg::l2_req_t w_slave_payloads[ARB_NUM];
logic [ARB_NUM-1: 0] w_slave_ready;
msrh_lsu_pkg::l2_req_t w_payload_selected;

generate for (genvar a_idx = 0; a_idx < ARB_NUM; a_idx++) begin : req_loop
  assign w_slave_valids  [a_idx] = l2_req_slave_if[a_idx].valid;
  assign w_slave_payloads[a_idx] = l2_req_slave_if[a_idx].payload;

  assign l2_req_slave_if[a_idx].ready = w_slave_ready[a_idx] & l2_req_master_if.ready;
end
endgenerate
bit_extract_lsb #(.WIDTH(ARB_NUM)) u_bit_select_valids (.in(w_slave_valids), .out(w_slave_ready));

bit_oh_or #(.T(msrh_lsu_pkg::l2_req_t), .WORDS(ARB_NUM)) sel_req_payload (.i_oh(w_slave_ready), .i_data(w_slave_payloads), .o_selected(w_payload_selected));

assign l2_req_master_if.valid = |w_slave_valids;
assign l2_req_master_if.payload = w_payload_selected;


// generate for (genvar a_idx = 0; a_idx < ARB_NUM; a_idx++) begin : resp_loop
//   assign l2_resp_master_if[a_idx].valid = l2_resp_slave_if.valid;
//   assign l2_resp_master_if[a_idx].payload = l2_resp_slave_if.payload;
// end
// endgenerate

endmodule // l2_if_arbiter
