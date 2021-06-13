module msrh_l2_req_arbiter
  #(
    parameter REQ_PORT_NUM = 2
    )
(
 l2_req_if.slave  l1d_ext_in_req[REQ_PORT_NUM],
 l2_req_if.master l1d_ext_req
 );

logic [REQ_PORT_NUM-1: 0] w_req_valid;
logic [REQ_PORT_NUM-1: 0] w_req_accept_oh;
msrh_lsu_pkg::l2_req_t [REQ_PORT_NUM-1:0] w_req_payload;
msrh_lsu_pkg::l2_req_t                    w_req_payload_selected;

generate for (genvar idx=0; idx < REQ_PORT_NUM; idx++) begin : req_loop
  assign w_req_valid[idx]   = l1d_ext_in_req[idx].valid;
  assign w_req_payload[idx] = l1d_ext_in_req[idx].payload;
  assign l1d_ext_in_req[idx].ready = w_req_accept_oh[idx] & l1d_ext_req.ready;
end
endgenerate

simple_arbiter #(.WIDTH(REQ_PORT_NUM)) req_arbiter(.i_valid(w_req_valid), .o_accept(w_req_accept_oh));

bit_oh_or_packed #(.T(msrh_lsu_pkg::l2_req_t), .WORDS(REQ_PORT_NUM))
req_payload_select (.i_oh(w_req_accept_oh), .i_data(w_req_payload), .o_selected(w_req_payload_selected));

assign l1d_ext_req.valid   = |w_req_valid;
assign l1d_ext_req.payload = w_req_payload_selected;

endmodule // msrh_l2_req_arbiter
