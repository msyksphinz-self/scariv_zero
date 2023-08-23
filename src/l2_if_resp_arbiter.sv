module l2_if_resp_arbiter
  #(parameter ARB_NUM = 4)
(
 l2_resp_if.slave  l2_resp_slave_if[ARB_NUM],
 l2_resp_if.master l2_resp_master_if
 );

logic [ARB_NUM-1: 0]                 w_master_valids;
scariv_lsu_pkg::l2_resp_t            w_master_payloads[ARB_NUM];
logic [l2_resp_master_if.TAG_W-1: 0] w_master_tags[ARB_NUM];
logic [ARB_NUM-1: 0]                 w_master_ready;

scariv_lsu_pkg::l2_resp_t            w_payload_selected;
logic [l2_resp_master_if.TAG_W-1: 0] w_tag_selected;

generate for (genvar a_idx = 0; a_idx < ARB_NUM; a_idx++) begin : req_loop
  assign w_master_valids  [a_idx] = l2_resp_slave_if[a_idx].valid;
  assign w_master_payloads[a_idx] = l2_resp_slave_if[a_idx].payload;
  assign w_master_tags    [a_idx] = l2_resp_slave_if[a_idx].tag;

  assign l2_resp_slave_if[a_idx].ready = w_master_ready[a_idx] & l2_resp_master_if.ready;
end
endgenerate
bit_extract_lsb #(.WIDTH(ARB_NUM)) u_bit_select_valids (.in(w_master_valids), .out(w_master_ready));

bit_oh_or #(.T(scariv_lsu_pkg::l2_resp_t),            .WORDS(ARB_NUM)) sel_resp_payload (.i_oh(w_master_ready), .i_data(w_master_payloads), .o_selected(w_payload_selected));
bit_oh_or #(.T(logic [l2_resp_master_if.TAG_W-1: 0]), .WORDS(ARB_NUM)) sel_resp_tags    (.i_oh(w_master_ready), .i_data(w_master_tags    ), .o_selected(w_tag_selected    ));

assign l2_resp_master_if.valid   = |w_master_valids;
assign l2_resp_master_if.tag     = w_tag_selected;
assign l2_resp_master_if.payload = w_payload_selected;

endmodule // l2_if_resp_arbiter
