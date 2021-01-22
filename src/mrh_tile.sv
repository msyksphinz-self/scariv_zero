module mrh_tile
(
    input logic i_clk,
    input logic i_reset_n,

    // L2 request from ICache
    output logic             ic_req_vaild,
    output mrh_pkg::l2_req_t ic_req_payload,
    input logic              ic_req_ready,

    input logic              ic_resp_valid,
    input mrh_pkg::l2_resp_t ic_resp_payload,
    output logic             ic_resp_ready
);

l2_req_if  l2_req  ();
l2_resp_if l2_resp ();

frontend u_frontend
(
    .i_clk (i_clk),
    .i_reset_n (i_reset_n),

    .l2_req  (l2_req ),
    .l2_resp (l2_resp)
);

endmodule
