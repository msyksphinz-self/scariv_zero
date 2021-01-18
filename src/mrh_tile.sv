module mrh_tile
(
    input logic i_clk,
    input logic i_reset_n
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

