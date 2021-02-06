module mrh_tile
(
    input logic i_clk,
    input logic i_reset_n,

    // L2 request from ICache
    l2_req_if.master ic_l2_req,
    l2_resp_if.slave ic_l2_resp
);

l2_req_if  l2_req  ();
l2_resp_if l2_resp ();

disp_if    disp_from_frontend ();
disp_if    disp_from_decoder ();
disp_if    disp_to_scheduler ();

frontend u_frontend
(
    .i_clk (i_clk),
    .i_reset_n (i_reset_n),

    .ic_l2_req  (ic_l2_req ),
    .ic_l2_resp (ic_l2_resp),

    .disp (disp_from_frontend)
);

mrh_decoder u_decoder
  (
   .i_clk (i_clk),
   .i_reset_n (i_reset_n),

   .disp_from_frontend (disp_from_frontend),
   .disp_to_renamer  (disp_from_decoder)
   );


mrh_rename u_rename
  (
   .i_clk (i_clk),
   .i_reset_n (i_reset_n),

   .disp_from_frontend (disp_from_decoder),
   .disp_to_scheduler (disp_to_scheduler)
   );


endmodule
