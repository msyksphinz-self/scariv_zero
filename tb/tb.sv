module tb;

logic w_clk;
logic w_reset_n;

logic w_timeout;

logic w_terminate;
assign w_terminate = w_timeout;

mrh_tile_wrapper u_mrh_tile_wrapper
  (
    .i_clk     (w_clk),
    .i_reset_n (w_reset_n),

    // L2 request from ICache
    .o_ic_req_valid  (),
    .o_ic_req_cmd    (),
    .o_ic_req_addr   (),
    .o_ic_req_tag    (),
    .o_ic_req_data   (),
    .o_ic_req_byte_en(),
    .i_ic_req_ready  (),

    .i_ic_resp_valid (),
    .i_ic_resp_tag   (),
    .i_ic_resp_data  (),
    .o_ic_resp_ready ()
   );

localparam STEP = 1;
localparam TIMEOUT = 100000;

initial begin
  w_clk = 1'b0;
  w_reset_n = 1'b0;
  #(STEP * TIMEOUT);
  w_timeout = 1'b1;
  $finish;
end

always #STEP begin
  w_clk = ~w_clk;
end

endmodule // tb
