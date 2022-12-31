module scariv_tile (
    input logic i_clk,
    input logic i_reset_n,

    // L2 request from ICache
    l2_req_if.master ic_l2_req,
    l2_resp_if.slave ic_l2_resp,

    // L2 request from L1D
    l2_req_if.master l1d_ext_req,
    l2_resp_if.slave l1d_ext_resp,

    // Cache Coherent Interface
    snoop_if.slave snoop_if,

    // PTW interconnection
    l2_req_if.master ptw_req,
    l2_resp_if.slave ptw_resp,
);

// L2 request from ICache
l2_req_if  w_ic_l2_req  ();
l2_resp_if w_ic_l2_resp ();
// L2 request from L1D
l2_req_if  w_l1d_ext_req ();
l2_resp_if w_l1d_ext_resp ();
// Cache Coherent Interface
snoop_if w_snoop_if ();
// PTW interconnection
l2_req_if  w_ptw_req ();
l2_resp_if w_ptw_resp ();
// CLINT connection
clint_if w_clint_if();

scariv_tile
u_tile
  (
   .i_clk     (i_clk),
   .i_reset_n (i_reset_n),

    // L2 request from ICache
    .ic_l2_req  (w_ic_l2_req ),
    .ic_l2_resp (w_ic_l2_resp),

    // L2 request from L1D
    .l1d_ext_req  (w_l1d_ext_req ),
    .l1d_ext_resp (w_l1d_ext_resp),

    // Cache Coherent Interface
    .snoop_if (w_snoop_if),

    // PTW interconnection
    .ptw_req  (w_ptw_req ),
    .ptw_resp (w_ptw_resp),

    // CLINT connection
    .clint_if (w_clint_if)
   );


l2_req_if req_if[4]();
l2_req_if req_if_selected();
l2_req_if req_if_splitted[2]();

scariv_pkg::paddr_t w_base_addr_list[1];
always_comb begin
  w_base_addr_list[0] = 'hc0c00_0000;
  w_mask_list     [0] = 'hc003f_ffff;
end

l2c_if_arbiter
  #(.ARB_NUM(4))
u_arbiter
  (
   .l2_req_slave_if (req_if),
   .l2_req_master_if(req_if_selected)
);
l2c_if_splitter_with_others
  #(.ARB_NUM(1))
u_arbiter
  (
   .l2_req_slave_if (req_if_selected),
   .l2_req_master_if(req_if_splitted)

   .i_base_addr (w_base_addr_list),
   .i_mask      (w_mask_list),
);


l2_req_if  w_main_bus_clint_req_if();
l2_resp_if w_main_bus_clint_resp_if();

assign main_bus_clint_if.valid   = req_if_splitted[0].valid;
assign main_bus_clint_if.payload = req_if_splitted[0].payload;
assign req_if_splitted[0].ready  = main_bus_clint_if.ready;

scariv_clint
#(
  .DATA_W   (scariv_conf_pkg::ICACHE_DATA_W),
  .TAG_W    (scariv_lsu_pkg::L2_CMD_TAG_W),
  .ADDR_W   (riscv_pkg::PADDR_W),
  .BASE_ADDR('h200_0000),
  .SIZE     ('h1_0000),
  .RD_LAT   (10)
) u_clint (
  .i_clk    (i_clk),
  .i_reset_n(i_ram_reset_n),

  // clint
  .i_req_valid   (w_main_bus_clint_if.valid           ),
  .i_req_cmd     (w_main_bus_clint_if.payload.cmd     ),
  .i_req_addr    (w_main_bus_clint_if.payload.addr    ),
  .i_req_tag     (w_main_bus_clint_if.payload.tag     ),
  .i_req_data    (w_main_bus_clint_if.payload.data    ),
  .i_req_byte_en (w_main_bus_clint_if.payload.byte_en ),
  .o_req_ready   (w_main_bus_clint_if.ready           ),

  .o_resp_valid  (w_main_bus_clint_resp_if.valid        ),
  .o_resp_tag    (w_main_bus_clint_resp_if.payload.tag  ),
  .o_resp_data   (w_main_bus_clint_resp_if.payload.data ),
  .i_resp_ready  (w_main_bus_clint_resp_if.ready        ),

  .clint_if (w_clint_if)
);

endmodule // scariv_tile
