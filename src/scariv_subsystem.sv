module scariv_subsystem (
    input logic i_clk,
    input logic i_reset_n,

    // L2 request from ICache
    l2_req_if.master l2_req,
    l2_resp_if.slave l2_resp,

    // Cache Coherent Interface
    snoop_if.slave snoop_if
);

// CLINT connection
clint_if w_clint_if();

l2_req_if w_req_if[3]();
l2_req_if w_req_if_selected();
l2_req_if w_req_if_splitted[2]();

l2_resp_if w_resp_if[3]();
l2_resp_if w_resp_if_selected();
l2_resp_if w_resp_if_splitted[2]();

localparam tile_if_idx_ic   = 0;
localparam tile_if_idx_data = 1;
localparam tile_if_idx_ptw  = 2;

scariv_tile
u_tile
  (
   .i_clk     (i_clk),
   .i_reset_n (i_reset_n),

    // L2 request from ICache
    .ic_l2_req  (w_req_if [tile_if_idx_ic]),
    .ic_l2_resp (w_resp_if_selected),

    // L2 request from L1D
    .l1d_ext_req  (w_req_if [tile_if_idx_data]),
    .l1d_ext_resp (w_resp_if_selected),

    // Cache Coherent Interface
    .snoop_if (snoop_if),

    // PTW interconnection
    .ptw_req  (w_req_if [tile_if_idx_ptw]),
    .ptw_resp (w_resp_if_selected),

    // CLINT connection
    .clint_if (w_clint_if)
   );


scariv_pkg::paddr_t w_base_addr_list[1];
scariv_pkg::paddr_t w_mask_list[1];
always_comb begin
  w_base_addr_list[0] = 'h0c00_0000;
  w_mask_list     [0] = 'h003f_ffff;
end

l2_if_arbiter
  #(.ARB_NUM(3))
u_arbiter
  (
   .l2_req_slave_if (w_req_if),
   .l2_req_master_if(w_req_if_selected)
);
l2_if_req_splitter_with_others
  #(.ARB_NUM(1))
u_req_splitter
  (
   .l2_req_slave_if (w_req_if_selected),
   .l2_req_master_if(w_req_if_splitted),

   .i_base_addr (w_base_addr_list),
   .i_mask      (w_mask_list)
);

l2_if_resp_arbiter
  #(.ARB_NUM(3))
u_l2_if_arbiter
  (
   .l2_resp_slave_if (w_resp_if),
   .l2_resp_master_if(w_resp_if_selected)
);


l2_req_if  w_main_bus_clint_req_if();
l2_resp_if w_main_bus_clint_resp_if();

assign w_main_bus_clint_req_if.valid     = w_req_if_splitted[0].valid;
assign w_main_bus_clint_req_if.payload   = w_req_if_splitted[0].payload;
assign w_req_if_splitted[0].ready  = w_main_bus_clint_req_if.ready;



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
  .i_reset_n(i_reset_n),

  // clint
  .i_req_valid   (w_main_bus_clint_req_if.valid           ),
  .i_req_cmd     (w_main_bus_clint_req_if.payload.cmd     ),
  .i_req_addr    (w_main_bus_clint_req_if.payload.addr    ),
  .i_req_tag     (w_main_bus_clint_req_if.payload.tag     ),
  .i_req_data    (w_main_bus_clint_req_if.payload.data    ),
  .i_req_byte_en (w_main_bus_clint_req_if.payload.byte_en ),
  .o_req_ready   (w_main_bus_clint_req_if.ready           ),

  .o_resp_valid  (w_main_bus_clint_resp_if.valid        ),
  .o_resp_tag    (w_main_bus_clint_resp_if.payload.tag  ),
  .o_resp_data   (w_main_bus_clint_resp_if.payload.data ),
  .i_resp_ready  (w_main_bus_clint_resp_if.ready        ),

  .clint_if (w_clint_if)
);

endmodule // scariv_tile
