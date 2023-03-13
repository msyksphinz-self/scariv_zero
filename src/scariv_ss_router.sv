// ------------------------------------------------------------------------
// NAME : scariv_ss_router
// TYPE : module
// ------------------------------------------------------------------------
// SCARIV subsystem request router
// ------------------------------------------------------------------------
// ------------------------------------------------------------------------

module scariv_ss_router
  (
   // Input
   // Request from Core ICache
   l2_req_if.slave   core_ic_req,
   l2_resp_if.master core_ic_resp,

   // Request from Core DCache
   l2_req_if.slave   core_dc_req,
   l2_resp_if.master core_dc_resp,

   // Request from Core PTW
   l2_req_if.slave   core_ptw_req,
   l2_resp_if.master core_ptw_resp,

   // -------
   // Output
   // -------
   // L2
   l2_req_if.master l2_req,
   l2_resp_if.slave l2_resp,

   // CLINT
   l2_req_if.master clint_req,
   l2_resp_if.slave clint_resp,

   // PLIC
   l2_req_if.master plic_req,
   l2_resp_if.slave plic_resp
   );

localparam EXTENDED_TAG_W = scariv_lsu_pkg::L2_CMD_TAG_W + $clog2(3);

l2_req_if #(.TAG_W(EXTENDED_TAG_W)) w_req_if[3]();
l2_req_if #(.TAG_W(EXTENDED_TAG_W)) w_req_if_selected();
l2_req_if #(.TAG_W(EXTENDED_TAG_W)) w_req_if_splitted[3]();

assign w_req_if[0].valid   = core_ic_req.valid;
assign w_req_if[0].tag     = {2'b00, core_ic_req.tag};
assign w_req_if[0].payload = core_ic_req.payload;
assign core_ic_req.ready   = w_req_if[0].ready;

assign w_req_if[1].valid   = core_dc_req.valid;
assign w_req_if[1].tag     = {2'b01, core_dc_req.tag};
assign w_req_if[1].payload = core_dc_req.payload;
assign core_dc_req.ready   = w_req_if[1].ready;

assign w_req_if[2].valid   = core_ptw_req.valid;
assign w_req_if[2].tag     = {2'b10, core_ptw_req.tag};
assign w_req_if[2].payload = core_ptw_req.payload;
assign core_ptw_req.ready  = w_req_if[2].ready;

scariv_pkg::paddr_t w_base_addr_list[2];
scariv_pkg::paddr_t w_mask_list[2];
always_comb begin
  w_base_addr_list[0] = 'h0200_0000; // CLINT
  w_mask_list     [0] = 'h003f_ffff; // CLINT
  w_base_addr_list[1] = 'h0c00_0000; // PLIC
  w_mask_list     [1] = 'h00ff_ffff; // PLIC
end


l2_if_arbiter
  #(.TAG_W (EXTENDED_TAG_W),
    .ARB_NUM(3))
u_req_arbiter
  (
   .l2_req_slave_if (w_req_if),
   .l2_req_master_if(w_req_if_selected)
);
l2_if_req_splitter_with_others
  #(.ARB_NUM(2))
u_req_splitter
  (
   .l2_req_slave_if (w_req_if_selected),
   .l2_req_master_if(w_req_if_splitted),

   .i_base_addr (w_base_addr_list),
   .i_mask      (w_mask_list)
);

assign clint_req.valid   = w_req_if_splitted[0].valid;
assign clint_req.tag     = w_req_if_splitted[0].tag;
assign clint_req.payload = w_req_if_splitted[0].payload;
assign w_req_if_splitted[0].ready = clint_req.ready;

assign plic_req.valid   = w_req_if_splitted[1].valid;
assign plic_req.tag     = w_req_if_splitted[1].tag;
assign plic_req.payload = w_req_if_splitted[1].payload;
assign w_req_if_splitted[1].ready = plic_req.ready;

assign l2_req.valid   = w_req_if_splitted[2].valid;
assign l2_req.tag     = w_req_if_splitted[2].tag;
assign l2_req.payload = w_req_if_splitted[2].payload;
assign w_req_if_splitted[2].ready = l2_req.ready;




l2_resp_if #(.TAG_W(EXTENDED_TAG_W)) w_resp_if[2]();
l2_resp_if #(.TAG_W(EXTENDED_TAG_W)) w_resp_if_selected();
l2_resp_if #(.TAG_W(EXTENDED_TAG_W)) w_resp_if_splitted[3]();

assign w_resp_if[0].valid = clint_resp.valid;
assign w_resp_if[0].tag   = clint_resp.tag;
assign w_resp_if[0].payload = clint_resp.payload;
assign clint_resp.ready = w_resp_if[0].ready;


assign w_resp_if[1].valid   = l2_resp.valid;
assign w_resp_if[1].tag     = l2_resp.tag;
assign w_resp_if[1].payload = l2_resp.payload;
assign l2_resp.ready = w_resp_if[1].ready;

l2_if_resp_arbiter
  #(.ARB_NUM(2))
u_resp_arbiter
  (
   .l2_resp_slave_if (w_resp_if),
   .l2_resp_master_if(w_resp_if_selected)
);



l2_if_resp_splitter
  #(.ARB_NUM(3))
u_resp_splitter
  (
   .l2_resp_slave_if (w_resp_if_selected),
   .l2_resp_master_if(w_resp_if_splitted)
);


assign core_ic_resp.valid   = w_resp_if_splitted[0].valid;
assign core_ic_resp.tag     = w_resp_if_splitted[0].tag[scariv_lsu_pkg::L2_CMD_TAG_W-1: 0];
assign core_ic_resp.payload = w_resp_if_splitted[0].payload;
assign w_resp_if_splitted[0].ready = core_ic_resp.ready;

assign core_dc_resp.valid   = w_resp_if_splitted[1].valid;
assign core_dc_resp.tag     = w_resp_if_splitted[1].tag[scariv_lsu_pkg::L2_CMD_TAG_W-1: 0];
assign core_dc_resp.payload = w_resp_if_splitted[1].payload;
assign w_resp_if_splitted[1].ready = core_dc_resp.ready;

assign core_ptw_resp.valid   = w_resp_if_splitted[2].valid;
assign core_ptw_resp.tag     = w_resp_if_splitted[2].tag[scariv_lsu_pkg::L2_CMD_TAG_W-1: 0];
assign core_ptw_resp.payload = w_resp_if_splitted[2].payload;
assign w_resp_if_splitted[2].ready = core_ptw_resp.ready;

endmodule // scariv_ss_router
