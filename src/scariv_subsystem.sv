// ------------------------------------------------------------------------
// NAME : scariv_subsystem
// TYPE : module
// ------------------------------------------------------------------------
// SCARIV Subsystem Top
// ------------------------------------------------------------------------
//
// ------------------------------------------------------------------------

module scariv_subsystem (
    input logic i_clk,
    input logic i_reset_n,

    // L2 request from ICache
    l2_req_if.master l2_req,
    l2_resp_if.slave l2_resp,


    // External Interrupts
    input logic [ 7: 0] i_interrupts,

    // Cache Coherent Interface
    snoop_if.slave snoop_if
);

// CLINT connection
clint_if w_clint_if();
// PLIC connection
plic_if  w_plic_if();

l2_req_if #(.TAG_W(scariv_lsu_pkg::L2_CMD_TAG_W)) w_req_core_ic_if();
l2_req_if #(.TAG_W(scariv_lsu_pkg::L2_CMD_TAG_W)) w_req_core_dc_if();
l2_req_if #(.TAG_W(scariv_lsu_pkg::L2_CMD_TAG_W)) w_req_core_ptw_if();

l2_resp_if #(.TAG_W(scariv_lsu_pkg::L2_CMD_TAG_W)) w_resp_core_ic_if ();
l2_resp_if #(.TAG_W(scariv_lsu_pkg::L2_CMD_TAG_W)) w_resp_core_dc_if ();
l2_resp_if #(.TAG_W(scariv_lsu_pkg::L2_CMD_TAG_W)) w_resp_core_ptw_if();

l2_req_if  #(.TAG_W(scariv_lsu_pkg::L2_CMD_TAG_W + 2)) w_req_clint_if ();
l2_resp_if #(.TAG_W(scariv_lsu_pkg::L2_CMD_TAG_W + 2)) w_resp_clint_if();

l2_req_if  #(.TAG_W(scariv_lsu_pkg::L2_CMD_TAG_W + 2)) w_req_plic_if ();
l2_resp_if #(.TAG_W(scariv_lsu_pkg::L2_CMD_TAG_W + 2)) w_resp_plic_if();

l2_req_if  #(.TAG_W(scariv_lsu_pkg::L2_CMD_TAG_W + 2)) w_req_lmul_exc_rom_if ();
l2_resp_if #(.TAG_W(scariv_lsu_pkg::L2_CMD_TAG_W + 2)) w_resp_lmul_exc_rom_if();

scariv_tile
u_tile
  (
   .i_clk     (i_clk),
   .i_reset_n (i_reset_n),

   // L2 request from ICache
   .ic_l2_req  (w_req_core_ic_if ),
   .ic_l2_resp (w_resp_core_ic_if),

   // L2 request from L1D
   .l1d_ext_req  (w_req_core_dc_if ),
   .l1d_ext_resp (w_resp_core_dc_if),

   // Cache Coherent Interface
   .snoop_if (snoop_if),

   // PTW interconnection
   .ptw_req  (w_req_core_ptw_if ),
   .ptw_resp (w_resp_core_ptw_if),

   // CLINT connection
   .clint_if (w_clint_if),
   // PLIC connection
   .plic_if (w_plic_if)
   );


scariv_ss_router
u_router
  (
   .core_ic_req  (w_req_core_ic_if),
   .core_ic_resp (w_resp_core_ic_if),

   // Request from Core DCache
   .core_dc_req  (w_req_core_dc_if),
   .core_dc_resp (w_resp_core_dc_if),

   // Request from Core PTW
   .core_ptw_req  (w_req_core_ptw_if),
   .core_ptw_resp (w_resp_core_ptw_if),

   // -------
   // Output
   // -------
   // L2
   .l2_req  (l2_req ),
   .l2_resp (l2_resp),

   // CLINT
   .clint_req  (w_req_clint_if),
   .clint_resp (w_resp_clint_if),

   // PLIC
   .plic_req  (w_req_plic_if),
   .plic_resp (w_resp_plic_if),

   // LMUL_EXC_HANDLER_ROM
   .lmul_exc_rom_req  (w_req_lmul_exc_rom_if),
   .lmul_exc_rom_resp (w_resp_lmul_exc_rom_if)
   );


scariv_rom
#(
  .DATA_W   (scariv_conf_pkg::ICACHE_DATA_W),
  .TAG_W    (scariv_lsu_pkg::L2_CMD_TAG_W + 2),
  .ADDR_W   (riscv_pkg::PADDR_W),
  .BASE_ADDR('h2000),
  .SIZE     ('h1_0000),
  .HEX_FILE_BASE ("../../../src/lmul_exc_handler/lmul_exc_rom")
) u_lmul_exc_handler (
  .i_clk    (i_clk),
  .i_reset_n(i_reset_n),

  // clint
  .i_req_valid   (w_req_lmul_exc_rom_if.valid           ),
  .i_req_cmd     (w_req_lmul_exc_rom_if.payload.cmd     ),
  .i_req_addr    (w_req_lmul_exc_rom_if.payload.addr    ),
  .i_req_tag     (w_req_lmul_exc_rom_if.tag             ),
  .i_req_data    (w_req_lmul_exc_rom_if.payload.data    ),
  .i_req_byte_en (w_req_lmul_exc_rom_if.payload.byte_en ),
  .o_req_ready   (w_req_lmul_exc_rom_if.ready           ),

  .o_resp_valid  (w_resp_lmul_exc_rom_if.valid        ),
  .o_resp_tag    (w_resp_lmul_exc_rom_if.tag          ),
  .o_resp_data   (w_resp_lmul_exc_rom_if.payload.data ),
  .i_resp_ready  (w_resp_lmul_exc_rom_if.ready        )
);


scariv_clint
#(
  .DATA_W   (scariv_conf_pkg::ICACHE_DATA_W),
  .TAG_W    (scariv_lsu_pkg::L2_CMD_TAG_W + 2),
  .ADDR_W   (riscv_pkg::PADDR_W),
  .BASE_ADDR('h200_0000),
  .SIZE     ('h1_0000)
) u_clint (
  .i_clk    (i_clk),
  .i_reset_n(i_reset_n),

  // clint
  .i_req_valid   (w_req_clint_if.valid           ),
  .i_req_cmd     (w_req_clint_if.payload.cmd     ),
  .i_req_addr    (w_req_clint_if.payload.addr    ),
  .i_req_tag     (w_req_clint_if.tag             ),
  .i_req_data    (w_req_clint_if.payload.data    ),
  .i_req_byte_en (w_req_clint_if.payload.byte_en ),
  .o_req_ready   (w_req_clint_if.ready           ),

  .o_resp_valid  (w_resp_clint_if.valid        ),
  .o_resp_tag    (w_resp_clint_if.tag          ),
  .o_resp_data   (w_resp_clint_if.payload.data ),
  .i_resp_ready  (w_resp_clint_if.ready        ),

  .clint_if (w_clint_if)
);


scariv_plic
#(
  .DATA_W   (scariv_conf_pkg::ICACHE_DATA_W),
  .TAG_W    (scariv_lsu_pkg::L2_CMD_TAG_W + 2),
  .ADDR_W   (riscv_pkg::PADDR_W),
  .BASE_ADDR('hc00_0000),
  .SIZE     ('h1_0000),
  .NUM_PRIORITIES (2),
  .NUM_HARTS      (1),
  .NUM_SOURCES    (8)
) u_plic (
  .i_clk    (i_clk),
  .i_reset_n(i_reset_n),

  .i_interrupts  (i_interrupts),

  // PLIC
  .i_req_valid   (w_req_plic_if.valid           ),
  .i_req_cmd     (w_req_plic_if.payload.cmd     ),
  .i_req_addr    (w_req_plic_if.payload.addr - 'hc00_0000),
  .i_req_tag     (w_req_plic_if.tag             ),
  .i_req_data    (w_req_plic_if.payload.data    ),
  .i_req_byte_en (w_req_plic_if.payload.byte_en ),
  .o_req_ready   (w_req_plic_if.ready           ),

  .o_resp_valid  (w_resp_plic_if.valid        ),
  .o_resp_tag    (w_resp_plic_if.tag          ),
  .o_resp_data   (w_resp_plic_if.payload.data ),
  .i_resp_ready  (w_resp_plic_if.ready        ),

  .plic_if (w_plic_if)
);


endmodule // scariv_subsystem
