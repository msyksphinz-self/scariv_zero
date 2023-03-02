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
   .clint_resp (w_resp_clint_if)
   );



scariv_clint
#(
  .DATA_W   (scariv_conf_pkg::ICACHE_DATA_W),
  .TAG_W    (scariv_lsu_pkg::L2_CMD_TAG_W + 2),
  .ADDR_W   (riscv_pkg::PADDR_W),
  .BASE_ADDR('h200_0000),
  .SIZE     ('h1_0000),
  .RD_LAT   (10)
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


logic [ 7: 0] w_ie       [1];  // Interrupt enable per source, for each target
logic [ 2: 0] w_ipriority[8];  // Priority for each source (priority is a reserved keyword)
logic [ 2: 0] w_threshold[1];  // Priority Threshold for each target

logic [ 0: 0] w_int_req;
logic [ 3: 0] w_int_id[1];
logic [ 0: 0] w_int_claim;
logic [ 0: 0] w_int_complete;

assign w_ie[0] = {8{w_plic_if.ie}};
assign w_ipriority[0] = 3'h0;
assign w_ipriority[1] = 3'h0;
assign w_ipriority[2] = 3'h0;
assign w_ipriority[3] = 3'h0;
assign w_ipriority[4] = 3'h0;
assign w_ipriority[5] = 3'h0;
assign w_ipriority[6] = 3'h0;
assign w_ipriority[7] = 3'h0;
assign w_threshold[0] = 3'h0;

assign w_plic_if.int_id = w_int_id[0];


plic_core
  #(
    .SOURCES           (8), //Number of interrupt sources
    .TARGETS           (1), //Number of interrupt targets
    .PRIORITIES        (8), //Number of Priority levels
    .MAX_PENDING_COUNT (0)
    )
u_plic_core
  (
   .clk   (i_clk),     // Input: System clock
   .rst_n (i_reset_n), // Input: Active low asynchronous reset

   .src       (i_interrupts),           // Input: Interrupt request from devices/sources
   .el        (1'b0),                   // Input: Edge/Level sensitive for each source
   .ip        (w_plic_if.ip), // Output: Interrupt Pending for each source

   .ie        (w_ie),                   // Input: Interrupt enable per source, for each target
   .ipriority (w_ipriority),            // Input: Priority for each source (priority is a reserved keyword)
   .threshold (w_threshold),            // Input: Priority Threshold for each target

   .ireq      (w_plic_if.int_valid   ),         // Output: Interrupt request for each target
   .id        (w_int_id              ),         // Output: Interrupt ID (1..SOURCES), for each target
   .claim     (1'b0                  ),         // Input: Interrupt claim
   .complete  (w_plic_if.int_complete)          // Input: Interrupt handling complete
   );

endmodule // scariv_subsystem
