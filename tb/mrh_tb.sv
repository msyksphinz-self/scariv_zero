module mrh_tb
  (
   input logic i_clk,
   input logic i_reset_n
   );

/* from Frontend IC */
logic                                w_ic_req_valid;
mrh_pkg::mem_cmd_t                   w_ic_req_cmd;
logic [riscv_pkg::PADDR_W-1:0]       w_ic_req_addr;
logic [mrh_pkg::L2_CMD_TAG_W-1:0]    w_ic_req_tag;
logic [mrh_pkg::ICACHE_DATA_W-1:0]   w_ic_req_data;
logic [mrh_pkg::ICACHE_DATA_W/8-1:0] w_ic_req_byte_en;
logic                                w_ic_req_ready;

logic                                w_ic_resp_valid;
logic [mrh_pkg::L2_CMD_TAG_W-1:0]    w_ic_resp_tag;
logic [mrh_pkg::ICACHE_DATA_W-1:0]   w_ic_resp_data;
logic                                w_ic_resp_ready;



/* from ELF Loader */
logic                                w_elf_req_valid;
mrh_pkg::mem_cmd_t                   w_elf_req_cmd;
logic [riscv_pkg::PADDR_W-1:0]       w_elf_req_addr;
logic [mrh_pkg::L2_CMD_TAG_W-1:0]    w_elf_req_tag;
logic [mrh_pkg::ICACHE_DATA_W-1:0]   w_elf_req_data;
logic [mrh_pkg::ICACHE_DATA_W/8-1:0] w_elf_req_byte_en;
logic                                w_elf_req_ready;


/* L2 Interface */
logic                                w_l2_req_valid;
mrh_pkg::mem_cmd_t                   w_l2_req_cmd;
logic [riscv_pkg::PADDR_W-1:0]       w_l2_req_addr;
logic [mrh_pkg::L2_CMD_TAG_W-1:0]    w_l2_req_tag;
logic [mrh_pkg::ICACHE_DATA_W-1:0]   w_l2_req_data;
logic [mrh_pkg::ICACHE_DATA_W/8-1:0] w_l2_req_byte_en;
logic                                w_l2_req_ready;

logic                                w_l2_resp_valid;
logic [mrh_pkg::L2_CMD_TAG_W-1:0]    w_l2_resp_tag;
logic [mrh_pkg::ICACHE_DATA_W-1:0]   w_l2_resp_data;
logic                                w_l2_resp_ready;


mrh_tile_wrapper
  u_mrh_tile_wrapper
    (
    .i_clk     (i_clk    ),
    .i_reset_n (i_reset_n),

    // L2 request from ICache
    .o_ic_req_valid   (w_ic_req_valid ),
    .o_ic_req_cmd     (w_ic_req_cmd   ),
    .o_ic_req_addr    (w_ic_req_addr  ),
    .o_ic_req_tag     (w_ic_req_tag   ),
    .o_ic_req_data    (w_ic_req_data  ),
    .o_ic_req_byte_en (w_ic_req_byte_en),
    .i_ic_req_ready   (w_ic_req_ready ),

    .i_ic_resp_valid  (w_ic_resp_valid),
    .i_ic_resp_tag    (w_ic_resp_tag  ),
    .i_ic_resp_data   (w_ic_resp_data ),
    .o_ic_resp_ready  (w_ic_resp_ready)
     );


tb_l2_behavior_ram
  #(
    .DATA_W    (mrh_pkg::ICACHE_DATA_W),
    .TAG_W     (mrh_pkg::L2_CMD_TAG_W),
    .ADDR_W    (riscv_pkg::PADDR_W),
    .BASE_ADDR ('h8000_0000),
    .SIZE      (4096),
    .RD_LAT    (10)
    )
u_tb_l2_behavior_ram
  (
   .i_clk     (i_clk    ),
   .i_reset_n (i_reset_n),

   // // L2 request from ICache
   // .i_req_valid   (w_l2_req_valid ),
   // .i_req_cmd     (w_l2_req_cmd   ),
   // .i_req_addr    (w_l2_req_addr  ),
   // .i_req_tag     (w_l2_req_tag   ),
   // .i_req_data    (w_l2_req_data  ),
   // .i_req_byte_en (w_l2_req_byte_en),
   // .o_req_ready   (w_l2_req_ready ),
   //
   // .o_resp_valid  (w_l2_resp_valid),
   // .o_resp_tag    (w_l2_resp_tag  ),
   // .o_resp_data   (w_l2_resp_data ),
   // .i_resp_ready  (w_l2_resp_ready)

   .i_req_valid   (w_elf_req_valid  ),
   .i_req_cmd     (w_elf_req_cmd    ),
   .i_req_addr    (w_elf_req_addr   ),
   .i_req_tag     (w_elf_req_tag    ),
   .i_req_data    (w_elf_req_data   ),
   .i_req_byte_en (w_elf_req_byte_en),
   .o_req_ready   (w_elf_req_ready  ),

   .o_resp_valid  (  ),
   .o_resp_tag    (  ),
   .o_resp_data   (  ),
   .i_resp_ready  (1'b1)

   );


tb_elf_loader
u_tb_elf_loader
  (
   .i_clk     (i_clk    ),
   .i_reset_n (i_reset_n),

   // L2 request from ELF Loader
   .o_req_valid   (w_elf_req_valid ),
   .o_req_cmd     (w_elf_req_cmd   ),
   .o_req_addr    (w_elf_req_addr  ),
   .o_req_tag     (w_elf_req_tag   ),
   .o_req_data    (w_elf_req_data  ),
   .o_req_byte_en (w_elf_req_byte_en),
   .i_req_ready   (w_elf_req_ready )
   );


endmodule // mrh_tb
