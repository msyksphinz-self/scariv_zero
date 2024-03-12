// import "DPI-C" function load_binary
// (
//  input string path_exec,
//  input string filename,
//  input logic is_load_dump
// );


import "DPI-C" function void step_spike
  (
   input longint rtl_time,
   input longint rtl_pc,
   input int     rtl_priv,
   input longint rtl_mstatus,
   input int     rtl_exception,
   input int     rtl_exception_cause,
   input int     rtl_cmt_id,
   input int     rtl_grp_id,
   input int     rtl_insn,
   input int     rtl_wr_valid,
   input int     rtl_wr_typ,
   input int     rtl_wr_gpr,
   input int     rtl_wr_rnid,
   input longint rtl_wr_val,
   input byte    rtl_wr_vec_val0[riscv_vec_conf_pkg::VLEN_W/8],
   input byte    rtl_wr_vec_val1[riscv_vec_conf_pkg::VLEN_W/8],
   input byte    rtl_wr_vec_val2[riscv_vec_conf_pkg::VLEN_W/8],
   input byte    rtl_wr_vec_val3[riscv_vec_conf_pkg::VLEN_W/8],
   input byte    rtl_wr_vec_val4[riscv_vec_conf_pkg::VLEN_W/8],
   input byte    rtl_wr_vec_val5[riscv_vec_conf_pkg::VLEN_W/8],
   input byte    rtl_wr_vec_val6[riscv_vec_conf_pkg::VLEN_W/8],
   input byte    rtl_wr_vec_val7[riscv_vec_conf_pkg::VLEN_W/8]
   );

import "DPI-C" function void step_spike_wo_cmp(input int count);

import "DPI-C" function void stop_sim_deadlock(input int count);

import "DPI-C" function void initial_gshare(input longint bhr_length,
                                            input longint cache_block_byte_size);
import "DPI-C" function void step_gshare (input longint rtl_time,
                                          input int     rtl_cmt_id,
                                          input int     rtl_grp_id,
                                          input longint rtl_gshare_bhr);

import "DPI-C" function void initial_ras(input longint ras_length);
import "DPI-C" function void step_ras (input longint rtl_time,
                                       input int     rtl_cmt_id,
                                       input int     rtl_grp_id,
                                       input longint rtl_ras_index,
                                       input longint rtl_ras_addr);

module scariv_tb (
    input logic i_clk,

    input logic i_elf_loader_reset_n,
    input logic i_scariv_reset_n,

    input logic i_ram_reset_n
);

localparam TAG_W = scariv_lsu_pkg::L2_CMD_TAG_W + 2;
typedef logic [TAG_W-1: 0] tag_t;

/* from ELF Loader */
logic                     w_elf_req_valid;
scariv_lsu_pkg::mem_cmd_t w_elf_req_cmd;
scariv_pkg::paddr_t       w_elf_req_addr;
tag_t                     w_elf_req_tag;
scariv_lsu_pkg::dc_data_t w_elf_req_data;
scariv_lsu_pkg::dc_strb_t w_elf_req_byte_en;
logic                     w_elf_req_ready;

/* from Frontend IC */
logic                     w_ss_req_valid;
scariv_lsu_pkg::mem_cmd_t w_ss_req_cmd;
scariv_pkg::paddr_t       w_ss_req_addr;
tag_t                     w_ss_req_tag;
scariv_lsu_pkg::dc_data_t w_ss_req_data;
scariv_lsu_pkg::dc_strb_t w_ss_req_byte_en;
logic                     w_ss_req_ready;

logic                     w_ss_resp_valid;
tag_t                     w_ss_resp_tag;
scariv_lsu_pkg::dc_data_t w_ss_resp_data;
logic                     w_ss_resp_ready;

/* L1D Interface */
logic                     w_l1d_req_valid;
scariv_lsu_pkg::mem_cmd_t w_l1d_req_cmd;
scariv_pkg::paddr_t       w_l1d_req_addr;
tag_t                     w_l1d_req_tag;
scariv_lsu_pkg::dc_data_t w_l1d_req_data;
scariv_lsu_pkg::dc_strb_t w_l1d_req_byte_en;
logic                     w_l1d_req_ready;

logic                     w_l1d_resp_valid;
tag_t                     w_l1d_resp_tag;
scariv_lsu_pkg::dc_data_t w_l1d_resp_data;
logic                     w_l1d_resp_ready;

/* PTW Interface */
logic                     w_ptw_req_valid;
scariv_lsu_pkg::mem_cmd_t w_ptw_req_cmd;
scariv_pkg::paddr_t       w_ptw_req_addr;
tag_t                     w_ptw_req_tag;
scariv_lsu_pkg::dc_data_t w_ptw_req_data;
scariv_lsu_pkg::dc_strb_t w_ptw_req_byte_en;
logic                     w_ptw_req_ready;

logic                     w_ptw_resp_valid;
tag_t                     w_ptw_resp_tag;
scariv_lsu_pkg::dc_data_t w_ptw_resp_data;
logic                     w_ptw_resp_ready;

// Snoop Interface
logic                     w_snoop_req_valid;
scariv_pkg::paddr_t       w_snoop_req_paddr;

logic                     w_snoop_resp_valid;
scariv_lsu_pkg::dc_data_t w_snoop_resp_data;
scariv_lsu_pkg::dc_strb_t w_snoop_resp_be;

/* Middle Interface */
logic                     w_mid_req_valid;
scariv_lsu_pkg::mem_cmd_t w_mid_req_cmd;
scariv_pkg::paddr_t       w_mid_req_addr;
tag_t                     w_mid_req_tag;
scariv_lsu_pkg::dc_data_t w_mid_req_data;
scariv_lsu_pkg::dc_strb_t w_mid_req_byte_en;
logic                     w_mid_req_ready;

logic                     w_mid_resp_valid;
tag_t                     w_mid_resp_tag;
scariv_lsu_pkg::dc_data_t w_mid_resp_data;
logic                     w_mid_resp_ready;

/* BootROM Interface */
logic                     w_bootrom_req_valid;
scariv_lsu_pkg::mem_cmd_t w_bootrom_req_cmd;
scariv_pkg::paddr_t       w_bootrom_req_addr;
tag_t                     w_bootrom_req_tag;
scariv_lsu_pkg::dc_data_t w_bootrom_req_data;
scariv_lsu_pkg::dc_strb_t w_bootrom_req_byte_en;
logic                     w_bootrom_req_ready;

logic                     w_bootrom_resp_valid;
tag_t                     w_bootrom_resp_tag;
scariv_lsu_pkg::dc_data_t w_bootrom_resp_data;
logic                     w_bootrom_resp_ready;

/* Serial Interface */
logic                     w_serial_req_valid;
scariv_lsu_pkg::mem_cmd_t w_serial_req_cmd;
scariv_pkg::paddr_t       w_serial_req_addr;
tag_t                     w_serial_req_tag;
scariv_lsu_pkg::dc_data_t w_serial_req_data;
scariv_lsu_pkg::dc_strb_t w_serial_req_byte_en;
logic                     w_serial_req_ready;

logic                     w_serial_resp_valid;
tag_t                     w_serial_resp_tag;
scariv_lsu_pkg::dc_data_t w_serial_resp_data;
logic                     w_serial_resp_ready;

/* Kernel Boot Flash Interface */
logic                     w_kernel_req_valid;
scariv_lsu_pkg::mem_cmd_t w_kernel_req_cmd;
scariv_pkg::paddr_t       w_kernel_req_addr;
tag_t                     w_kernel_req_tag;
scariv_lsu_pkg::dc_data_t w_kernel_req_data;
scariv_lsu_pkg::dc_strb_t w_kernel_req_byte_en;
logic                     w_kernel_req_ready;

logic                     w_kernel_resp_valid;
tag_t                     w_kernel_resp_tag;
scariv_lsu_pkg::dc_data_t w_kernel_resp_data;
logic                     w_kernel_resp_ready;

/* initrd Boot Flash Interface */
logic                     w_initrd_req_valid;
scariv_lsu_pkg::mem_cmd_t w_initrd_req_cmd;
scariv_pkg::paddr_t       w_initrd_req_addr;
tag_t                     w_initrd_req_tag;
scariv_lsu_pkg::dc_data_t w_initrd_req_data;
scariv_lsu_pkg::dc_strb_t w_initrd_req_byte_en;
logic                     w_initrd_req_ready;

logic                     w_initrd_resp_valid;
tag_t                     w_initrd_resp_tag;
scariv_lsu_pkg::dc_data_t w_initrd_resp_data;
logic                     w_initrd_resp_ready;

/* L2 Interface */
logic                     w_l2_req_valid;
scariv_lsu_pkg::mem_cmd_t w_l2_req_cmd;
scariv_pkg::paddr_t       w_l2_req_addr;
tag_t                     w_l2_req_tag;
scariv_lsu_pkg::dc_data_t w_l2_req_data;
scariv_lsu_pkg::dc_strb_t w_l2_req_byte_en;
logic                     w_l2_req_ready;

logic                     w_l2_resp_valid;
tag_t                     w_l2_resp_tag;
scariv_lsu_pkg::dc_data_t w_l2_resp_data;
logic                     w_l2_resp_ready;

/* Connection */
l2c_arbiter_wrapper
  #(.TAG_W(scariv_lsu_pkg::L2_CMD_TAG_W + 2))
u_l2c_arbiter_wrapper
(
 /* from ELF Loader */
 .i_elf_req_valid  (w_elf_req_valid),
 .i_elf_req_cmd    (w_elf_req_cmd),
 .i_elf_req_addr   (w_elf_req_addr),
 .i_elf_req_tag    (w_elf_req_tag),
 .i_elf_req_data   (w_elf_req_data),
 .i_elf_req_byte_en(w_elf_req_byte_en),
 .o_elf_req_ready  (w_elf_req_ready),

 /* from Frontend IC */
 .i_ss_req_valid  (w_ss_req_valid),
 .i_ss_req_cmd    (w_ss_req_cmd),
 .i_ss_req_addr   (w_ss_req_addr),
 .i_ss_req_tag    (w_ss_req_tag),
 .i_ss_req_data   (w_ss_req_data),
 .i_ss_req_byte_en(w_ss_req_byte_en),
 .o_ss_req_ready  (w_ss_req_ready),

 .o_ss_resp_valid(w_ss_resp_valid),
 .o_ss_resp_tag  (w_ss_resp_tag),
 .o_ss_resp_data (w_ss_resp_data),
 .i_ss_resp_ready(w_ss_resp_ready),

 /* Middle Interface */
 .o_l2_req_valid  (w_mid_req_valid   ),
 .o_l2_req_cmd    (w_mid_req_cmd     ),
 .o_l2_req_addr   (w_mid_req_addr    ),
 .o_l2_req_tag    (w_mid_req_tag     ),
 .o_l2_req_data   (w_mid_req_data    ),
 .o_l2_req_byte_en(w_mid_req_byte_en ),
 .i_l2_req_ready  (w_mid_req_ready   ),

 .i_l2_resp_valid (w_mid_resp_valid  ),
 .i_l2_resp_tag   (w_mid_resp_tag    ),
 .i_l2_resp_data  (w_mid_resp_data   ),
 .o_l2_resp_ready (w_mid_resp_ready  )
 );

l2c_splitter_wrapper
  #(.TAG_W(scariv_lsu_pkg::L2_CMD_TAG_W + 2))
u_l2c_splitter_wrapper
  (
   /* L2 Interface */
   .i_req_valid  (w_mid_req_valid   ),
   .i_req_cmd    (w_mid_req_cmd     ),
   .i_req_addr   (w_mid_req_addr    ),
   .i_req_tag    (w_mid_req_tag     ),
   .i_req_data   (w_mid_req_data    ),
   .i_req_byte_en(w_mid_req_byte_en ),
   .o_req_ready  (w_mid_req_ready   ),

   .o_resp_valid (w_mid_resp_valid  ),
   .o_resp_tag   (w_mid_resp_tag    ),
   .o_resp_data  (w_mid_resp_data   ),
   .i_resp_ready (w_mid_resp_ready  ),

   /* BootROM Interface */
   .o_bootrom_req_valid  (w_bootrom_req_valid   ),
   .o_bootrom_req_cmd    (w_bootrom_req_cmd     ),
   .o_bootrom_req_addr   (w_bootrom_req_addr    ),
   .o_bootrom_req_tag    (w_bootrom_req_tag     ),
   .o_bootrom_req_data   (w_bootrom_req_data    ),
   .o_bootrom_req_byte_en(w_bootrom_req_byte_en ),
   .i_bootrom_req_ready  (w_bootrom_req_ready   ),

   .i_bootrom_resp_valid (w_bootrom_resp_valid  ),
   .i_bootrom_resp_tag   (w_bootrom_resp_tag    ),
   .i_bootrom_resp_data  (w_bootrom_resp_data   ),
   .o_bootrom_resp_ready (w_bootrom_resp_ready  ),

   /* Serial Interface */
   .o_serial_req_valid  (w_serial_req_valid   ),
   .o_serial_req_cmd    (w_serial_req_cmd     ),
   .o_serial_req_addr   (w_serial_req_addr    ),
   .o_serial_req_tag    (w_serial_req_tag     ),
   .o_serial_req_data   (w_serial_req_data    ),
   .o_serial_req_byte_en(w_serial_req_byte_en ),
   .i_serial_req_ready  (w_serial_req_ready   ),

   .i_serial_resp_valid (w_serial_resp_valid  ),
   .i_serial_resp_tag   (w_serial_resp_tag    ),
   .i_serial_resp_data  (w_serial_resp_data   ),
   .o_serial_resp_ready (w_serial_resp_ready  ),

   /* Kernel Flash Interface */
   .o_kernel_req_valid   (w_kernel_req_valid   ),
   .o_kernel_req_cmd     (w_kernel_req_cmd     ),
   .o_kernel_req_addr    (w_kernel_req_addr    ),
   .o_kernel_req_tag     (w_kernel_req_tag     ),
   .o_kernel_req_data    (w_kernel_req_data    ),
   .o_kernel_req_byte_en (w_kernel_req_byte_en ),
   .i_kernel_req_ready   (w_kernel_req_ready   ),

   .i_kernel_resp_valid (w_kernel_resp_valid  ),
   .i_kernel_resp_tag   (w_kernel_resp_tag    ),
   .i_kernel_resp_data  (w_kernel_resp_data   ),
   .o_kernel_resp_ready (w_kernel_resp_ready  ),

   /* initrd Flash Interface */
   .o_initrd_req_valid   (w_initrd_req_valid   ),
   .o_initrd_req_cmd     (w_initrd_req_cmd     ),
   .o_initrd_req_addr    (w_initrd_req_addr    ),
   .o_initrd_req_tag     (w_initrd_req_tag     ),
   .o_initrd_req_data    (w_initrd_req_data    ),
   .o_initrd_req_byte_en (w_initrd_req_byte_en ),
   .i_initrd_req_ready   (w_initrd_req_ready   ),

   .i_initrd_resp_valid (w_initrd_resp_valid  ),
   .i_initrd_resp_tag   (w_initrd_resp_tag    ),
   .i_initrd_resp_data  (w_initrd_resp_data   ),
   .o_initrd_resp_ready (w_initrd_resp_ready  ),

   /* L2 Interface */
   .o_l2_req_valid  (w_l2_req_valid   ),
   .o_l2_req_cmd    (w_l2_req_cmd     ),
   .o_l2_req_addr   (w_l2_req_addr    ),
   .o_l2_req_tag    (w_l2_req_tag     ),
   .o_l2_req_data   (w_l2_req_data    ),
   .o_l2_req_byte_en(w_l2_req_byte_en ),
   .i_l2_req_ready  (w_l2_req_ready   ),

   .i_l2_resp_valid (w_l2_resp_valid  ),
   .i_l2_resp_tag   (w_l2_resp_tag    ),
   .i_l2_resp_data  (w_l2_resp_data   ),
   .o_l2_resp_ready (w_l2_resp_ready  )
   );

scariv_subsystem_wrapper
u_scariv_subsystem_wrapper
  (
   .i_clk    (i_clk),
   .i_reset_n(i_scariv_reset_n),

   // ICache Interconnection
   .o_l2_req_valid  (w_ss_req_valid),
   .o_l2_req_cmd    (w_ss_req_cmd),
   .o_l2_req_addr   (w_ss_req_addr),
   .o_l2_req_tag    (w_ss_req_tag),
   .o_l2_req_data   (w_ss_req_data),
   .o_l2_req_byte_en(w_ss_req_byte_en),
   .i_l2_req_ready  (w_ss_req_ready),

   .i_l2_resp_valid (w_ss_resp_valid),
   .i_l2_resp_tag   (w_ss_resp_tag),
   .i_l2_resp_data  (w_ss_resp_data),
   .o_l2_resp_ready (w_ss_resp_ready),

   // Snoop Interface
   .i_snoop_req_valid(w_snoop_req_valid),
   .i_snoop_req_paddr(w_snoop_req_paddr),

   .o_snoop_resp_valid(w_snoop_resp_valid),
   .o_snoop_resp_data (w_snoop_resp_data),
   .o_snoop_resp_be   (w_snoop_resp_be),

   .i_interrupts ('h0)
   );


tb_l2_behavior_ram
  #(
    .DATA_W   (scariv_conf_pkg::DCACHE_DATA_W),
    .TAG_W    (TAG_W),
    .ADDR_W   (riscv_pkg::PADDR_W),
    .BASE_ADDR('h8000_0000),
    .SIZE     ('h4000),
    .RD_LAT   (10)
    )
u_tb_l2_behavior_ram
  (
   .i_clk    (i_clk),
   .i_reset_n(i_ram_reset_n),

   // L2 request from ICache
   .i_req_valid  (w_l2_req_valid),
   .i_req_cmd    (w_l2_req_cmd),
   .i_req_addr   (w_l2_req_addr),
   .i_req_tag    (w_l2_req_tag),
   .i_req_data   (w_l2_req_data),
   .i_req_byte_en(w_l2_req_byte_en),
   .o_req_ready  (w_l2_req_ready),

   .o_resp_valid(w_l2_resp_valid),
   .o_resp_tag  (w_l2_resp_tag),
   .o_resp_data (w_l2_resp_data),
   .i_resp_ready(w_l2_resp_ready),

   // Snoop Interface
   .o_snoop_req_valid(w_snoop_req_valid),
   .o_snoop_req_paddr(w_snoop_req_paddr),

   .i_snoop_resp_valid(w_snoop_resp_valid),
   .i_snoop_resp_data (w_snoop_resp_data),
   .i_snoop_resp_be   (w_snoop_resp_be)
   );

// BootROM
scariv_bootrom
#(
  .DATA_W   (scariv_conf_pkg::DCACHE_DATA_W),
  .TAG_W    (TAG_W),
  .ADDR_W   (riscv_pkg::PADDR_W),
  .BASE_ADDR('h1000),
  .SIZE     ('h4000),
  .RD_LAT   (10)
) u_scariv_bootrom (
  .i_clk    (i_clk),
  .i_reset_n(i_ram_reset_n),

  // L2 request from ICache
  .i_req_valid   (w_bootrom_req_valid   ),
  .i_req_cmd     (w_bootrom_req_cmd     ),
  .i_req_addr    (w_bootrom_req_addr    ),
  .i_req_tag     (w_bootrom_req_tag     ),
  .i_req_data    (w_bootrom_req_data    ),
  .i_req_byte_en (w_bootrom_req_byte_en ),
  .o_req_ready   (w_bootrom_req_ready   ),

  .o_resp_valid  (w_bootrom_resp_valid  ),
  .o_resp_tag    (w_bootrom_resp_tag    ),
  .o_resp_data   (w_bootrom_resp_data   ),
  .i_resp_ready  (w_bootrom_resp_ready  )
);


// Serial
scariv_serialdevice
#(
  .DATA_W   (scariv_conf_pkg::DCACHE_DATA_W),
  .TAG_W    (TAG_W),
  .ADDR_W   (riscv_pkg::PADDR_W),
  .BASE_ADDR('h5400_0000),
  .SIZE     ('h1000),
  .RD_LAT   (10)
) u_scariv_serialdevice (
  .i_clk    (i_clk),
  .i_reset_n(i_ram_reset_n),

  // Serial request from ICache
  .i_req_valid   (w_serial_req_valid   ),
  .i_req_cmd     (w_serial_req_cmd     ),
  .i_req_addr    (w_serial_req_addr    ),
  .i_req_tag     (w_serial_req_tag     ),
  .i_req_data    (w_serial_req_data    ),
  .i_req_byte_en (w_serial_req_byte_en ),
  .o_req_ready   (w_serial_req_ready   ),

  .o_resp_valid  (w_serial_resp_valid  ),
  .o_resp_tag    (w_serial_resp_tag    ),
  .o_resp_data   (w_serial_resp_data   ),
  .i_resp_ready  (w_serial_resp_ready  )
);


// Kernel Flash
tb_flash
#(
  .FILE     ("image"),
  .DATA_W   (scariv_conf_pkg::DCACHE_DATA_W),
  .TAG_W    (TAG_W),
  .ADDR_W   (riscv_pkg::PADDR_W),
  .BASE_ADDR('h8020_0000),
  .SIZE     ('h0200_0000),
  .RD_LAT   (30)
) u_kernel_flash (
  .i_clk    (i_clk),
  .i_reset_n(i_ram_reset_n),

  // L2 request from ICache
  .i_req_valid   (w_kernel_req_valid   ),
  .i_req_cmd     (w_kernel_req_cmd     ),
  .i_req_addr    (w_kernel_req_addr    ),
  .i_req_tag     (w_kernel_req_tag     ),
  .i_req_data    (w_kernel_req_data    ),
  .i_req_byte_en (w_kernel_req_byte_en ),
  .o_req_ready   (w_kernel_req_ready   ),

  .o_resp_valid  (w_kernel_resp_valid  ),
  .o_resp_tag    (w_kernel_resp_tag    ),
  .o_resp_data   (w_kernel_resp_data   ),
  .i_resp_ready  (w_kernel_resp_ready  )
);


// initrd Flash
tb_flash
#(
  .FILE     ("initrd"),
  .DATA_W   (scariv_conf_pkg::DCACHE_DATA_W),
  .TAG_W    (TAG_W),
  .ADDR_W   (riscv_pkg::PADDR_W),
  .BASE_ADDR('hffc8_4a00),
  .SIZE     ('h0200_0000),
  .RD_LAT   (30)
) u_initrd_flash (
  .i_clk    (i_clk),
  .i_reset_n(i_ram_reset_n),

  // L2 request from ICache
  .i_req_valid   (w_initrd_req_valid   ),
  .i_req_cmd     (w_initrd_req_cmd     ),
  .i_req_addr    (w_initrd_req_addr    ),
  .i_req_tag     (w_initrd_req_tag     ),
  .i_req_data    (w_initrd_req_data    ),
  .i_req_byte_en (w_initrd_req_byte_en ),
  .o_req_ready   (w_initrd_req_ready   ),

  .o_resp_valid  (w_initrd_resp_valid  ),
  .o_resp_tag    (w_initrd_resp_tag    ),
  .o_resp_data   (w_initrd_resp_data   ),
  .i_resp_ready  (w_initrd_resp_ready  )
);


tb_elf_loader u_tb_elf_loader (
    .i_clk    (i_clk),
    .i_reset_n(i_elf_loader_reset_n),

    // L2 request from ELF Loader
    .o_req_valid  (w_elf_req_valid),
    .o_req_cmd    (w_elf_req_cmd),
    .o_req_addr   (w_elf_req_addr),
    .o_req_tag    (w_elf_req_tag),
    .o_req_data   (w_elf_req_data),
    .o_req_byte_en(w_elf_req_byte_en),
    .i_req_ready  (w_elf_req_ready)
);


`include "tb_commit_mon_utils.sv"

logic [63: 0]                                                  cycle_counter;
localparam cycle_interval = 1000;
logic [63: 0]                                                  total_commit_counter;
logic [63: 0]                                                  int_commit_counter;

`define BRANCH_INFO_Q u_scariv_subsystem_wrapper.u_scariv_subsystem.u_tile.u_frontend.u_predictor.u_gshare.branch_info_queue
`define ROB u_scariv_subsystem_wrapper.u_scariv_subsystem.u_tile.u_rob

byte w_physical_vec_data_rnid[scariv_pkg::DISP_SIZE-1: 0][8][riscv_vec_conf_pkg::VLEN_W/8-1: 0];

generate if (riscv_vec_conf_pkg::VLEN_W != 0) begin : vpu
  for (genvar grp_idx = 0; grp_idx < scariv_pkg::DISP_SIZE; grp_idx++) begin
    for (genvar lmul_idx = 0; lmul_idx < 8; lmul_idx++) begin
      for (genvar idx = 0; idx < riscv_vec_conf_pkg::VLEN_W/8; idx++) begin : array_loop
        assign w_physical_vec_data_rnid[grp_idx][lmul_idx][idx] = w_physical_vec_data[committed_rob_payload.disp[grp_idx].wr_reg.rnid + lmul_idx][idx*8 +: 8];
      end
    end
  end
end endgenerate

always_ff @(negedge i_clk, negedge i_scariv_reset_n) begin
    if (!i_scariv_reset_n) begin
    end else begin
      if (`ROB.w_out_valid) begin
        for (int grp_idx = 0; grp_idx < scariv_pkg::DISP_SIZE; grp_idx++) begin
          if (`ROB.w_commit.grp_id[grp_idx] &
              ~`ROB.w_commit.dead_id[grp_idx]) begin
            /* verilator lint_off WIDTH */
            step_spike ($time / 4, longint'(committed_rob_payload.disp[grp_idx].pc_addr),
                        int'(u_scariv_subsystem_wrapper.u_scariv_subsystem.u_tile.u_csu.u_scariv_csr.r_priv),
                        `ROB.w_sim_mstatus[`ROB.w_out_cmt_entry_id][grp_idx],
                        // Exception selection
                        (`ROB.w_commit.cmt_id == `ROB.r_rob_except.cmt_id) & |((1 << grp_idx) & `ROB.r_rob_except.grp_id) ? `ROB.r_rob_except.valid : 1'b0,
                        `ROB.r_rob_except.typ,
                        `ROB.w_out_cmt_id,
                        1 << grp_idx,
                        committed_rob_payload.disp[grp_idx].rvc_inst_valid ? committed_rob_payload.disp[grp_idx].rvc_inst : committed_rob_payload.disp[grp_idx].inst,
                        committed_rob_payload.disp[grp_idx].wr_reg.valid,
                        committed_rob_payload.disp[grp_idx].wr_reg.typ,
                        committed_rob_payload.disp[grp_idx].wr_reg.regidx,
                        committed_rob_payload.disp[grp_idx].wr_reg.rnid,
                        committed_rob_payload.disp[grp_idx].wr_reg.typ == scariv_pkg::GPR ?
                        w_physical_int_data[committed_rob_payload.disp[grp_idx].wr_reg.rnid] :
                        w_physical_fp_data [committed_rob_payload.disp[grp_idx].wr_reg.rnid],
                        w_physical_vec_data_rnid[grp_idx][0], w_physical_vec_data_rnid[grp_idx][1], w_physical_vec_data_rnid[grp_idx][2], w_physical_vec_data_rnid[grp_idx][3],
                        w_physical_vec_data_rnid[grp_idx][4], w_physical_vec_data_rnid[grp_idx][5], w_physical_vec_data_rnid[grp_idx][6], w_physical_vec_data_rnid[grp_idx][7]
                        );

            for (int q_idx = 0; q_idx < `BRANCH_INFO_Q.size(); q_idx++) begin
              if (`BRANCH_INFO_Q[q_idx].cmt_id == `ROB.w_out_cmt_id &&
                  `BRANCH_INFO_Q[q_idx].grp_id == 1 << grp_idx) begin
                step_gshare ($time,
                             `BRANCH_INFO_Q[q_idx].cmt_id,
                             `BRANCH_INFO_Q[q_idx].grp_id,
                             `BRANCH_INFO_Q[q_idx].gshare_bht);
                if (`BRANCH_INFO_Q[q_idx].mispredict) begin
                  for (int q_idx_tmp = 0; q_idx_tmp <= q_idx; q_idx_tmp++) begin
                    `BRANCH_INFO_Q.pop_front();
                  end
                end else begin
                  `BRANCH_INFO_Q.delete(q_idx);
                end
                break;
              end // if (`BRANCH_INFO_Q[q_idx].cmt_id == `ROB.w_out_cmt_id &&...
            end // for (int q_idx = 0; q_idx < `BRANCH_INFO_Q.size(); q_idx++)

            // RAS check
            // step_ras ($time,
            //           `ROB.w_out_cmt_id,
            //           1 << grp_idx,
            //           `ROB.w_out_entry.br_upd_info.sim_ras_index,
            //           `ROB.w_out_entry.br_upd_info.sim_pred_vaddr);
          end // if (`ROB.w_commit.grp_id[grp_idx] &...
        end  // for (int grp_idx = 0; grp_idx < scariv_pkg::DISP_SIZE; grp_idx++)
      end  // if (`ROB.w_out_valid)

      // Counting up instruction
      cycle_counter <= cycle_counter + 1;
      if (`ROB.w_out_valid) begin
        total_commit_counter <= total_commit_counter + $countones(`ROB.w_commit.grp_id &
                                                     ~`ROB.w_commit.dead_id);
        int_commit_counter <= int_commit_counter + $countones(`ROB.w_commit.grp_id &
                                                              ~`ROB.w_commit.dead_id);
      end
      if (((cycle_counter % cycle_interval) == 0) && (cycle_counter != 0)) begin
        $display ("%10d : %10d : IPC(recent) = %0.02f, IPC(total) = %0.02f",
                  cycle_counter,
                  total_commit_counter,
                  real'(int_commit_counter) / cycle_interval,
                  real'(total_commit_counter) / real'(cycle_counter));
        int_commit_counter <= 'h0;
      end
    end  // else: !if(!i_scariv_reset_n)
  end  // always_ff @ (negedge i_clk, negedge i_scariv_reset_n)



  logic w_clk;
  logic w_scariv_reset_n;
  assign w_clk = i_clk;
  assign w_scariv_reset_n = i_scariv_reset_n;

  `include "tb_json_dumper.sv"
  `include "tb_json_perf_dumper.sv"

  `include "tb_ooo_dumper.sv"

`ifdef NEVER
// ------------------------------
// Instruction Cache Checker
// ------------------------------
logic [riscv_pkg::PADDR_W-1: $clog2(scariv_lsu_pkg::ICACHE_DATA_B_W)] ram_addr;
assign ram_addr = u_scariv_subsystem_wrapper.u_scariv_subsystem.u_tile.u_frontend.r_s2_paddr[riscv_pkg::PADDR_W-1: $clog2(scariv_lsu_pkg::ICACHE_DATA_B_W)];

always_ff @(negedge i_clk, negedge i_scariv_reset_n) begin
  if (i_scariv_reset_n) begin
    if (u_scariv_subsystem_wrapper.u_scariv_subsystem.u_tile.u_frontend.u_scariv_icache.o_s2_resp.valid &
        ~u_scariv_subsystem_wrapper.u_scariv_subsystem.u_tile.u_frontend.r_s2_tlb_miss) begin
      if (u_tb_l2_behavior_ram.ram[ram_addr] != u_scariv_subsystem_wrapper.u_scariv_subsystem.u_tile.u_frontend.u_scariv_icache.o_s2_resp.data) begin
        $fatal(0, "Fetched data from ICache and External L2 data is different.\n Addr = %x\n  Fetch = %x\n  Data  = %x\n",
               u_scariv_subsystem_wrapper.u_scariv_subsystem.u_tile.u_frontend.r_s2_paddr,
               u_scariv_subsystem_wrapper.u_scariv_subsystem.u_tile.u_frontend.u_scariv_icache.o_s2_resp.data,
               u_tb_l2_behavior_ram.ram[ram_addr]);
      end
    end
  end // else: !if(!i_scariv_reset_n)
end // always_ff @ (negedge i_clk, negedge i_scariv_reset_n)
`endif //  `ifdef NEVER

initial begin
  initial_gshare (scariv_conf_pkg::GSHARE_BHT_W,
                  scariv_lsu_pkg::ICACHE_DATA_B_W);
  initial_ras (scariv_conf_pkg::RAS_ENTRY_SIZE);
end

endmodule  // scariv_tb
