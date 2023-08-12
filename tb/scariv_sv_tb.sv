`ifndef DIRECT_LOAD_HEX
import "DPI-C" function load_binary
(
 input string path_exec,
 input string filename,
 input logic is_load_dump
);

import "DPI-C" function open_log_fp
(
 input string filename
 );

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
   input longint rtl_wr_val
   );

import "DPI-C" function void step_spike_wo_cmp(input int count);

import "DPI-C" function void stop_sim_deadlock(input int count);

`endif // DIRECT_LOAD_HEX


module tb;

export "DPI-C" task stop_sim;

task stop_sim;
  $finish;
endtask // stop_sim

localparam TAG_W = scariv_lsu_pkg::L2_CMD_TAG_W + 2;
typedef logic [TAG_W-1: 0] tag_t;

logic w_clk;
logic w_elf_loader_reset_n;
logic w_scariv_reset_n;
logic w_ram_reset_n;

logic w_timeout;

logic w_terminate;
assign w_terminate = w_timeout;

/* from Frontend IC */
logic                     w_ss_req_valid;
scariv_lsu_pkg::mem_cmd_t w_ss_req_cmd;
scariv_pkg::paddr_t       w_ss_req_addr;
tag_t                     w_ss_req_tag;
scariv_pkg::ic_data_t     w_ss_req_data;
scariv_pkg::ic_strb_t     w_ss_req_byte_en;
logic                     w_ss_req_ready;

logic                     w_ss_resp_valid;
tag_t                     w_ss_resp_tag;
scariv_pkg::ic_data_t     w_ss_resp_data;
logic                     w_ss_resp_ready;

/* from ELF Loader */
logic                                     w_elf_req_valid;
scariv_lsu_pkg::mem_cmd_t                   w_elf_req_cmd;
logic [riscv_pkg::PADDR_W-1:0]            w_elf_req_addr;
logic [scariv_lsu_pkg::L2_CMD_TAG_W-1:0]    w_elf_req_tag;
logic [scariv_conf_pkg::ICACHE_DATA_W-1:0]   w_elf_req_data;
logic [scariv_conf_pkg::ICACHE_DATA_W/8-1:0] w_elf_req_byte_en;
logic                                     w_elf_req_ready;

/* L1D Interface */
logic                                     w_l1d_req_valid;
scariv_lsu_pkg::mem_cmd_t                   w_l1d_req_cmd;
logic [riscv_pkg::PADDR_W-1:0]            w_l1d_req_addr;
logic [scariv_lsu_pkg::L2_CMD_TAG_W-1:0]    w_l1d_req_tag;
logic [scariv_conf_pkg::ICACHE_DATA_W-1:0]   w_l1d_req_data;
logic [scariv_conf_pkg::ICACHE_DATA_W/8-1:0] w_l1d_req_byte_en;
logic                                     w_l1d_req_ready;

logic                                     w_l1d_resp_valid;
logic [scariv_lsu_pkg::L2_CMD_TAG_W-1:0]    w_l1d_resp_tag;
logic [scariv_conf_pkg::ICACHE_DATA_W-1:0]   w_l1d_resp_data;
logic                                     w_l1d_resp_ready;

/* PTW Interface */
logic                                     w_ptw_req_valid;
scariv_lsu_pkg::mem_cmd_t                   w_ptw_req_cmd;
logic [riscv_pkg::PADDR_W-1:0]            w_ptw_req_addr;
logic [scariv_lsu_pkg::L2_CMD_TAG_W-1:0]    w_ptw_req_tag;
logic [scariv_conf_pkg::ICACHE_DATA_W-1:0]   w_ptw_req_data;
logic [scariv_conf_pkg::ICACHE_DATA_W/8-1:0] w_ptw_req_byte_en;
logic                                     w_ptw_req_ready;

logic                                     w_ptw_resp_valid;
logic [scariv_lsu_pkg::L2_CMD_TAG_W-1:0]    w_ptw_resp_tag;
logic [scariv_conf_pkg::ICACHE_DATA_W-1:0]   w_ptw_resp_data;
logic                                     w_ptw_resp_ready;

/* L2 Interface */
logic                                     w_l2_req_valid;
scariv_lsu_pkg::mem_cmd_t                   w_l2_req_cmd;
logic [riscv_pkg::PADDR_W-1:0]            w_l2_req_addr;
logic [scariv_lsu_pkg::L2_CMD_TAG_W-1:0]    w_l2_req_tag;
logic [scariv_conf_pkg::ICACHE_DATA_W-1:0]   w_l2_req_data;
logic [scariv_conf_pkg::ICACHE_DATA_W/8-1:0] w_l2_req_byte_en;
logic                                     w_l2_req_ready;

logic                                     w_l2_resp_valid;
logic [scariv_lsu_pkg::L2_CMD_TAG_W-1:0]    w_l2_resp_tag;
logic [scariv_conf_pkg::ICACHE_DATA_W-1:0]   w_l2_resp_data;
logic                                     w_l2_resp_ready;

// Snoop Interface
logic                                     w_snoop_req_valid;
logic [            riscv_pkg::PADDR_W-1:0] w_snoop_req_paddr;

logic                                      w_snoop_resp_valid;
logic [  scariv_conf_pkg::DCACHE_DATA_W-1:0] w_snoop_resp_data;
logic [ scariv_lsu_pkg::DCACHE_DATA_B_W-1:0] w_snoop_resp_be;


/* Connection */
l2c_arbiter_wrapper
u_l2c_arbiter_wrapper
  (
   /* from ELF Loader */
   .i_elf_req_valid   (w_elf_req_valid  ),
   .i_elf_req_cmd     (w_elf_req_cmd    ),
   .i_elf_req_addr    (w_elf_req_addr   ),
   .i_elf_req_tag     (w_elf_req_tag    ),
   .i_elf_req_data    (w_elf_req_data   ),
   .i_elf_req_byte_en (w_elf_req_byte_en),
   .o_elf_req_ready   (w_elf_req_ready  ),

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


   /* L2 Interface */
   .o_l2_req_valid    (w_mid_req_valid  ),
   .o_l2_req_cmd      (w_mid_req_cmd    ),
   .o_l2_req_addr     (w_mid_req_addr   ),
   .o_l2_req_tag      (w_mid_req_tag    ),
   .o_l2_req_data     (w_mid_req_data   ),
   .o_l2_req_byte_en  (w_mid_req_byte_en),
   .i_l2_req_ready    (w_mid_req_ready  ),

   .i_l2_resp_valid   (w_mid_resp_valid ),
   .i_l2_resp_tag     (w_mid_resp_tag   ),
   .i_l2_resp_data    (w_mid_resp_data  ),
   .o_l2_resp_ready   (w_mid_resp_ready )
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
    .DATA_W    (scariv_conf_pkg::ICACHE_DATA_W),
    .TAG_W     (scariv_lsu_pkg::L2_CMD_TAG_W),
    .ADDR_W    (riscv_pkg::PADDR_W),
    .BASE_ADDR ('h8000_0000),
    .SIZE      (4096),
    .RD_LAT    (10)
    )
u_tb_l2_behavior_ram
  (
   .i_clk     (w_clk        ),
   .i_reset_n (w_ram_reset_n),

   // L2 request from ICache
   .i_req_valid   (w_l2_req_valid  ),
   .i_req_cmd     (w_l2_req_cmd    ),
   .i_req_addr    (w_l2_req_addr   ),
   .i_req_tag     (w_l2_req_tag    ),
   .i_req_data    (w_l2_req_data   ),
   .i_req_byte_en (w_l2_req_byte_en),
   .o_req_ready   (w_l2_req_ready  ),

   .o_resp_valid  (w_l2_resp_valid),
   .o_resp_tag    (w_l2_resp_tag  ),
   .o_resp_data   (w_l2_resp_data ),
   .i_resp_ready  (w_l2_resp_ready),

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
  .DATA_W   (scariv_conf_pkg::ICACHE_DATA_W),
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
  .DATA_W   (scariv_conf_pkg::ICACHE_DATA_W),
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
  .DATA_W   (scariv_conf_pkg::ICACHE_DATA_W),
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
  .DATA_W   (scariv_conf_pkg::ICACHE_DATA_W),
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


`ifndef DIRECT_LOAD_HEX
tb_elf_loader
u_tb_elf_loader
  (
   .i_clk     (w_clk               ),
   .i_reset_n (w_elf_loader_reset_n),

   // L2 request from ELF Loader
   .o_req_valid   (w_elf_req_valid ),
   .o_req_cmd     (w_elf_req_cmd   ),
   .o_req_addr    (w_elf_req_addr  ),
   .o_req_tag     (w_elf_req_tag   ),
   .o_req_data    (w_elf_req_data  ),
   .o_req_byte_en (w_elf_req_byte_en),
   .i_req_ready   (w_elf_req_ready )
   );
`else // DIRECT_LOAD_HEX
assign w_elf_req_valid  = 1'b0;
assign w_elf_req_cmd    = scariv_lsu_pkg::M_XRD;
assign w_elf_req_addr   = 'h0;
assign w_elf_req_tag    = 'h0;
assign w_elf_req_data   = 'h0;
assign w_elf_req_byte_en = 'h0;
`endif // DIRECT_LOAD_HEX

localparam STEP = 1;
localparam TIMEOUT = 100000000;

initial begin
  w_clk = 1'b0;
  w_elf_loader_reset_n = 1'b0;
  w_scariv_reset_n        = 1'b0;
  w_ram_reset_n        = 1'b0;

  #(STEP * 100);

  w_elf_loader_reset_n = 1'b1;
  w_scariv_reset_n        = 1'b0;
  w_ram_reset_n        = 1'b1;

  #(STEP * 10000);

  w_elf_loader_reset_n = 1'b0;
  w_scariv_reset_n        = 1'b1;
  w_ram_reset_n        = 1'b1;

  #(STEP * TIMEOUT);
  w_timeout = 1'b1;
  $finish;
end

always #STEP begin
  w_clk = ~w_clk;
end

string filename;

initial begin
`ifdef DIRECT_LOAD_HEX
  if ($value$plusargs("HEX=%s", filename)) begin
    $display("Loading HEX file = %s", filename);
  end else begin
    $display("+HEX= is not specified");
    $finish(1);
  end

  $readmemh (filename, u_tb_l2_behavior_ram.ram);
`else // DIRECT_LOAD_HEX
  if ($value$plusargs("ELF=%s", filename)) begin
    $display("Loading ELF file = %s", filename);
  end else begin
    $display("+ELF= is not specified");
    $finish(1);
  end
  open_log_fp(filename);
  load_binary("", filename, 1'b1);
`endif // DIRECT_LOAD_HEX

end


`include "tb_commit_mon_utils.sv"

// `ifdef SIMULATION
//   `ifndef VERILATOR
//
// always_ff @ (negedge w_clk, negedge w_scariv_reset_n) begin
//   if (!w_scariv_reset_n) begin
//   end else begin
//     if (u_scariv_subsystem_wrapper.u_scariv_subsystem.u_tile.u_rob.o_commit.commit) begin
//       for (int grp_idx = 0; grp_idx < scariv_conf_pkg::DISP_SIZE; grp_idx++) begin
//         if (committed_rob_entry.grp_id[grp_idx] & (!w_dead_grp_id[grp_idx])) begin
//           $fwrite (log_fp, "%5t %5d PC=%010x (%02d,%02d) %08x ", $time,
//                    u_scariv_subsystem_wrapper.u_scariv_subsystem.u_tile.u_scariv_csu.u_scariv_csr.r_minstret,
//                    committed_rob_entry.inst[grp_idx].pc_addr,
//                    u_scariv_subsystem_wrapper.u_scariv_subsystem.u_tile.u_rob.w_out_cmt_id, 1 << grp_idx,
//                    committed_rob_entry.inst[grp_idx].inst);
//           if (committed_rob_entry.inst[grp_idx].rd_valid) begin
//             $fwrite (log_fp, "GPR[%02d](%03d)=%016x : ",
//                      committed_rob_entry.inst[grp_idx].rd_regidx,
//                      committed_rob_entry.inst[grp_idx].rd_rnid,
//                      w_physical_int_data[committed_rob_entry.inst[grp_idx].rd_rnid]);
//           end else begin
//             $fwrite (log_fp, "                              : ");
//           end
//           $fwrite(log_fp, "DASM(%08x)\n", committed_rob_entry.inst[grp_idx].inst);
//         end // if (committed_rob_entry.grp_id[grp_idx])
//       end // for (int grp_idx = 0; grp_idx < scariv_conf_pkg::DISP_SIZE; grp_idx++)
//     end // if (u_scariv_subsystem_wrapper.u_scariv_subsystem.u_tile.u_rob.w_entry_all_done[u_scariv_subsystem_wrapper.u_scariv_subsystem.u_tile.u_rob.w_out_cmd_id])
//   end
// end
//
//   `endif // SIMULATION
// `endif // VERILATOR

`ifdef DIRECT_LOAD_HEX

always_ff @(negedge w_clk, negedge w_scariv_reset_n) begin
  if (!w_scariv_reset_n) begin
  end else begin
    if (u_scariv_subsystem_wrapper.u_scariv_subsystem.u_tile.u_rob.o_commit.commit) begin
      for (int grp_idx = 0; grp_idx < scariv_conf_pkg::DISP_SIZE; grp_idx++) begin
        if (committed_rob_entry.grp_id[grp_idx]) begin
          $fwrite (pipe_fp, "(%02d,%02d) PC=%08x ",
                   u_scariv_subsystem_wrapper.u_scariv_subsystem.u_tile.u_rob.w_out_cmt_id, 1 << grp_idx,
                   (committed_rob_entry.pc_addr << 1) + (4 * grp_idx));
          if (committed_rob_entry.inst[grp_idx].rd_valid) begin
            $fwrite (pipe_fp, "GPR[%02d](%03d)=%016x : ",
                     committed_rob_entry.inst[grp_idx].rd_regidx,
                     committed_rob_entry.inst[grp_idx].rd_rnid,
                     w_physical_int_data[committed_rob_entry.inst[grp_idx].rd_rnid]);
          end else begin
            $fwrite (pipe_fp, "                                        : ");
          end
          $fwrite (pipe_fp, "DASM(%08x)", committed_rob_entry.inst[grp_idx].inst);
        end // if (committed_rob_entry.grp_id[grp_idx])
      end // for (int grp_idx = 0; grp_idx < scariv_conf_pkg::DISP_SIZE; grp_idx++)
    end // if (u_scariv_subsystem_wrapper.u_scariv_subsystem.u_tile.u_rob.w_entry_all_done[u_scariv_subsystem_wrapper.u_scariv_subsystem.u_tile.u_rob.w_out_cmd_id])
    $fwrite(pipe_fp, "\n");
  end // else: !if(!w_scariv_reset_n)
end // always_ff @ (negedge w_clk, negedge w_scariv_reset_n)

`else //  `ifndef DIRECT_LOAD_HEX

`include "tb_json_dumper.sv"
always_ff @(negedge w_clk, negedge w_scariv_reset_n) begin
  if (!w_scariv_reset_n) begin
  end else begin
    if (u_scariv_subsystem_wrapper.u_scariv_subsystem.u_tile.u_rob.o_commit.commit) begin
      for (int grp_idx = 0; grp_idx < scariv_conf_pkg::DISP_SIZE; grp_idx++) begin
        if (u_scariv_subsystem_wrapper.u_scariv_subsystem.u_tile.u_rob.o_commit.grp_id[grp_idx] &
            ~u_scariv_subsystem_wrapper.u_scariv_subsystem.u_tile.u_rob.o_commit.dead_id[grp_idx]) begin
          step_spike ($time / 4, longint'(committed_rob_entry.inst[grp_idx].pc_addr),
                      int'(u_scariv_subsystem_wrapper.u_scariv_subsystem.u_tile.u_scariv_csu.u_scariv_csr.r_priv),
                      u_scariv_subsystem_wrapper.u_scariv_subsystem.u_tile.u_rob.w_sim_mstatus[u_scariv_subsystem_wrapper.u_scariv_subsystem.u_tile.u_rob.w_out_cmt_entry_id][grp_idx],
                      u_scariv_subsystem_wrapper.u_scariv_subsystem.u_tile.u_rob.w_valid_except_grp_id[grp_idx],
                      u_scariv_subsystem_wrapper.u_scariv_subsystem.u_tile.u_rob.w_except_type_selected,
                      u_scariv_subsystem_wrapper.u_scariv_subsystem.u_tile.u_rob.w_out_cmt_id,
                      1 << grp_idx,
                      committed_rob_entry.inst[grp_idx].rvc_inst_valid ? committed_rob_entry.inst[grp_idx].rvc_inst : committed_rob_entry.inst[grp_idx].inst,
                      committed_rob_entry.inst[grp_idx].wr_reg.valid,
                      committed_rob_entry.inst[grp_idx].wr_reg.typ,
                      committed_rob_entry.inst[grp_idx].wr_reg.regidx,
                      committed_rob_entry.inst[grp_idx].wr_reg.rnid,
                      committed_rob_entry.inst[grp_idx].wr_reg.typ == scariv_pkg::GPR ?
                      w_physical_int_data[committed_rob_entry.inst[grp_idx].wr_reg.rnid] :
                      w_physical_fp_data [committed_rob_entry.inst[grp_idx].wr_reg.rnid]);
        end
      end  // for (int grp_idx = 0; grp_idx < scariv_pkg::DISP_SIZE; grp_idx++)
    end  // if (u_scariv_subsystem_wrapper.u_scariv_subsystem.u_tile.u_rob.w_out_valid)
  end  // else: !if(!i_scariv_reset_n)
end  // always_ff @ (negedge i_clk, negedge i_scariv_reset_n)

`endif // !`ifndef DIRECT_LOAD_HEX


`ifdef VCS_SIM

initial begin
  $fsdbDumpfile("wave.fsdb");
  $fsdbDumpvars(0, tb);
  $fsdbDumpvars("+all");
end

`endif // VCS_SIM


// always_ff @ (negedge w_clk, negedge w_scariv_reset_n) begin
//   if (!w_scariv_reset_n) begin
//   end else begin
//     $fwrite(pipe_fp, "%t PC=%010x | ", $time, u_scariv_subsystem_wrapper.u_scariv_subsystem.u_tile.w_iq_disp.pc_addr);
//     // Schedule Pipe
//     for (int grp_idx = 0; grp_idx < scariv_conf_pkg::DISP_SIZE; grp_idx++) begin
//       $fwrite(pipe_fp, "(");
//       if (u_scariv_subsystem_wrapper.u_scariv_subsystem.u_tile.w_sc_disp.inst[grp_idx].rd_valid)
//         $fwrite(pipe_fp, "%03d,", u_scariv_subsystem_wrapper.u_scariv_subsystem.u_tile.w_sc_disp.inst[grp_idx].rd_rnid);
//       else
//         $fwrite(pipe_fp, "   ,");
//       if (u_scariv_subsystem_wrapper.u_scariv_subsystem.u_tile.w_sc_disp.inst[grp_idx].rs1_valid)
//         $fwrite(pipe_fp, "%01d,%03d,", u_scariv_subsystem_wrapper.u_scariv_subsystem.u_tile.w_sc_disp.inst[grp_idx].rs1_ready,
//                 u_scariv_subsystem_wrapper.u_scariv_subsystem.u_tile.w_sc_disp.inst[grp_idx].rs1_rnid);
//       else
//         $fwrite(pipe_fp, "     ,");
//       if (u_scariv_subsystem_wrapper.u_scariv_subsystem.u_tile.w_sc_disp.inst[grp_idx].rs2_valid)
//         $fwrite(pipe_fp, "%01d,%03d,", u_scariv_subsystem_wrapper.u_scariv_subsystem.u_tile.w_sc_disp.inst[grp_idx].rs2_ready,
//                 u_scariv_subsystem_wrapper.u_scariv_subsystem.u_tile.w_sc_disp.inst[grp_idx].rs2_rnid);
//       else
//         $fwrite(pipe_fp, "     ,");
//       $fwrite(pipe_fp, ")");
//     end
//     $fwrite(pipe_fp, " | ");
//     if (u_scariv_subsystem_wrapper.u_scariv_subsystem.u_tile.u_rob.w_out_valid) begin
//       for (int grp_idx = 0; grp_idx < scariv_conf_pkg::DISP_SIZE; grp_idx++) begin
//         if (committed_rob_entry.grp_id[grp_idx]) begin
//           $fwrite (pipe_fp, "(%02d,%02d) PC=%08x ",
//                    u_scariv_subsystem_wrapper.u_scariv_subsystem.u_tile.u_rob.w_out_cmt_id, 1 << grp_idx,
//                    (committed_rob_entry.pc_addr << 1) + (4 * grp_idx));
//           if (committed_rob_entry.inst[grp_idx].rd_valid) begin
//             $fwrite (pipe_fp, "GPR[%02d](%03d)=%016x : ",
//                      committed_rob_entry.inst[grp_idx].rd_regidx,
//                      committed_rob_entry.inst[grp_idx].rd_rnid,
//                      w_physical_int_data[committed_rob_entry.inst[grp_idx].rd_rnid]);
//           end else begin
//             $fwrite (pipe_fp, "                                        : ");
//           end
//           $fwrite (pipe_fp, "DASM(%08x)", committed_rob_entry.inst[grp_idx].inst);
//         end // if (committed_rob_entry.grp_id[grp_idx])
//       end // for (int grp_idx = 0; grp_idx < scariv_conf_pkg::DISP_SIZE; grp_idx++)
//     end // if (u_scariv_subsystem_wrapper.u_scariv_subsystem.u_tile.u_rob.w_entry_all_done[u_scariv_subsystem_wrapper.u_scariv_subsystem.u_tile.u_rob.w_out_cmd_id])
//     $fwrite(pipe_fp, "\n");
//   end // else: !if(!w_scariv_reset_n)
// end // always_ff @ (negedge w_clk, negedge w_scariv_reset_n)
//
// `include "tb_json_dumper.sv"

endmodule // tb
