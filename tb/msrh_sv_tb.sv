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
   input int     rtl_wr_gpr,
   input int     rtl_wr_rnid,
   input longint rtl_wr_val
   );
`endif // DIRECT_LOAD_HEX

module tb;

logic w_clk;
logic w_elf_loader_reset_n;
logic w_msrh_reset_n;
logic w_ram_reset_n;

logic w_timeout;

logic w_terminate;
assign w_terminate = w_timeout;

/* from Frontend IC */
logic                                     w_ic_req_valid;
msrh_lsu_pkg::mem_cmd_t                   w_ic_req_cmd;
logic [riscv_pkg::PADDR_W-1:0]            w_ic_req_addr;
logic [msrh_lsu_pkg::L2_CMD_TAG_W-1:0]    w_ic_req_tag;
logic [msrh_conf_pkg::ICACHE_DATA_W-1:0]   w_ic_req_data;
logic [msrh_conf_pkg::ICACHE_DATA_W/8-1:0] w_ic_req_byte_en;
logic                                     w_ic_req_ready;

logic                                     w_ic_resp_valid;
logic [msrh_lsu_pkg::L2_CMD_TAG_W-1:0]    w_ic_resp_tag;
logic [msrh_conf_pkg::ICACHE_DATA_W-1:0]   w_ic_resp_data;
logic                                     w_ic_resp_ready  ;

/* from ELF Loader */
logic                                     w_elf_req_valid;
msrh_lsu_pkg::mem_cmd_t                   w_elf_req_cmd;
logic [riscv_pkg::PADDR_W-1:0]            w_elf_req_addr;
logic [msrh_lsu_pkg::L2_CMD_TAG_W-1:0]    w_elf_req_tag;
logic [msrh_conf_pkg::ICACHE_DATA_W-1:0]   w_elf_req_data;
logic [msrh_conf_pkg::ICACHE_DATA_W/8-1:0] w_elf_req_byte_en;
logic                                     w_elf_req_ready;

/* L1D Interface */
logic                                     w_l1d_req_valid;
msrh_lsu_pkg::mem_cmd_t                   w_l1d_req_cmd;
logic [riscv_pkg::PADDR_W-1:0]            w_l1d_req_addr;
logic [msrh_lsu_pkg::L2_CMD_TAG_W-1:0]    w_l1d_req_tag;
logic [msrh_conf_pkg::ICACHE_DATA_W-1:0]   w_l1d_req_data;
logic [msrh_conf_pkg::ICACHE_DATA_W/8-1:0] w_l1d_req_byte_en;
logic                                     w_l1d_req_ready;

logic                                     w_l1d_resp_valid;
logic [msrh_lsu_pkg::L2_CMD_TAG_W-1:0]    w_l1d_resp_tag;
logic [msrh_conf_pkg::ICACHE_DATA_W-1:0]   w_l1d_resp_data;
logic                                     w_l1d_resp_ready;

/* PTW Interface */
logic                                     w_ptw_req_valid;
msrh_lsu_pkg::mem_cmd_t                   w_ptw_req_cmd;
logic [riscv_pkg::PADDR_W-1:0]            w_ptw_req_addr;
logic [msrh_lsu_pkg::L2_CMD_TAG_W-1:0]    w_ptw_req_tag;
logic [msrh_conf_pkg::ICACHE_DATA_W-1:0]   w_ptw_req_data;
logic [msrh_conf_pkg::ICACHE_DATA_W/8-1:0] w_ptw_req_byte_en;
logic                                     w_ptw_req_ready;

logic                                     w_ptw_resp_valid;
logic [msrh_lsu_pkg::L2_CMD_TAG_W-1:0]    w_ptw_resp_tag;
logic [msrh_conf_pkg::ICACHE_DATA_W-1:0]   w_ptw_resp_data;
logic                                     w_ptw_resp_ready;

/* L2 Interface */
logic                                     w_l2_req_valid;
msrh_lsu_pkg::mem_cmd_t                   w_l2_req_cmd;
logic [riscv_pkg::PADDR_W-1:0]            w_l2_req_addr;
logic [msrh_lsu_pkg::L2_CMD_TAG_W-1:0]    w_l2_req_tag;
logic [msrh_conf_pkg::ICACHE_DATA_W-1:0]   w_l2_req_data;
logic [msrh_conf_pkg::ICACHE_DATA_W/8-1:0] w_l2_req_byte_en;
logic                                     w_l2_req_ready;

logic                                     w_l2_resp_valid;
logic [msrh_lsu_pkg::L2_CMD_TAG_W-1:0]    w_l2_resp_tag;
logic [msrh_conf_pkg::ICACHE_DATA_W-1:0]   w_l2_resp_data;
logic                                     w_l2_resp_ready;

// Snoop Interface
logic                                     w_snoop_req_valid;
logic [            riscv_pkg::PADDR_W-1:0] w_snoop_req_paddr;

logic                                      w_snoop_resp_valid;
logic [  msrh_conf_pkg::DCACHE_DATA_W-1:0] w_snoop_resp_data;
logic [ msrh_lsu_pkg::DCACHE_DATA_B_W-1:0] w_snoop_resp_be;


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
   .i_ic_req_valid    (w_ic_req_valid  ),
   .i_ic_req_cmd      (w_ic_req_cmd    ),
   .i_ic_req_addr     (w_ic_req_addr   ),
   .i_ic_req_tag      (w_ic_req_tag    ),
   .i_ic_req_data     (w_ic_req_data   ),
   .i_ic_req_byte_en  (w_ic_req_byte_en),
   .o_ic_req_ready    (w_ic_req_ready  ),

   .o_ic_resp_valid   (w_ic_resp_valid ),
   .o_ic_resp_tag     (w_ic_resp_tag   ),
   .o_ic_resp_data    (w_ic_resp_data  ),
   .i_ic_resp_ready   (w_ic_resp_ready ),

   /* L1D Interface */
   .i_l1d_req_valid   (w_l1d_req_valid  ),
   .i_l1d_req_cmd     (w_l1d_req_cmd    ),
   .i_l1d_req_addr    (w_l1d_req_addr   ),
   .i_l1d_req_tag     (w_l1d_req_tag    ),
   .i_l1d_req_data    (w_l1d_req_data   ),
   .i_l1d_req_byte_en (w_l1d_req_byte_en),
   .o_l1d_req_ready   (w_l1d_req_ready  ),

   .o_l1d_resp_valid  (w_l1d_resp_valid ),
   .o_l1d_resp_tag    (w_l1d_resp_tag   ),
   .o_l1d_resp_data   (w_l1d_resp_data  ),
   .i_l1d_resp_ready  (w_l1d_resp_ready ),

   /* PTW Interface */
   .i_ptw_req_valid   (w_ptw_req_valid  ),
   .i_ptw_req_cmd     (w_ptw_req_cmd    ),
   .i_ptw_req_addr    (w_ptw_req_addr   ),
   .i_ptw_req_tag     (w_ptw_req_tag    ),
   .i_ptw_req_data    (w_ptw_req_data   ),
   .i_ptw_req_byte_en (w_ptw_req_byte_en),
   .o_ptw_req_ready   (w_ptw_req_ready  ),

   .o_ptw_resp_valid  (w_ptw_resp_valid ),
   .o_ptw_resp_tag    (w_ptw_resp_tag   ),
   .o_ptw_resp_data   (w_ptw_resp_data  ),
   .i_ptw_resp_ready  (w_ptw_resp_ready ),

   /* L2 Interface */
   .o_l2_req_valid    (w_l2_req_valid  ),
   .o_l2_req_cmd      (w_l2_req_cmd    ),
   .o_l2_req_addr     (w_l2_req_addr   ),
   .o_l2_req_tag      (w_l2_req_tag    ),
   .o_l2_req_data     (w_l2_req_data   ),
   .o_l2_req_byte_en  (w_l2_req_byte_en),
   .i_l2_req_ready    (w_l2_req_ready  ),

   .i_l2_resp_valid   (w_l2_resp_valid ),
   .i_l2_resp_tag     (w_l2_resp_tag   ),
   .i_l2_resp_data    (w_l2_resp_data  ),
   .o_l2_resp_ready   (w_l2_resp_ready )
   );


msrh_tile_wrapper u_msrh_tile_wrapper
  (
    .i_clk     (w_clk),
    .i_reset_n (w_msrh_reset_n),

    // ICache Interconnection
    .o_ic_req_valid  (w_ic_req_valid  ),
    .o_ic_req_cmd    (w_ic_req_cmd    ),
    .o_ic_req_addr   (w_ic_req_addr   ),
    .o_ic_req_tag    (w_ic_req_tag    ),
    .o_ic_req_data   (w_ic_req_data   ),
    .o_ic_req_byte_en(w_ic_req_byte_en),
    .i_ic_req_ready  (w_ic_req_ready  ),

    .i_ic_resp_valid (w_ic_resp_valid ),
    .i_ic_resp_tag   (w_ic_resp_tag   ),
    .i_ic_resp_data  (w_ic_resp_data  ),
    .o_ic_resp_ready (w_ic_resp_ready ),

    // L1D Interconnection
    .o_l1d_req_valid  (w_l1d_req_valid  ),
    .o_l1d_req_cmd    (w_l1d_req_cmd    ),
    .o_l1d_req_addr   (w_l1d_req_addr   ),
    .o_l1d_req_tag    (w_l1d_req_tag    ),
    .o_l1d_req_data   (w_l1d_req_data   ),
    .o_l1d_req_byte_en(w_l1d_req_byte_en),
    .i_l1d_req_ready  (w_l1d_req_ready  ),

    .i_l1d_resp_valid (w_l1d_resp_valid ),
    .i_l1d_resp_tag   (w_l1d_resp_tag   ),
    .i_l1d_resp_data  (w_l1d_resp_data  ),
    .o_l1d_resp_ready (w_l1d_resp_ready ),

    // PTW Interconnection
    .o_ptw_req_valid  (w_ptw_req_valid  ),
    .o_ptw_req_cmd    (w_ptw_req_cmd    ),
    .o_ptw_req_addr   (w_ptw_req_addr   ),
    .o_ptw_req_tag    (w_ptw_req_tag    ),
    .o_ptw_req_data   (w_ptw_req_data   ),
    .o_ptw_req_byte_en(w_ptw_req_byte_en),
    .i_ptw_req_ready  (w_ptw_req_ready  ),

    .i_ptw_resp_valid (w_ptw_resp_valid ),
    .i_ptw_resp_tag   (w_ptw_resp_tag   ),
    .i_ptw_resp_data  (w_ptw_resp_data  ),
    .o_ptw_resp_ready (w_ptw_resp_ready ),

   // Snoop Interface
   .i_snoop_req_valid(w_snoop_req_valid),
   .i_snoop_req_paddr(w_snoop_req_paddr),

   .o_snoop_resp_valid(w_snoop_resp_valid),
   .o_snoop_resp_data (w_snoop_resp_data),
   .o_snoop_resp_be   (w_snoop_resp_be)
   );


tb_l2_behavior_ram
  #(
    .DATA_W    (msrh_conf_pkg::ICACHE_DATA_W),
    .TAG_W     (msrh_lsu_pkg::L2_CMD_TAG_W),
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
assign w_elf_req_cmd    = msrh_lsu_pkg::M_XRD;
assign w_elf_req_addr   = 'h0;
assign w_elf_req_tag    = 'h0;
assign w_elf_req_data   = 'h0;
assign w_elf_req_byte_en = 'h0;
`endif // DIRECT_LOAD_HEX

localparam STEP = 1;
localparam TIMEOUT = 100000;

initial begin
  w_clk = 1'b0;
  w_elf_loader_reset_n = 1'b0;
  w_msrh_reset_n        = 1'b0;
  w_ram_reset_n        = 1'b0;

  #(STEP * 10);

  w_elf_loader_reset_n = 1'b1;
  w_msrh_reset_n        = 1'b0;
  w_ram_reset_n        = 1'b1;

  #(STEP * 100);

  w_elf_loader_reset_n = 1'b0;
  w_msrh_reset_n        = 1'b1;
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

// always_ff @ (negedge w_clk, negedge w_msrh_reset_n) begin
//   if (!w_msrh_reset_n) begin
//   end else begin
//     if (u_msrh_tile_wrapper.u_msrh_tile.u_rob.w_out_valid) begin
//       for (int grp_idx = 0; grp_idx < msrh_conf_pkg::DISP_SIZE; grp_idx++) begin
//         if (committed_rob_entry.grp_id[grp_idx] & (!w_dead_grp_id[grp_idx])) begin
//           $fwrite (log_fp, "%t PC=%010x (%02d,%02d) %08x ", $time, (committed_rob_entry.pc_addr << 1) + (4 * grp_idx),
//                    u_msrh_tile_wrapper.u_msrh_tile.u_rob.w_out_cmt_id, 1 << grp_idx,
//                    committed_rob_entry.inst[grp_idx].inst);
//           if (committed_rob_entry.inst[grp_idx].rd_valid) begin
//             $fwrite (log_fp, "GPR[%02d](%03d)=%016x : ",
//                      committed_rob_entry.inst[grp_idx].rd_regidx,
//                      committed_rob_entry.inst[grp_idx].rd_rnid,
//                      w_physical_gpr_data[committed_rob_entry.inst[grp_idx].rd_rnid]);
//           end else begin
//             $fwrite (log_fp, "                              : ");
//           end
//           $fwrite(log_fp, "DASM(%08x)\n", committed_rob_entry.inst[grp_idx].inst);
//         end // if (committed_rob_entry.grp_id[grp_idx])
//       end // for (int grp_idx = 0; grp_idx < msrh_conf_pkg::DISP_SIZE; grp_idx++)
//     end // if (u_msrh_tile_wrapper.u_msrh_tile.u_rob.w_entry_all_done[u_msrh_tile_wrapper.u_msrh_tile.u_rob.w_out_cmd_id])
//   end
// end

`ifndef DIRECT_LOAD_HEX

always_ff @(negedge w_clk, negedge w_msrh_reset_n) begin
  if (!w_msrh_reset_n) begin
  end else begin
    if (u_msrh_tile_wrapper.u_msrh_tile.u_rob.o_commit.commit & !u_msrh_tile_wrapper.u_msrh_tile.u_rob.o_commit.all_dead) begin
      for (int grp_idx = 0; grp_idx < msrh_conf_pkg::DISP_SIZE; grp_idx++) begin
        if (committed_rob_entry.grp_id[grp_idx]) begin
          $fwrite (pipe_fp, "(%02d,%02d) PC=%08x ",
                   u_msrh_tile_wrapper.u_msrh_tile.u_rob.w_out_cmt_id, 1 << grp_idx,
                   (committed_rob_entry.pc_addr << 1) + (4 * grp_idx));
          if (committed_rob_entry.inst[grp_idx].rd_valid) begin
            $fwrite (pipe_fp, "GPR[%02d](%03d)=%016x : ",
                     committed_rob_entry.inst[grp_idx].rd_regidx,
                     committed_rob_entry.inst[grp_idx].rd_rnid,
                     w_physical_gpr_data[committed_rob_entry.inst[grp_idx].rd_rnid]);
          end else begin
            $fwrite (pipe_fp, "                                        : ");
          end
          $fwrite (pipe_fp, "DASM(%08x)", committed_rob_entry.inst[grp_idx].inst);
        end // if (committed_rob_entry.grp_id[grp_idx])
      end // for (int grp_idx = 0; grp_idx < msrh_conf_pkg::DISP_SIZE; grp_idx++)
    end // if (u_msrh_tile_wrapper.u_msrh_tile.u_rob.w_entry_all_done[u_msrh_tile_wrapper.u_msrh_tile.u_rob.w_out_cmd_id])
    $fwrite(pipe_fp, "\n");
  end // else: !if(!w_msrh_reset_n)
end // always_ff @ (negedge w_clk, negedge w_msrh_reset_n)
`endif //  `ifndef DIRECT_LOAD_HEX

`include "tb_json_dumper.sv"
=======
        if (u_msrh_tile_wrapper.u_msrh_tile.u_rob.o_commit.grp_id[grp_idx] &
            ~u_msrh_tile_wrapper.u_msrh_tile.u_rob.o_commit.dead_id[grp_idx]) begin
          /* verilator lint_off WIDTH */
          step_spike ($time, longint'(committed_rob_entry.inst[grp_idx].pc_addr),
                      int'(u_msrh_tile_wrapper.u_msrh_tile.u_msrh_csu.u_msrh_csr.r_priv),
                      u_msrh_tile_wrapper.u_msrh_tile.u_rob.w_sim_mstatus[u_msrh_tile_wrapper.u_msrh_tile.u_rob.w_out_cmt_entry_id][grp_idx],
                      u_msrh_tile_wrapper.u_msrh_tile.u_rob.w_valid_except_grp_id[grp_idx],
                      u_msrh_tile_wrapper.u_msrh_tile.u_rob.w_except_type_selected,
                      u_msrh_tile_wrapper.u_msrh_tile.u_rob.w_out_cmt_id,
                      1 << grp_idx,
                      committed_rob_entry.inst[grp_idx].rvc_inst_valid ? committed_rob_entry.inst[grp_idx].rvc_inst : committed_rob_entry.inst[grp_idx].inst,
                      committed_rob_entry.inst[grp_idx].rd_valid,
                      committed_rob_entry.inst[grp_idx].rd_regidx,
                      committed_rob_entry.inst[grp_idx].rd_rnid,
                      w_physical_gpr_data[committed_rob_entry.inst[grp_idx].rd_rnid]);
        end
      end  // for (int grp_idx = 0; grp_idx < msrh_pkg::DISP_SIZE; grp_idx++)
    end  // if (u_msrh_tile_wrapper.u_msrh_tile.u_rob.w_out_valid)
  end  // else: !if(!i_msrh_reset_n)
end  // always_ff @ (negedge i_clk, negedge i_msrh_reset_n)


// always_ff @ (negedge w_clk, negedge w_msrh_reset_n) begin
//   if (!w_msrh_reset_n) begin
//   end else begin
//     $fwrite(pipe_fp, "%t PC=%010x | ", $time, u_msrh_tile_wrapper.u_msrh_tile.w_iq_disp.pc_addr);
//     // Schedule Pipe
//     for (int grp_idx = 0; grp_idx < msrh_conf_pkg::DISP_SIZE; grp_idx++) begin
//       $fwrite(pipe_fp, "(");
//       if (u_msrh_tile_wrapper.u_msrh_tile.w_sc_disp.inst[grp_idx].rd_valid)
//         $fwrite(pipe_fp, "%03d,", u_msrh_tile_wrapper.u_msrh_tile.w_sc_disp.inst[grp_idx].rd_rnid);
//       else
//         $fwrite(pipe_fp, "   ,");
//       if (u_msrh_tile_wrapper.u_msrh_tile.w_sc_disp.inst[grp_idx].rs1_valid)
//         $fwrite(pipe_fp, "%01d,%03d,", u_msrh_tile_wrapper.u_msrh_tile.w_sc_disp.inst[grp_idx].rs1_ready,
//                 u_msrh_tile_wrapper.u_msrh_tile.w_sc_disp.inst[grp_idx].rs1_rnid);
//       else
//         $fwrite(pipe_fp, "     ,");
//       if (u_msrh_tile_wrapper.u_msrh_tile.w_sc_disp.inst[grp_idx].rs2_valid)
//         $fwrite(pipe_fp, "%01d,%03d,", u_msrh_tile_wrapper.u_msrh_tile.w_sc_disp.inst[grp_idx].rs2_ready,
//                 u_msrh_tile_wrapper.u_msrh_tile.w_sc_disp.inst[grp_idx].rs2_rnid);
//       else
//         $fwrite(pipe_fp, "     ,");
//       $fwrite(pipe_fp, ")");
//     end
//     $fwrite(pipe_fp, " | ");
//     if (u_msrh_tile_wrapper.u_msrh_tile.u_rob.w_out_valid) begin
//       for (int grp_idx = 0; grp_idx < msrh_conf_pkg::DISP_SIZE; grp_idx++) begin
//         if (committed_rob_entry.grp_id[grp_idx]) begin
//           $fwrite (pipe_fp, "(%02d,%02d) PC=%08x ",
//                    u_msrh_tile_wrapper.u_msrh_tile.u_rob.w_out_cmt_id, 1 << grp_idx,
//                    (committed_rob_entry.pc_addr << 1) + (4 * grp_idx));
//           if (committed_rob_entry.inst[grp_idx].rd_valid) begin
//             $fwrite (pipe_fp, "GPR[%02d](%03d)=%016x : ",
//                      committed_rob_entry.inst[grp_idx].rd_regidx,
//                      committed_rob_entry.inst[grp_idx].rd_rnid,
//                      w_physical_gpr_data[committed_rob_entry.inst[grp_idx].rd_rnid]);
//           end else begin
//             $fwrite (pipe_fp, "                                        : ");
//           end
//           $fwrite (pipe_fp, "DASM(%08x)", committed_rob_entry.inst[grp_idx].inst);
//         end // if (committed_rob_entry.grp_id[grp_idx])
//       end // for (int grp_idx = 0; grp_idx < msrh_conf_pkg::DISP_SIZE; grp_idx++)
//     end // if (u_msrh_tile_wrapper.u_msrh_tile.u_rob.w_entry_all_done[u_msrh_tile_wrapper.u_msrh_tile.u_rob.w_out_cmd_id])
//     $fwrite(pipe_fp, "\n");
//   end // else: !if(!w_msrh_reset_n)
// end // always_ff @ (negedge w_clk, negedge w_msrh_reset_n)
//
// `include "tb_json_dumper.sv"
>>>>>>> 71d5661cd32adc3d7b02a9ce6c790f14916c95ed

// always_ff @ (negedge w_clk, negedge w_msrh_reset_n) begin
//   if (!w_msrh_reset_n) begin
//   end else begin
//     $fwrite(pipe_fp, "%t PC=%010x | ", $time, u_msrh_tile_wrapper.u_msrh_tile.w_iq_disp.pc_addr);
//     // Schedule Pipe
//     for (int grp_idx = 0; grp_idx < msrh_conf_pkg::DISP_SIZE; grp_idx++) begin
//       $fwrite(pipe_fp, "(");
//       if (u_msrh_tile_wrapper.u_msrh_tile.w_sc_disp.inst[grp_idx].rd_valid)
//         $fwrite(pipe_fp, "%03d,", u_msrh_tile_wrapper.u_msrh_tile.w_sc_disp.inst[grp_idx].rd_rnid);
//       else
//         $fwrite(pipe_fp, "   ,");
//       if (u_msrh_tile_wrapper.u_msrh_tile.w_sc_disp.inst[grp_idx].rs1_valid)
//         $fwrite(pipe_fp, "%01d,%03d,", u_msrh_tile_wrapper.u_msrh_tile.w_sc_disp.inst[grp_idx].rs1_ready,
//                 u_msrh_tile_wrapper.u_msrh_tile.w_sc_disp.inst[grp_idx].rs1_rnid);
//       else
//         $fwrite(pipe_fp, "     ,");
//       if (u_msrh_tile_wrapper.u_msrh_tile.w_sc_disp.inst[grp_idx].rs2_valid)
//         $fwrite(pipe_fp, "%01d,%03d,", u_msrh_tile_wrapper.u_msrh_tile.w_sc_disp.inst[grp_idx].rs2_ready,
//                 u_msrh_tile_wrapper.u_msrh_tile.w_sc_disp.inst[grp_idx].rs2_rnid);
//       else
//         $fwrite(pipe_fp, "     ,");
//       $fwrite(pipe_fp, ")");
//     end
//     $fwrite(pipe_fp, " | ");
//     if (u_msrh_tile_wrapper.u_msrh_tile.u_rob.w_out_valid) begin
//       for (int grp_idx = 0; grp_idx < msrh_conf_pkg::DISP_SIZE; grp_idx++) begin
//         if (committed_rob_entry.grp_id[grp_idx]) begin
//           $fwrite (pipe_fp, "(%02d,%02d) PC=%08x ",
//                    u_msrh_tile_wrapper.u_msrh_tile.u_rob.w_out_cmt_id, 1 << grp_idx,
//                    (committed_rob_entry.pc_addr << 1) + (4 * grp_idx));
//           if (committed_rob_entry.inst[grp_idx].rd_valid) begin
//             $fwrite (pipe_fp, "GPR[%02d](%03d)=%016x : ",
//                      committed_rob_entry.inst[grp_idx].rd_regidx,
//                      committed_rob_entry.inst[grp_idx].rd_rnid,
//                      w_physical_gpr_data[committed_rob_entry.inst[grp_idx].rd_rnid]);
//           end else begin
//             $fwrite (pipe_fp, "                                        : ");
//           end
//           $fwrite (pipe_fp, "DASM(%08x)", committed_rob_entry.inst[grp_idx].inst);
//         end // if (committed_rob_entry.grp_id[grp_idx])
//       end // for (int grp_idx = 0; grp_idx < msrh_conf_pkg::DISP_SIZE; grp_idx++)
//     end // if (u_msrh_tile_wrapper.u_msrh_tile.u_rob.w_entry_all_done[u_msrh_tile_wrapper.u_msrh_tile.u_rob.w_out_cmd_id])
//     $fwrite(pipe_fp, "\n");
//   end // else: !if(!w_msrh_reset_n)
// end // always_ff @ (negedge w_clk, negedge w_msrh_reset_n)
//
// `include "tb_json_dumper.sv"

endmodule // tb
