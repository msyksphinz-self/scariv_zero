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
   input int     rtl_wr_gpr,
   input int     rtl_wr_rnid,
   input longint rtl_wr_val
   );

module msrh_tb (
    input logic i_clk,

    input logic i_elf_loader_reset_n,
    input logic i_msrh_reset_n,

    input logic i_ram_reset_n
);

  /* from ELF Loader */
  logic                                                        w_elf_req_valid;
  msrh_lsu_pkg::mem_cmd_t                                      w_elf_req_cmd;
  logic                   [            riscv_pkg::PADDR_W-1:0] w_elf_req_addr;
  logic                   [    msrh_lsu_pkg::L2_CMD_TAG_W-1:0] w_elf_req_tag;
  logic                   [  msrh_conf_pkg::ICACHE_DATA_W-1:0] w_elf_req_data;
  logic                   [msrh_conf_pkg::ICACHE_DATA_W/8-1:0] w_elf_req_byte_en;
  logic                                                        w_elf_req_ready;

  /* from Frontend IC */
  logic                                                        w_ic_req_valid;
  msrh_lsu_pkg::mem_cmd_t                                      w_ic_req_cmd;
  logic                   [            riscv_pkg::PADDR_W-1:0] w_ic_req_addr;
  logic                   [    msrh_lsu_pkg::L2_CMD_TAG_W-1:0] w_ic_req_tag;
  logic                   [  msrh_conf_pkg::ICACHE_DATA_W-1:0] w_ic_req_data;
  logic                   [msrh_conf_pkg::ICACHE_DATA_W/8-1:0] w_ic_req_byte_en;
  logic                                                        w_ic_req_ready;

  logic                                                        w_ic_resp_valid;
  logic                   [    msrh_lsu_pkg::L2_CMD_TAG_W-1:0] w_ic_resp_tag;
  logic                   [  msrh_conf_pkg::ICACHE_DATA_W-1:0] w_ic_resp_data;
  logic                                                        w_ic_resp_ready;

  /* L1D Interface */
  logic                                                        w_l1d_req_valid;
  msrh_lsu_pkg::mem_cmd_t                                      w_l1d_req_cmd;
  logic                   [            riscv_pkg::PADDR_W-1:0] w_l1d_req_addr;
  logic                   [    msrh_lsu_pkg::L2_CMD_TAG_W-1:0] w_l1d_req_tag;
  logic                   [  msrh_conf_pkg::ICACHE_DATA_W-1:0] w_l1d_req_data;
  logic                   [msrh_conf_pkg::ICACHE_DATA_W/8-1:0] w_l1d_req_byte_en;
  logic                                                        w_l1d_req_ready;

  logic                                                        w_l1d_resp_valid;
  logic                   [    msrh_lsu_pkg::L2_CMD_TAG_W-1:0] w_l1d_resp_tag;
  logic                   [  msrh_conf_pkg::ICACHE_DATA_W-1:0] w_l1d_resp_data;
  logic                                                        w_l1d_resp_ready;

  /* PTW Interface */
  logic                                                        w_ptw_req_valid;
  msrh_lsu_pkg::mem_cmd_t                                      w_ptw_req_cmd;
  logic                   [            riscv_pkg::PADDR_W-1:0] w_ptw_req_addr;
  logic                   [    msrh_lsu_pkg::L2_CMD_TAG_W-1:0] w_ptw_req_tag;
  logic                   [  msrh_conf_pkg::ICACHE_DATA_W-1:0] w_ptw_req_data;
  logic                   [msrh_conf_pkg::ICACHE_DATA_W/8-1:0] w_ptw_req_byte_en;
  logic                                                        w_ptw_req_ready;

  logic                                                        w_ptw_resp_valid;
  logic                   [    msrh_lsu_pkg::L2_CMD_TAG_W-1:0] w_ptw_resp_tag;
  logic                   [  msrh_conf_pkg::ICACHE_DATA_W-1:0] w_ptw_resp_data;
  logic                                                        w_ptw_resp_ready;

  /* L2 Interface */
  logic                                                        w_l2_req_valid;
  msrh_lsu_pkg::mem_cmd_t                                      w_l2_req_cmd;
  logic                   [            riscv_pkg::PADDR_W-1:0] w_l2_req_addr;
  logic                   [    msrh_lsu_pkg::L2_CMD_TAG_W-1:0] w_l2_req_tag;
  logic                   [  msrh_conf_pkg::ICACHE_DATA_W-1:0] w_l2_req_data;
  logic                   [msrh_conf_pkg::ICACHE_DATA_W/8-1:0] w_l2_req_byte_en;
  logic                                                        w_l2_req_ready;

  logic                                                        w_l2_resp_valid;
  logic                   [    msrh_lsu_pkg::L2_CMD_TAG_W-1:0] w_l2_resp_tag;
  logic                   [  msrh_conf_pkg::ICACHE_DATA_W-1:0] w_l2_resp_data;
  logic                                                        w_l2_resp_ready;

  // Snoop Interface
  logic                                                        w_snoop_req_valid;
  logic                   [            riscv_pkg::PADDR_W-1:0] w_snoop_req_paddr;

  logic                                                        w_snoop_resp_valid;
  logic                   [  msrh_conf_pkg::DCACHE_DATA_W-1:0] w_snoop_resp_data;
  logic                   [ msrh_lsu_pkg::DCACHE_DATA_B_W-1:0] w_snoop_resp_be;

  /* Connection */
  l2c_arbiter_wrapper u_l2c_arbiter_wrapper (
      /* from ELF Loader */
      .i_elf_req_valid  (w_elf_req_valid),
      .i_elf_req_cmd    (w_elf_req_cmd),
      .i_elf_req_addr   (w_elf_req_addr),
      .i_elf_req_tag    (w_elf_req_tag),
      .i_elf_req_data   (w_elf_req_data),
      .i_elf_req_byte_en(w_elf_req_byte_en),
      .o_elf_req_ready  (w_elf_req_ready),

      /* from Frontend IC */
      .i_ic_req_valid  (w_ic_req_valid),
      .i_ic_req_cmd    (w_ic_req_cmd),
      .i_ic_req_addr   (w_ic_req_addr),
      .i_ic_req_tag    (w_ic_req_tag),
      .i_ic_req_data   (w_ic_req_data),
      .i_ic_req_byte_en(w_ic_req_byte_en),
      .o_ic_req_ready  (w_ic_req_ready),

      .o_ic_resp_valid(w_ic_resp_valid),
      .o_ic_resp_tag  (w_ic_resp_tag),
      .o_ic_resp_data (w_ic_resp_data),
      .i_ic_resp_ready(w_ic_resp_ready),

      /* L1D Interface */
      .i_l1d_req_valid  (w_l1d_req_valid),
      .i_l1d_req_cmd    (w_l1d_req_cmd),
      .i_l1d_req_addr   (w_l1d_req_addr),
      .i_l1d_req_tag    (w_l1d_req_tag),
      .i_l1d_req_data   (w_l1d_req_data),
      .i_l1d_req_byte_en(w_l1d_req_byte_en),
      .o_l1d_req_ready  (w_l1d_req_ready),

      .o_l1d_resp_valid(w_l1d_resp_valid),
      .o_l1d_resp_tag  (w_l1d_resp_tag),
      .o_l1d_resp_data (w_l1d_resp_data),
      .i_l1d_resp_ready(w_l1d_resp_ready),

      /* PTW Interface */
      .i_ptw_req_valid  (w_ptw_req_valid),
      .i_ptw_req_cmd    (w_ptw_req_cmd),
      .i_ptw_req_addr   (w_ptw_req_addr),
      .i_ptw_req_tag    (w_ptw_req_tag),
      .i_ptw_req_data   (w_ptw_req_data),
      .i_ptw_req_byte_en(w_ptw_req_byte_en),
      .o_ptw_req_ready  (w_ptw_req_ready),

      .o_ptw_resp_valid(w_ptw_resp_valid),
      .o_ptw_resp_tag  (w_ptw_resp_tag),
      .o_ptw_resp_data (w_ptw_resp_data),
      .i_ptw_resp_ready(w_ptw_resp_ready),

      /* L2 Interface */
      .o_l2_req_valid  (w_l2_req_valid),
      .o_l2_req_cmd    (w_l2_req_cmd),
      .o_l2_req_addr   (w_l2_req_addr),
      .o_l2_req_tag    (w_l2_req_tag),
      .o_l2_req_data   (w_l2_req_data),
      .o_l2_req_byte_en(w_l2_req_byte_en),
      .i_l2_req_ready  (w_l2_req_ready),

      .i_l2_resp_valid(w_l2_resp_valid),
      .i_l2_resp_tag  (w_l2_resp_tag),
      .i_l2_resp_data (w_l2_resp_data),
      .o_l2_resp_ready(w_l2_resp_ready)
  );


  // assign w_l2_req_valid   = w_l1d_req_valid ? w_l1d_req_valid   : i_msrh_reset_n ? w_ic_req_valid   : w_elf_req_valid;
  // assign w_l2_req_cmd     = w_l1d_req_valid ? w_l1d_req_cmd     : i_msrh_reset_n ? w_ic_req_cmd     : w_elf_req_cmd;
  // assign w_l2_req_addr    = w_l1d_req_valid ? w_l1d_req_addr    : i_msrh_reset_n ? w_ic_req_addr    : w_elf_req_addr;
  // assign w_l2_req_tag     = w_l1d_req_valid ? w_l1d_req_tag     : i_msrh_reset_n ? w_ic_req_tag     : w_elf_req_tag;
  // assign w_l2_req_data    = w_l1d_req_valid ? w_l1d_req_data    : i_msrh_reset_n ? w_ic_req_data    : w_elf_req_data;
  // assign w_l2_req_byte_en = w_l1d_req_valid ? w_l1d_req_byte_en : i_msrh_reset_n ? w_ic_req_byte_en : w_elf_req_byte_en;
  //
  //
  // assign w_ic_req_ready  = w_l1d_req_valid ? 1'b0 : w_l2_req_ready ;
  // assign w_l1d_req_ready = w_l2_req_ready ;
  // assign w_elf_req_ready = w_l2_req_ready ;
  //
  // assign w_ic_resp_valid = w_l2_resp_valid;
  // assign w_ic_resp_tag   = w_l2_resp_tag  ;
  // assign w_ic_resp_data  = w_l2_resp_data ;
  //
  // assign w_l2_resp_ready = w_ic_resp_ready | w_l1d_resp_ready;
  //
  // assign w_l1d_resp_valid = w_l2_resp_valid;
  // assign w_l1d_resp_tag   = w_l2_resp_tag  ;
  // assign w_l1d_resp_data  = w_l2_resp_data ;

  msrh_tile_wrapper u_msrh_tile_wrapper (
      .i_clk    (i_clk),
      .i_reset_n(i_msrh_reset_n),

      // ICache Interconnection
      .o_ic_req_valid  (w_ic_req_valid),
      .o_ic_req_cmd    (w_ic_req_cmd),
      .o_ic_req_addr   (w_ic_req_addr),
      .o_ic_req_tag    (w_ic_req_tag),
      .o_ic_req_data   (w_ic_req_data),
      .o_ic_req_byte_en(w_ic_req_byte_en),
      .i_ic_req_ready  (w_ic_req_ready),

      .i_ic_resp_valid(w_ic_resp_valid),
      .i_ic_resp_tag  (w_ic_resp_tag),
      .i_ic_resp_data (w_ic_resp_data),
      .o_ic_resp_ready(w_ic_resp_ready),

      // L1D Interconnection
      .o_l1d_req_valid  (w_l1d_req_valid),
      .o_l1d_req_cmd    (w_l1d_req_cmd),
      .o_l1d_req_addr   (w_l1d_req_addr),
      .o_l1d_req_tag    (w_l1d_req_tag),
      .o_l1d_req_data   (w_l1d_req_data),
      .o_l1d_req_byte_en(w_l1d_req_byte_en),
      .i_l1d_req_ready  (w_l1d_req_ready),

      .i_l1d_resp_valid(w_l1d_resp_valid),
      .i_l1d_resp_tag  (w_l1d_resp_tag),
      .i_l1d_resp_data (w_l1d_resp_data),
      .o_l1d_resp_ready(w_l1d_resp_ready),

      // PTW Interconnection
      .o_ptw_req_valid  (w_ptw_req_valid),
      .o_ptw_req_cmd    (w_ptw_req_cmd),
      .o_ptw_req_addr   (w_ptw_req_addr),
      .o_ptw_req_tag    (w_ptw_req_tag),
      .o_ptw_req_data   (w_ptw_req_data),
      .o_ptw_req_byte_en(w_ptw_req_byte_en),
      .i_ptw_req_ready  (w_ptw_req_ready),

      .i_ptw_resp_valid(w_ptw_resp_valid),
      .i_ptw_resp_tag  (w_ptw_resp_tag),
      .i_ptw_resp_data (w_ptw_resp_data),
      .o_ptw_resp_ready(w_ptw_resp_ready),

      // Snoop Interface
      .i_snoop_req_valid(w_snoop_req_valid),
      .i_snoop_req_paddr(w_snoop_req_paddr),

      .o_snoop_resp_valid(w_snoop_resp_valid),
      .o_snoop_resp_data (w_snoop_resp_data),
      .o_snoop_resp_be   (w_snoop_resp_be)
  );


  tb_l2_behavior_ram #(
      .DATA_W   (msrh_conf_pkg::ICACHE_DATA_W),
      .TAG_W    (msrh_lsu_pkg::L2_CMD_TAG_W),
      .ADDR_W   (riscv_pkg::PADDR_W),
      .BASE_ADDR('h8000_0000),
      .SIZE     ('h4000),
      .RD_LAT   (10)
  ) u_tb_l2_behavior_ram (
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

  always_ff @(negedge i_clk, negedge i_msrh_reset_n) begin
    if (!i_msrh_reset_n) begin
    end else begin
      if (u_msrh_tile_wrapper.u_msrh_tile.u_rob.o_commit.commit) begin
        for (int grp_idx = 0; grp_idx < msrh_pkg::DISP_SIZE; grp_idx++) begin
          if (u_msrh_tile_wrapper.u_msrh_tile.u_rob.o_commit.grp_id[grp_idx] &
              ~u_msrh_tile_wrapper.u_msrh_tile.u_rob.o_commit.dead_id[grp_idx]) begin
            /* verilator lint_off WIDTH */
            step_spike ($time / 4, longint'(committed_rob_entry.inst[grp_idx].pc_addr),
                        int'(u_msrh_tile_wrapper.u_msrh_tile.u_msrh_csu.u_msrh_csr.r_priv),
                        u_msrh_tile_wrapper.u_msrh_tile.u_rob.w_sim_mstatus[u_msrh_tile_wrapper.u_msrh_tile.u_rob.w_out_cmt_entry_id][grp_idx],
                        u_msrh_tile_wrapper.u_msrh_tile.u_rob.w_valid_except_grp_id[grp_idx],
                        u_msrh_tile_wrapper.u_msrh_tile.u_rob.w_except_type_selected,
                        u_msrh_tile_wrapper.u_msrh_tile.u_rob.w_out_cmt_id,
                        1 << grp_idx,
                        committed_rob_entry.inst[grp_idx].rvc_inst_valid ? committed_rob_entry.inst[grp_idx].rvc_inst : committed_rob_entry.inst[grp_idx].inst,
                        committed_rob_entry.inst[grp_idx].wr_reg.valid,
                        committed_rob_entry.inst[grp_idx].wr_reg.regidx,
                        committed_rob_entry.inst[grp_idx].wr_reg.rnid,
                        w_physical_gpr_data[committed_rob_entry.inst[grp_idx].wr_reg.rnid]);
          end
        end  // for (int grp_idx = 0; grp_idx < msrh_pkg::DISP_SIZE; grp_idx++)
      end  // if (u_msrh_tile_wrapper.u_msrh_tile.u_rob.w_out_valid)

      // Counting up instruction
      cycle_counter <= cycle_counter + 1;
      if (u_msrh_tile_wrapper.u_msrh_tile.u_rob.o_commit.commit) begin
        total_commit_counter <= total_commit_counter + $countones(u_msrh_tile_wrapper.u_msrh_tile.u_rob.o_commit.grp_id &
                                                     ~u_msrh_tile_wrapper.u_msrh_tile.u_rob.o_commit.dead_id);
        int_commit_counter <= int_commit_counter + $countones(u_msrh_tile_wrapper.u_msrh_tile.u_rob.o_commit.grp_id &
                                                             ~u_msrh_tile_wrapper.u_msrh_tile.u_rob.o_commit.dead_id);
      end
      if (((cycle_counter % cycle_interval) == 0) && (cycle_counter != 0)) begin
        $display ("%10d : %10d : IPC(recent) = %0.02f, IPC(total) = %0.02f",
                  cycle_counter,
                  total_commit_counter,
                  real'(int_commit_counter) / cycle_interval,
                  real'(total_commit_counter) / real'(cycle_counter));
        int_commit_counter <= 'h0;
      end
    end  // else: !if(!i_msrh_reset_n)
  end  // always_ff @ (negedge i_clk, negedge i_msrh_reset_n)



  logic w_clk;
  logic w_msrh_reset_n;
  assign w_clk = i_clk;
  assign w_msrh_reset_n = i_msrh_reset_n;

  `include "tb_json_dumper.sv"
  `include "tb_json_perf_dumper.sv"

`ifdef NEVER
// ------------------------------
// Instruction Cache Checker
// ------------------------------
logic [riscv_pkg::PADDR_W-1: $clog2(msrh_lsu_pkg::ICACHE_DATA_B_W)] ram_addr;
assign ram_addr = u_msrh_tile_wrapper.u_msrh_tile.u_frontend.r_s2_paddr[riscv_pkg::PADDR_W-1: $clog2(msrh_lsu_pkg::ICACHE_DATA_B_W)];

always_ff @(negedge i_clk, negedge i_msrh_reset_n) begin
  if (i_msrh_reset_n) begin
    if (u_msrh_tile_wrapper.u_msrh_tile.u_frontend.u_msrh_icache.o_s2_resp.valid &
        ~u_msrh_tile_wrapper.u_msrh_tile.u_frontend.r_s2_tlb_miss) begin
      if (u_tb_l2_behavior_ram.ram[ram_addr] != u_msrh_tile_wrapper.u_msrh_tile.u_frontend.u_msrh_icache.o_s2_resp.data) begin
        $fatal(0, "Fetched data from ICache and External L2 data is different.\n Addr = %x\n  Fetch = %x\n  Data  = %x\n",
               u_msrh_tile_wrapper.u_msrh_tile.u_frontend.r_s2_paddr,
               u_msrh_tile_wrapper.u_msrh_tile.u_frontend.u_msrh_icache.o_s2_resp.data,
               u_tb_l2_behavior_ram.ram[ram_addr]);
      end
    end
  end // else: !if(!i_msrh_reset_n)
end // always_ff @ (negedge i_clk, negedge i_msrh_reset_n)
`endif //  `ifdef NEVER

endmodule  // msrh_tb
