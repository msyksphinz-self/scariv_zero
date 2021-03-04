import "DPI-C" function load_binary
(
 input string path_exec,
 input string filename,
 input logic is_load_dump
);


import "DPI-C" function void step_spike
  (
   input longint rtl_time,
   input longint rtl_pc,
   input int     rtl_cmt_id,
   input int     rtl_grp_id,
   input int     rtl_insn,
   input int     rtl_wr_valid,
   input int     rtl_wr_gpr,
   input longint rtl_wr_val
   );


module msrh_tb
  (
   input logic i_clk,

   input logic i_elf_loader_reset_n,
   input logic i_msrh_reset_n,

   input logic i_ram_reset_n
   );

/* from Frontend IC */
logic                                     w_ic_req_valid;
msrh_lsu_pkg::mem_cmd_t                   w_ic_req_cmd;
logic [riscv_pkg::PADDR_W-1:0]            w_ic_req_addr;
logic [msrh_lsu_pkg::L2_CMD_TAG_W-1:0]    w_ic_req_tag;
logic [msrh_lsu_pkg::ICACHE_DATA_W-1:0]   w_ic_req_data;
logic [msrh_lsu_pkg::ICACHE_DATA_W/8-1:0] w_ic_req_byte_en;
logic                                     w_ic_req_ready;

logic                                     w_ic_resp_valid;
logic [msrh_lsu_pkg::L2_CMD_TAG_W-1:0]    w_ic_resp_tag;
logic [msrh_lsu_pkg::ICACHE_DATA_W-1:0]   w_ic_resp_data;
logic                                     w_ic_resp_ready  ;

/* from ELF Loader */
logic                                     w_elf_req_valid;
msrh_lsu_pkg::mem_cmd_t                   w_elf_req_cmd;
logic [riscv_pkg::PADDR_W-1:0]            w_elf_req_addr;
logic [msrh_lsu_pkg::L2_CMD_TAG_W-1:0]    w_elf_req_tag;
logic [msrh_lsu_pkg::ICACHE_DATA_W-1:0]   w_elf_req_data;
logic [msrh_lsu_pkg::ICACHE_DATA_W/8-1:0] w_elf_req_byte_en;
logic                                     w_elf_req_ready;

/* L2 Interface */
logic                                     w_l2_req_valid;
msrh_lsu_pkg::mem_cmd_t                   w_l2_req_cmd;
logic [riscv_pkg::PADDR_W-1:0]            w_l2_req_addr;
logic [msrh_lsu_pkg::L2_CMD_TAG_W-1:0]    w_l2_req_tag;
logic [msrh_lsu_pkg::ICACHE_DATA_W-1:0]   w_l2_req_data;
logic [msrh_lsu_pkg::ICACHE_DATA_W/8-1:0] w_l2_req_byte_en;
logic                                     w_l2_req_ready;

logic                                     w_l2_resp_valid;
logic [msrh_lsu_pkg::L2_CMD_TAG_W-1:0]    w_l2_resp_tag;
logic [msrh_lsu_pkg::ICACHE_DATA_W-1:0]   w_l2_resp_data;
logic                                     w_l2_resp_ready;


/* L1D Interface */
logic                                     w_l1d_req_valid;
msrh_lsu_pkg::mem_cmd_t                   w_l1d_req_cmd;
logic [riscv_pkg::PADDR_W-1:0]            w_l1d_req_addr;
logic [msrh_lsu_pkg::L2_CMD_TAG_W-1:0]    w_l1d_req_tag;
logic [msrh_lsu_pkg::ICACHE_DATA_W-1:0]   w_l1d_req_data;
logic [msrh_lsu_pkg::ICACHE_DATA_W/8-1:0] w_l1d_req_byte_en;
logic                                     w_l1d_req_ready;

logic                                     w_l1d_resp_valid;
logic [msrh_lsu_pkg::L2_CMD_TAG_W-1:0]    w_l1d_resp_tag;
logic [msrh_lsu_pkg::ICACHE_DATA_W-1:0]   w_l1d_resp_data;
logic                                     w_l1d_resp_ready;

/* Connection */
assign w_l2_req_valid   = w_l1d_req_valid ? w_l1d_req_valid   : i_msrh_reset_n ? w_ic_req_valid   : w_elf_req_valid;
assign w_l2_req_cmd     = w_l1d_req_valid ? w_l1d_req_cmd     : i_msrh_reset_n ? w_ic_req_cmd     : w_elf_req_cmd;
assign w_l2_req_addr    = w_l1d_req_valid ? w_l1d_req_addr    : i_msrh_reset_n ? w_ic_req_addr    : w_elf_req_addr;
assign w_l2_req_tag     = w_l1d_req_valid ? w_l1d_req_tag     : i_msrh_reset_n ? w_ic_req_tag     : w_elf_req_tag;
assign w_l2_req_data    = w_l1d_req_valid ? w_l1d_req_data    : i_msrh_reset_n ? w_ic_req_data    : w_elf_req_data;
assign w_l2_req_byte_en = w_l1d_req_valid ? w_l1d_req_byte_en : i_msrh_reset_n ? w_ic_req_byte_en : w_elf_req_byte_en;

assign w_ic_req_ready  = w_l2_req_ready ;
assign w_elf_req_ready = w_l2_req_ready ;

assign w_ic_resp_valid = w_l2_resp_valid;
assign w_ic_resp_tag   = w_l2_resp_tag  ;
assign w_ic_resp_data  = w_l2_resp_data ;

assign w_l2_resp_ready = w_ic_resp_ready | w_l1d_resp_ready;

assign w_l1d_resp_valid = w_l2_resp_valid;
assign w_l1d_resp_tag   = w_l2_resp_tag  ;
assign w_l1d_resp_data  = w_l2_resp_data ;


msrh_tile_wrapper
  u_msrh_tile_wrapper
    (
    .i_clk     (i_clk        ),
    .i_reset_n (i_msrh_reset_n),

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
    .o_ic_resp_ready  (w_ic_resp_ready),

    // L2 request from L1D
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
    .o_l1d_resp_ready (w_l1d_resp_ready )
     );


tb_l2_behavior_ram
  #(
    .DATA_W    (msrh_lsu_pkg::ICACHE_DATA_W),
    .TAG_W     (msrh_lsu_pkg::L2_CMD_TAG_W),
    .ADDR_W    (riscv_pkg::PADDR_W),
    .BASE_ADDR ('h8000_0000),
    .SIZE      (4096),
    .RD_LAT    (10)
    )
u_tb_l2_behavior_ram
  (
   .i_clk     (i_clk        ),
   .i_reset_n (i_ram_reset_n),

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
   .i_resp_ready  (w_l2_resp_ready)
   );


tb_elf_loader
u_tb_elf_loader
  (
   .i_clk     (i_clk               ),
   .i_reset_n (i_elf_loader_reset_n),

   // L2 request from ELF Loader
   .o_req_valid   (w_elf_req_valid ),
   .o_req_cmd     (w_elf_req_cmd   ),
   .o_req_addr    (w_elf_req_addr  ),
   .o_req_tag     (w_elf_req_tag   ),
   .o_req_data    (w_elf_req_data  ),
   .o_req_byte_en (w_elf_req_byte_en),
   .i_req_ready   (w_elf_req_ready )
   );


msrh_pkg::rob_entry_t rob_entries[msrh_pkg::CMT_BLK_SIZE];
msrh_pkg::rob_entry_t committed_rob_entry;
generate for (genvar r_idx = 0; r_idx < msrh_pkg::CMT_BLK_SIZE; r_idx++) begin : rob_loop
  assign rob_entries[r_idx] = u_msrh_tile_wrapper.u_msrh_tile.u_rob.entry_loop[r_idx].u_entry.r_entry;
end
endgenerate

logic [msrh_pkg::CMT_BLK_SIZE-1: 0] w_commited_oh;
assign w_commited_oh = 'h1 << u_msrh_tile_wrapper.u_msrh_tile.u_rob.w_out_cmt_id;

bit_oh_or
  #(
    .WIDTH($size(msrh_pkg::rob_entry_t)),
    .WORDS(msrh_pkg::CMT_BLK_SIZE)
    )
commite_entry
  (
   .i_oh(w_commited_oh),
   .i_data(rob_entries),
   .o_selected(committed_rob_entry)
);


logic [riscv_pkg::XLEN_W-1: 0] w_physical_gpr_data [msrh_pkg::RNID_SIZE + 32];
generate for (genvar r_idx = 0; r_idx < msrh_pkg::RNID_SIZE + 32; r_idx++) begin: reg_loop
  assign w_physical_gpr_data[r_idx] = u_msrh_tile_wrapper.u_msrh_tile.u_int_phy_registers.r_phy_regs[r_idx];
end
endgenerate

always_ff @ (negedge i_clk, negedge i_msrh_reset_n) begin
  if (!i_msrh_reset_n) begin
  end else begin
    if (u_msrh_tile_wrapper.u_msrh_tile.u_rob.w_out_vld) begin
      for (int grp_idx = 0; grp_idx < msrh_pkg::DISP_SIZE; grp_idx++) begin
        if (committed_rob_entry.grp_id[grp_idx]) begin
          /* verilator lint_off WIDTH */
          step_spike ($time, longint'((committed_rob_entry.pc_addr << 1) + (4 * grp_idx)),
                      u_msrh_tile_wrapper.u_msrh_tile.u_rob.w_out_cmt_id,
                      1 << grp_idx,
                      committed_rob_entry.inst[grp_idx].inst,
                      committed_rob_entry.inst[grp_idx].rd_valid,
                      committed_rob_entry.inst[grp_idx].rd_regidx,
                      w_physical_gpr_data[committed_rob_entry.inst[grp_idx].rd_rnid]);
        end
      end // for (int grp_idx = 0; grp_idx < msrh_pkg::DISP_SIZE; grp_idx++)
    end // if (u_msrh_tile_wrapper.u_msrh_tile.u_rob.w_out_vld)
  end // else: !if(!i_msrh_reset_n)
end // always_ff @ (negedge i_clk, negedge i_msrh_reset_n)

`include "tb_json_dumper.sv"

endmodule // msrh_tb
