`ifndef DIRECT_LOAD_HEX
import "DPI-C" function load_binary
(
 input string path_exec,
 input string filename,
 input logic is_load_dump
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
logic                                w_ic_req_valid;
msrh_pkg::mem_cmd_t                   w_ic_req_cmd;
logic [riscv_pkg::PADDR_W-1:0]       w_ic_req_addr;
logic [msrh_pkg::L2_CMD_TAG_W-1:0]    w_ic_req_tag;
logic [msrh_pkg::ICACHE_DATA_W-1:0]   w_ic_req_data;
logic [msrh_pkg::ICACHE_DATA_W/8-1:0] w_ic_req_byte_en;
logic                                w_ic_req_ready;

logic                                w_ic_resp_valid;
logic [msrh_pkg::L2_CMD_TAG_W-1:0]    w_ic_resp_tag;
logic [msrh_pkg::ICACHE_DATA_W-1:0]   w_ic_resp_data;
logic                                w_ic_resp_ready  ;

/* from ELF Loader */
logic                                w_elf_req_valid;
msrh_pkg::mem_cmd_t                   w_elf_req_cmd;
logic [riscv_pkg::PADDR_W-1:0]       w_elf_req_addr;
logic [msrh_pkg::L2_CMD_TAG_W-1:0]    w_elf_req_tag;
logic [msrh_pkg::ICACHE_DATA_W-1:0]   w_elf_req_data;
logic [msrh_pkg::ICACHE_DATA_W/8-1:0] w_elf_req_byte_en;
logic                                w_elf_req_ready;

/* L2 Interface */
logic                                w_l2_req_valid;
msrh_pkg::mem_cmd_t                   w_l2_req_cmd;
logic [riscv_pkg::PADDR_W-1:0]       w_l2_req_addr;
logic [msrh_pkg::L2_CMD_TAG_W-1:0]    w_l2_req_tag;
logic [msrh_pkg::ICACHE_DATA_W-1:0]   w_l2_req_data;
logic [msrh_pkg::ICACHE_DATA_W/8-1:0] w_l2_req_byte_en;
logic                                w_l2_req_ready;

logic                                w_l2_resp_valid;
logic [msrh_pkg::L2_CMD_TAG_W-1:0]    w_l2_resp_tag;
logic [msrh_pkg::ICACHE_DATA_W-1:0]   w_l2_resp_data;
logic                                w_l2_resp_ready;

/* Connection */
assign w_l2_req_valid   = w_msrh_reset_n ? w_ic_req_valid   : w_elf_req_valid;
assign w_l2_req_cmd     = w_msrh_reset_n ? w_ic_req_cmd     : w_elf_req_cmd;
assign w_l2_req_addr    = w_msrh_reset_n ? w_ic_req_addr    : w_elf_req_addr;
assign w_l2_req_tag     = w_msrh_reset_n ? w_ic_req_tag     : w_elf_req_tag;
assign w_l2_req_data    = w_msrh_reset_n ? w_ic_req_data    : w_elf_req_data;
assign w_l2_req_byte_en = w_msrh_reset_n ? w_ic_req_byte_en : w_elf_req_byte_en;

assign w_ic_req_ready  = w_l2_req_ready ;
assign w_elf_req_ready = w_l2_req_ready ;

assign w_ic_resp_valid = w_l2_resp_valid;
assign w_ic_resp_tag   = w_l2_resp_tag  ;
assign w_ic_resp_data  = w_l2_resp_data ;
assign w_l2_resp_ready = w_ic_resp_ready;

msrh_tile_wrapper u_msrh_tile_wrapper
  (
    .i_clk     (w_clk),
    .i_reset_n (w_msrh_reset_n),

    // L2 request from ICache
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
    .o_ic_resp_ready (w_ic_resp_ready )
   );


tb_l2_behavior_ram
  #(
    .DATA_W    (msrh_pkg::ICACHE_DATA_W),
    .TAG_W     (msrh_pkg::L2_CMD_TAG_W),
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
   .i_resp_ready  (w_l2_resp_ready)
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

  load_binary("", filename, 1'b1);
`endif // DIRECT_LOAD_HEX

end


int log_fp;
initial begin
  log_fp = $fopen("simulate.log");
end


msrh_pkg::rob_entry_t rob_entries[msrh_pkg::CMT_BLK_SIZE];
msrh_pkg::rob_entry_t committed_rob_entry;
generate for (genvar r_idx = 0; r_idx < msrh_pkg::CMT_BLK_SIZE; r_idx++) begin : rob_loop
  assign rob_entries[r_idx] = u_msrh_tile_wrapper.u_msrh_tile.u_rob.entry_loop[r_idx].u_entry.r_entry;
end
endgenerate

bit_oh_or
  #(
    .WIDTH($size(msrh_pkg::rob_entry_t)),
    .WORDS(msrh_pkg::CMT_BLK_SIZE)
    )
commite_entry
  (
   .i_oh(u_msrh_tile_wrapper.u_msrh_tile.u_rob.w_entry_all_done),
   .i_data(rob_entries),
   .o_selected(committed_rob_entry)
);

logic [riscv_pkg::XLEN_W-1: 0] w_physical_gpr_data [msrh_pkg::RNID_SIZE];
generate for (genvar r_idx = 0; r_idx < msrh_pkg::RNID_SIZE; r_idx++) begin: reg_loop
  assign w_physical_gpr_data[r_idx] = u_msrh_tile_wrapper.u_msrh_tile.u_int_phy_registers.r_phy_regs[r_idx];
end
endgenerate


always_ff @ (negedge w_clk, negedge w_msrh_reset_n) begin
  if (!w_msrh_reset_n) begin
  end else begin
    for (int cmt_idx = 0; cmt_idx < msrh_pkg::CMT_BLK_SIZE; cmt_idx++) begin
      if (u_msrh_tile_wrapper.u_msrh_tile.u_rob.w_entry_all_done[cmt_idx]) begin
        for (int grp_idx = 0; grp_idx < msrh_pkg::DISP_SIZE; grp_idx++) begin
          if (rob_entries[cmt_idx].grp_id[grp_idx]) begin
            $fwrite (log_fp, "%t PC=%010x (%02d,%02d) %08x ", $time, (rob_entries[cmt_idx].pc_addr << 1) + (4 * grp_idx),
                     cmt_idx, 1 << grp_idx,
                     rob_entries[cmt_idx].inst[grp_idx].inst);
            if (rob_entries[cmt_idx].inst[grp_idx].rd_valid) begin
              $fwrite (log_fp, "GPR[%02d](%03d)=%016x : ",
                       rob_entries[cmt_idx].inst[grp_idx].rd_regidx,
                       rob_entries[cmt_idx].inst[grp_idx].rd_rnid,
                       w_physical_gpr_data[rob_entries[cmt_idx].inst[grp_idx].rd_rnid]);
            end else begin
              $fwrite (log_fp, " : ");
            end
            $fwrite(log_fp, "DASM(%08x)\n", rob_entries[cmt_idx].inst[grp_idx].inst);
          end // if (rob_entries[cmt_idx].grp_id[grp_idx])
        end // for (int grp_idx = 0; grp_idx < msrh_pkg::DISP_SIZE; grp_idx++)
      end // if (u_msrh_tile_wrapper.u_msrh_tile.u_rob.w_entry_all_done[cmt_idx])
    end // for (int cmt_idx = 0; cmt_idx < msrh_pkg::CMT_BLK_SIZE; cmt_idx++)
  end
end

final begin
  $fclose(log_fp);
end

endmodule // tb
