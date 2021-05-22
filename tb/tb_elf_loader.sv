import "DPI-C" function int debug_tick
(
 output bit debug_req_valid,
 input bit  debug_req_ready,
 output int debug_req_bits_addr,
 output int debug_req_bits_data
);

module tb_elf_loader
(
 input logic                               i_clk,
 input logic                               i_reset_n,

 output logic                                o_req_valid,
 output msrh_lsu_pkg::mem_cmd_t                   o_req_cmd,
 output logic [riscv_pkg::PADDR_W-1:0]       o_req_addr,
 output logic [msrh_lsu_pkg::L2_CMD_TAG_W-1:0]    o_req_tag,
 output logic [msrh_conf_pkg::ICACHE_DATA_W-1:0]   o_req_data,
 output logic [msrh_conf_pkg::ICACHE_DATA_W/8-1:0] o_req_byte_en,
 input logic                                 i_req_ready
);

logic                __debug_req_valid;
logic [riscv_pkg::PADDR_W-1: 0] __debug_req_bits_addr;
logic [31: 0]                   __debug_req_bits_data;

logic                req_valid_reg;
logic [riscv_pkg::PADDR_W-1:0] req_bits_addr_reg;
logic [31:0]                   req_bits_data_reg;

always_ff @(posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    req_valid_reg <= 1'b0;
  end else begin
    req_valid_reg     <= __debug_req_valid;
    req_bits_addr_reg <= __debug_req_bits_addr;
    req_bits_data_reg <= __debug_req_bits_data;
  end
end

assign o_req_valid = req_valid_reg;
assign o_req_cmd   = msrh_lsu_pkg::M_XWR;
assign o_req_addr  = req_bits_addr_reg;
assign o_req_tag   = 'h0;
generate for(genvar i = 0; i < msrh_conf_pkg::ICACHE_DATA_W / 32; i++) begin: data_loop
  assign o_req_data[i*32+:32] = req_bits_data_reg;
  assign o_req_byte_en[i*4+:4] = {4{(o_req_addr[$clog2(msrh_conf_pkg::ICACHE_DATA_W / 8)-1:2] == i)}};
end
endgenerate


int debug_tick_val;

always_ff @(negedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
  end else begin
    /* verilator lint_off WIDTH */
    debug_tick_val = debug_tick(
      __debug_req_valid,
      1'b1,
      __debug_req_bits_addr[31:0],
      __debug_req_bits_data
      );
  end
end

assign __debug_req_bits_addr[riscv_pkg::PADDR_W-1:32] = 'h0;

endmodule // tb_elf_loader
